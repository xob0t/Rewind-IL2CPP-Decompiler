// Modified by xob0t (2026): inlined constructor folding. See FORK.md.
using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Puts inlined constructors back.
///
/// "new T(args)" is compiled as "allocate; run T's constructor on it", and the C++ compiler often pastes the
/// constructor's statements in place of the call. What the machine code then shows is a raw allocation followed
/// by those statements - exact, but not how anyone would write it. Here the statements after an allocation are
/// compared with the bodies of T's constructors (recovered the same way from their own machine code); where
/// they are one constructor's statements with particular values in place of its parameters, they are replaced
/// by a call of that constructor with those values. Where nothing matches, the raw form stays: it does the same
/// thing either way.
/// </summary>
internal static partial class ConstructorFolding
{
    /// <param name="again">A second look, after other things were put back: only what is found now changes anything.</param>
    public static void Run(HMethod method, ProgramAnalysis program, MethodPipeline pipeline, bool again = false)
    {
        // Later allocations first, so that an object created inside another constructor's statements has
        // already taken its final form when the outer one is compared.
        // (Folding a constructor with branches takes blocks away: what is gone is passed over.)
        List<HBlock> blocks = [.. method.Blocks];
        for (int b = blocks.Count - 1; b >= 0; b--)
        {
            HBlock block = blocks[b];
            if (!method.Blocks.Contains(block)) continue;
            for (int i = block.Statements.Count - 1; i >= 0; i--)
            {
                if (i >= block.Statements.Count) continue;
                if (block.Statements[i] is not HAssign { Target: HLocal target, Value: HTypeExpr { Op: HTypeOp.Allocate } allocation }) continue;
                string problem = $"the constructor of {allocation.Target.ShortName} was inlined and could not be folded back";
                string note = $"the constructor of {allocation.Target.ShortName} was inlined here; the object is allocated raw and its statements follow";
                if (TryFold(block, i, target, allocation.Target, program, pipeline) || TryFoldChain(method, block, i, target, allocation.Target, program, pipeline) ||
                    TryFoldAround(block, i, target, allocation.Target, program, pipeline))
                {
                    if (again)
                    {
                        method.Problems.Remove(problem);
                        method.Notes.Remove(note);
                    }
                    continue;
                }
                if (again) continue;
                if (TryFoldAcrossJoin(method, block, i, program, pipeline)) continue;
                if (program.RawAllocator == null) method.Problems.Add(problem);
                else method.Notes.Add(note);
            }
        }
        // Inside a constructor: the base class's constructor, pasted in.
        FoldOwnChain(method, program, pipeline);
    }

    private static bool TryFold(HBlock block, int at, HLocal target, TypeSig type, ProgramAnalysis program, MethodPipeline pipeline)
    {
        TypeDef? definition = type.Definition;
        if (definition == null || definition.IsValueType) return false;
        TypeSig[] classArguments = type is GenericInstSig g ? g.Arguments : [];
        List<HStmt> site = block.Statements;
        HVar created = target.Variable;

        // The constructor's statements start at the first statement that touches the new object, or a little
        // before it (a value computed first and stored afterwards).
        int firstMention = at + 1;
        while (firstMention < site.Count && firstMention - at <= 8 && site[firstMention] is HAssign or HEval && !Mentions(site[firstMention], created))
            firstMention++;

        MethodDef? best = null;
        HExpr?[]? bestArguments = null;
        int bestStart = 0, bestLength = -1;
        foreach (MethodDef constructor in definition.Methods)
        {
            if (constructor.Name != ".ctor" || constructor.IsStatic) continue;
            HMethod? body = pipeline.ConstructorBody(constructor, classArguments);
            if (body == null) continue;
            foreach (List<HStmt> statements in Variants(body.Blocks[0].Statements))
            {
            int length = statements.Count - 1; // without the final return
            if (length < bestLength || (length == bestLength && best != null && best.Parameters.Length <= constructor.Parameters.Length)) continue;

            int lastStart = length == 0 ? at + 1 : Math.Min(firstMention, site.Count - length);
            for (int start = at + 1; start <= lastStart; start++)
            {
                var unifier = new Unifier(created, constructor.Parameters.Length) { Constructor = constructor, Quiet = c => QuietConstructor(c, pipeline) };
                bool matched = true;
                for (int k = 0; k < length && matched; k++)
                    matched = unifier.Statement(statements[k], site[start + k], k);
                if (!matched && Reordered(statements, length, site, start, created, constructor.Parameters.Length, pipeline) is { } other)
                {
                    unifier = other;
                    unifier.Quiet = c => QuietConstructor(c, pipeline);
                    matched = true;
                }
                if (!matched || !unifier.ArgumentsAreValid(site, start, length)) continue;
                best = constructor;
                bestArguments = unifier.Arguments;
                bestStart = start;
                bestLength = length;
                break;
            }
            }
        }
        if (best == null || bestArguments == null) return false;

        var arguments = new HExpr[best.Parameters.Length];
        for (int i = 0; i < arguments.Length; i++)
        {
            TypeSig parameter = best.Parameters[i].Type;
            if (classArguments.Length != 0) parameter = program.Model.Sigs.Substitute(parameter, classArguments, []);
            // A parameter the constructor never looks at: any value does.
            arguments[i] = bestArguments[i] ?? (parameter.IsValueType || parameter is GenericParamSig
                ? new HTypeExpr(HTypeOp.Default, parameter, null) { Type = parameter }
                : new HConst(null, parameter));
        }
        var creation = new HAssign(target, new HNewObject
        {
            Constructor = best,
            DeclaringType = type is GenericInstSig ? type : null,
            Arguments = arguments,
            Type = type,
        })
        { Address = block.Statements[at].Address };

        if (bestLength > 0) site.RemoveRange(bestStart, bestLength);
        site.Insert(bestStart, creation);
        site.RemoveAt(at);
        return true;
    }

    private static readonly bool NoMarkedRawConstructors = Environment.GetEnvironmentVariable("REWIND_NO_MARKED_RAW_CONSTRUCTORS") != null;

    /// <summary>
    /// In the finished method: an object allocated raw whose own constructor was not put back, but a base
    /// class's constructor was, as a call on the object. A constructor run on anything but "this" inside a
    /// constructor is no IL a verifier accepts. The code does what the original did, so it stays; the place is
    /// marked with a note (one that does not stop the code) and the method is reported incomplete.
    /// </summary>
    public static void MarkRawConstructors(HMethod method)
    {
        if (NoMarkedRawConstructors) return;
        foreach (HBlock block in method.Blocks)
            for (int i = block.Statements.Count - 1; i >= 0; i--)
            {
                if (block.Statements[i] is not HAssign { Target: HLocal { Variable: var created }, Value: HTypeExpr { Op: HTypeOp.Allocate } allocation } ||
                    !RunsConstructorOn(method, created))
                    continue;
                string invalid = $"the constructor of {allocation.Target.ShortName} was not put back: a constructor runs on the object allocated raw";
                if (method.Problems.Count < 64) method.Problems.Add(invalid);
                method.SiteProblems.Add(invalid);
                block.Statements.Insert(i, new HEval(new HOpaque("raw_constructor") { Problem = invalid, Remark = true }) { Address = block.Statements[i].Address });
            }
    }

    /// <summary>Whether a constructor is called on the object a variable holds (or a variable it is copied into).</summary>
    private static bool RunsConstructorOn(HMethod method, HVar created)
    {
        var holders = new HashSet<HVar> { created };
        for (bool more = true; more;)
        {
            more = false;
            foreach (HBlock b in method.Blocks)
                foreach (HStmt s in b.Statements)
                    if (s is HAssign { Target: HLocal { Variable: var copy }, Value: HLocal { Variable: var from } } && holders.Contains(from) && holders.Add(copy))
                        more = true;
        }
        bool found = false;
        foreach (HBlock b in method.Blocks)
            foreach (HStmt s in b.Statements)
                FinallyFolding.Visit(s, e => found |= e is HCall { Method.Name: ".ctor", This: HLocal { Variable: var v } } && holders.Contains(v));
        return found;
    }

    private static readonly bool NoPropagatedTemporaries = Environment.GetEnvironmentVariable("REWIND_NO_CONSTRUCTOR_TEMP_PROPAGATION") != null;

    /// <summary>
    /// The constructor's statements as they are, and - where it keeps a value computed from its parameters
    /// alone in a temporary ("double scaled = value / 255; this.scaled = scaled;") - with that value written
    /// where the temporary is read. The compiler does the same at a site where it knows the arguments: there the
    /// value is a constant stored straight into the field, and no temporary is left to match.
    /// </summary>
    private static IEnumerable<List<HStmt>> Variants(List<HStmt> statements)
    {
        yield return statements;
        if (NoPropagatedTemporaries) yield break;
        var sets = new Dictionary<HVar, int>();
        foreach (HStmt st in statements)
            if (st is HAssign { Target: HLocal { Variable: var v } }) sets[v] = sets.GetValueOrDefault(v) + 1;
        var known = new Dictionary<HVar, HExpr>();
        var propagated = new List<HStmt>(statements.Count);
        foreach (HStmt st in statements)
        {
            HStmt current = st;
            if (known.Count != 0 && st is not (HReturn or HJump or HBranch or HSwitch or HThrow))
            {
                if (HirCopy.Of(st, e => e is HLocal { Variable: var read } && known.TryGetValue(read, out HExpr? value) ? HirCopy.Of(value) : null) is not { } copy) yield break;
                current = copy;
            }
            if (current is HAssign { Target: HLocal { Variable: var temp }, Value: var computed } && sets[temp] == 1 && HirBuilder.IsPure(computed) && !Names(computed))
            {
                known[temp] = computed;
                continue;
            }
            propagated.Add(current);
        }
        if (known.Count != 0) yield return propagated;

        static bool Names(HExpr e)
        {
            bool named = false;
            FinallyFolding.Visit(e, x => named |= x is HLocal or HArg { Index: < 0 });
            return named;
        }
    }

    /// <summary>
    /// The constructor's statements, found at the site with its stores into the new object in another order.
    /// The compiler puts those in whatever order suits it: nothing can see the object yet, and what is stored
    /// only computes. So between two statements that do something else, each store of the constructor is
    /// looked for among the site's stores there, by the field it goes to. Null when that does not work out.
    /// </summary>
    private static Unifier? Reordered(List<HStmt> statements, int length, List<HStmt> site, int start, HVar created, int parameters, MethodPipeline pipeline)
    {
        if (length < 2 || start + length > site.Count) return null;
        // What is stored only computes: plain values, and a struct written out from plain values by a
        // constructor that does nothing but store them ("new Stats(4, 1, 2.5f)").
        bool Plain(HExpr value) => HirBuilder.IsPure(value) ||
            (!NoWrittenStructs && value is HNewObject { Type.IsValueType: true } made && made.Arguments.All(Plain) &&
             StructFolding.OnlyStores(made.Constructor, made.Type, pipeline));
        FieldDef? Filled(HStmt s, Func<HExpr, bool> isObject) =>
            s is HAssign { Target: HField { Object: { } o } target, Value: var value } && !target.Field.IsStatic && isObject(o) && Plain(value) ? target.Field : null;
        bool This(HExpr e) => e is HArg { Index: < 0 };
        bool Created(HExpr e) => e is HLocal l && ReferenceEquals(l.Variable, created);

        var unifier = new Unifier(created, parameters);
        for (int a = 0; a < length;)
        {
            if (Filled(statements[a], This) == null)
            {
                // Anything else stands where it stands.
                if (Filled(site[start + a], Created) != null || !unifier.Statement(statements[a], site[start + a], a)) return null;
                a++;
                continue;
            }
            // A run of stores: the same fields are filled at the site over the same stretch.
            int b = a;
            while (b < length && Filled(statements[b], This) != null) b++;
            var used = new bool[b - a];
            for (int j = a; j < b; j++)
                if (Filled(site[start + j], Created) == null)
                    return null;
            for (int k = a; k < b; k++)
            {
                FieldDef field = Filled(statements[k], This)!;
                int at = -1;
                for (int j = a; j < b && at < 0; j++)
                    if (!used[j - a] && ReferenceEquals(Filled(site[start + j], Created), field))
                        at = j;
                if (at < 0 || !unifier.Statement(statements[k], site[start + at], at)) return null;
                used[at - a] = true;
            }
            a = b;
        }
        return unifier;
    }

    private static readonly bool NoAround = Environment.GetEnvironmentVariable("REWIND_NO_CONSTRUCTOR_INTERLEAVING") != null;

    /// <summary>
    /// A constructor whose statements have the creating code's own stores in between: "new d__12(0) {
    /// &lt;&gt;4__this = this }" with the compiler storing &lt;&gt;4__this before the constructor's last store. Both go
    /// into an object nothing else can see yet, so the order is the compiler's choice. A store of the site is
    /// passed over when it comes after the base constructor has run, goes into a field the constructor's
    /// statements never name, and stores a constant, an argument or a plain local; it then follows "new".
    /// </summary>
    private static bool TryFoldAround(HBlock block, int at, HLocal target, TypeSig type, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (NoAround || type.Definition is not { IsValueType: false } definition) return false;
        TypeSig[] classArguments = type is GenericInstSig g ? g.Arguments : [];
        List<HStmt> site = block.Statements;
        HVar created = target.Variable;
        bool IsCreated(HExpr? e) => e is HLocal l && ReferenceEquals(l.Variable, created);
        foreach (MethodDef constructor in definition.Methods)
        {
            if (constructor.Name != ".ctor" || constructor.IsStatic) continue;
            if (pipeline.ConstructorBody(constructor, classArguments) is not { } body) continue;
            List<HStmt> statements = body.Blocks[0].Statements;
            int length = statements.Count - 1;
            if (length < 2) continue;
            // The fields the constructor's statements name, read or written.
            var named = new HashSet<FieldDef>();
            foreach (HStmt s in statements)
                FinallyFolding.Visit(s, e => { if (e is HField f) named.Add(f.Field); });
            int start = at + 1;
            if (start >= site.Count) continue;
            var picked = new List<int>();
            bool passedBase = false, skipped = false;
            for (int j = start; j < site.Count && picked.Count < length && j - start < length + 8; j++)
            {
                HStmt s = site[j];
                if (passedBase && picked.Count > 0 && s is HAssign { Target: HField { Object: var o } field, Value: HConst or HArg or HLocal } foreign &&
                    IsCreated(o) && !named.Contains(field.Field) && !field.Field.IsStatic &&
                    !(foreign.Value is HLocal { Variable: var v } && (v.AddressTaken || ReferenceEquals(v, created))))
                {
                    skipped = true;
                    continue;
                }
                if (s is not (HAssign or HEval)) break;
                picked.Add(j);
                if (s is HEval { Expression: HCall { Method.Name: ".ctor", This: var self } } && IsCreated(self)) passedBase = true;
            }
            if (!skipped || picked.Count != length) continue;
            var gathered = picked.Select(k => site[k]).ToList();
            // (A local stored by a passed-over store keeps its value: none of the constructor's statements give it one.)
            var moved = new HashSet<HVar>();
            for (int j = picked[0]; j < picked[^1]; j++)
                if (!picked.Contains(j) && site[j] is HAssign { Value: HLocal { Variable: var kept } }) moved.Add(kept);
            if (gathered.Any(s => s is HAssign { Target: HLocal { Variable: var given } } && moved.Contains(given))) continue;
            var unifier = new Unifier(created, constructor.Parameters.Length) { Constructor = constructor, Quiet = c => QuietConstructor(c, pipeline) };
            bool matched = true;
            for (int k = 0; k < length && matched; k++) matched = unifier.Statement(statements[k], gathered[k], k);
            if (!matched && Reordered(statements, length, gathered, 0, created, constructor.Parameters.Length, pipeline) is { } other)
            {
                unifier = other;
                unifier.Quiet = c => QuietConstructor(c, pipeline);
                matched = true;
            }
            if (!matched || !unifier.ArgumentsAreValid(gathered, 0, length)) continue;
            var arguments = new HExpr[constructor.Parameters.Length];
            for (int i = 0; i < arguments.Length; i++)
            {
                TypeSig parameter = constructor.Parameters[i].Type;
                if (classArguments.Length != 0) parameter = program.Model.Sigs.Substitute(parameter, classArguments, []);
                arguments[i] = unifier.Arguments[i] ?? (parameter.IsValueType || parameter is GenericParamSig
                    ? new HTypeExpr(HTypeOp.Default, parameter, null) { Type = parameter }
                    : new HConst(null, parameter));
            }
            var creation = new HAssign(target, new HNewObject
            {
                Constructor = constructor,
                DeclaringType = type is GenericInstSig ? type : null,
                Arguments = arguments,
                Type = type,
            })
            { Address = site[at].Address };
            int first = picked[0];
            for (int k = picked.Count - 1; k >= 0; k--) site.RemoveAt(picked[k]);
            site.Insert(first, creation);
            site.RemoveAt(at);
            return true;
        }
        return false;
    }

    private static readonly bool NoJoinTails = Environment.GetEnvironmentVariable("REWIND_NO_JOINED_CONSTRUCTORS") != null;
    private static readonly bool NoWrittenStructs = Environment.GetEnvironmentVariable("REWIND_NO_REORDERED_STRUCTS") != null;

    /// <summary>
    /// Constructors whose last statements the compiler wrote once for several branches.
    ///
    /// "if (big) return new Dragon(name); return new Goblin(name);" with both constructors pasted in: they end
    /// alike ("stats = new Stats(...)", with other numbers), and the compiler keeps one copy of that ending
    /// after the branches meet, with merged values standing for each branch's own. Each branch then holds a
    /// constructor without its end, and none of them folds. Copied back into every branch that leads there -
    /// with that branch's values in place of the merged ones - the endings complete the constructors again.
    /// Running the statements at the end of each branch is the same as running them once after the branches
    /// meet; it is done only when every branch's constructor then folds, all of the copied statements with it.
    /// </summary>
    private static bool TryFoldAcrossJoin(HMethod method, HBlock block, int at, ProgramAnalysis program, MethodPipeline pipeline)
    {
        if (NoJoinTails || block.Statements.Count == 0 || block.Statements[^1] is not HJump { Target: var join }) return false;
        if (ReferenceEquals(join, block) || join.Scope != block.Scope || join.Statements.Count < 2) return false;
        if (method.Blocks.Count == 0 || ReferenceEquals(method.Blocks[0], join)) return false;
        foreach (HTryRegion r in method.TryRegions.Values)
            if (ReferenceEquals(r.Entry, join) || ReferenceEquals(r.HandlerEntry, join))
                return false;
        // Every way into the meeting point is a plain jump at the end of a branch.
        var preds = new List<HBlock>();
        foreach (HBlock b in method.Blocks)
        {
            if (b.Statements.Count == 0) continue;
            switch (b.Statements[^1])
            {
                case HJump j when ReferenceEquals(j.Target, join):
                    if (ReferenceEquals(b, join) || b.Scope != join.Scope) return false;
                    preds.Add(b);
                    break;
                case HBranch br when ReferenceEquals(br.WhenTrue, join) || ReferenceEquals(br.WhenFalse, join):
                    return false;
                case HSwitch sw when ReferenceEquals(sw.Default, join) || sw.Targets.Any(t => ReferenceEquals(t, join)):
                    return false;
            }
        }
        if (preds.Count < 2) return false;

        int most = Math.Min(8, join.Statements.Count - 1);
        for (int n = 1; n <= most; n++)
        {
            // Only statements that do something to an object or call something: a merged value given to a
            // local is the ending of no constructor.
            if (join.Statements[n - 1] is not (HAssign { Target: not HLocal } or HEval)) break;
            var folded = new List<(HBlock Block, List<HStmt> Statements, HashSet<HVar> Moved)>();
            foreach (HBlock p in preds)
            {
                int allocation = ReferenceEquals(p, block) ? at : LastAllocation(p);
                if (allocation < 0 || FoldWithEnding(p, allocation, join, n, program, pipeline) is not { } result) break;
                folded.Add((p, result.Statements, result.Moved));
            }
            if (folded.Count != preds.Count) continue;
            var moved = new HashSet<HVar>();
            foreach ((_, _, HashSet<HVar> those) in folded) moved.UnionWith(those);
            // Inside a try region the copies run before the merged values are given: a handler that reads
            // one of those could tell the difference when a copy throws.
            if (join.Scope >= 0 && method.Blocks.Any(b => (b.Scope & 1) == 1 && b.Statements.Any(s => moved.Any(v => Reads(s, v))))) return false;
            foreach ((HBlock p, List<HStmt> statements, _) in folded)
            {
                p.Statements.Clear();
                p.Statements.AddRange(statements);
            }
            join.Statements.RemoveRange(0, n);
            // A merged value that only the moved statements read is given for nothing now.
            foreach (HVar v in moved)
            {
                if (method.Blocks.Any(b => b.Statements.Any(s => Reads(s, v)))) continue;
                foreach (HBlock b in method.Blocks)
                    b.Statements.RemoveAll(s => s is HAssign { Target: HLocal l, Value: HConst or HLocal } && ReferenceEquals(l.Variable, v));
            }
            return true;
        }
        return false;
    }

    private static int LastAllocation(HBlock block)
    {
        for (int i = block.Statements.Count - 1; i >= 0; i--)
            if (block.Statements[i] is HAssign { Target: HLocal, Value: HTypeExpr { Op: HTypeOp.Allocate } })
                return i;
        return -1;
    }

    /// <summary>
    /// The branch's statements with the first <paramref name="count"/> statements of the meeting point copied in
    /// (each merged value replaced by what the branch gives it) and the constructor folded; null unless the fold
    /// took every copied statement.
    /// </summary>
    private static (List<HStmt> Statements, HashSet<HVar> Moved)? FoldWithEnding(HBlock branch, int at, HBlock join, int count,
        ProgramAnalysis program, MethodPipeline pipeline)
    {
        List<HStmt> s = branch.Statements;
        int jump = s.Count - 1;
        // The values the branch gives the merged variables, last thing before it jumps.
        int moves = jump;
        while (moves > at + 1 && s[moves - 1] is HAssign { Target: HLocal, Value: HConst or HLocal }) moves--;
        var map = new Dictionary<HVar, HExpr>();
        for (int i = moves; i < jump; i++)
        {
            var move = (HAssign)s[i];
            HVar to = ((HLocal)move.Target).Variable;
            // (One move reading what another gives: the order would matter.)
            if (move.Value is HLocal from && map.ContainsKey(from.Variable)) return null;
            if (map.ContainsKey(to)) return null;
            map[to] = move.Value;
        }
        var copies = new List<HStmt>();
        var sources = new HashSet<HVar>(map.Values.OfType<HLocal>().Select(l => l.Variable));
        for (int k = 0; k < count; k++)
        {
            if (Copy(join.Statements[k], map) is not { } copy) return null;
            // (A copy that could change a local a move reads - through its address - must stay after it.)
            if (sources.Any(v => AddressTaken(copy, v))) return null;
            copies.Add(copy);
        }
        // The copies go before the moves: they read none of what the moves give (that is replaced), and the
        // moves read only locals and constants, which the copies do not change.
        var candidate = new List<HStmt>(s.Count + count);
        candidate.AddRange(s.Take(moves));
        candidate.AddRange(copies);
        candidate.AddRange(s.Skip(moves));
        var trial = new HBlock { Id = branch.Id, Scope = branch.Scope, Statements = candidate };
        if (candidate[at] is not HAssign { Target: HLocal target, Value: HTypeExpr { Op: HTypeOp.Allocate } allocation }) return null;
        if (!TryFold(trial, at, target, allocation.Target, program, pipeline)) return null;
        foreach (HStmt copy in copies)
            if (trial.Statements.Contains(copy))
                return null;
        return (trial.Statements, [.. map.Keys]);
    }

    /// <summary>A statement copied with some locals replaced by values; null for anything not copied.</summary>
    private static HStmt? Copy(HStmt statement, Dictionary<HVar, HExpr> map)
    {
        switch (statement)
        {
            case HAssign a when a.Target is not HLocal:
                return Copy(a.Target, map) is { } target && Copy(a.Value, map) is { } value ? new HAssign(target, value) { Address = a.Address } : null;
            case HEval e:
                return Copy(e.Expression, map) is { } expression ? new HEval(expression) { Address = e.Address } : null;
            default:
                return null;
        }
    }

    private static HExpr? Copy(HExpr? e, Dictionary<HVar, HExpr> map)
    {
        HExpr[]? All(HExpr[] items)
        {
            var copies = new HExpr[items.Length];
            for (int i = 0; i < items.Length; i++)
                if ((copies[i] = Copy(items[i], map)!) == null)
                    return null;
            return copies;
        }
        switch (e)
        {
            case null:
                return null;
            case HLocal l when map.TryGetValue(l.Variable, out HExpr? value):
                return Copy(value, []);
            case HLocal l:
                return new HLocal(l.Variable) { Type = l.Type };
            case HConst c:
                return new HConst(c.Value, c.Type);
            case HArg a:
                return new HArg(a.Index) { Type = a.Type };
            case HField f:
            {
                HExpr? owner = null;
                if (f.Object != null && (owner = Copy(f.Object, map)) == null) return null;
                return new HField { Object = owner, Field = f.Field, DeclaringType = f.DeclaringType, Type = f.Type };
            }
            case HElement el:
                return Copy(el.Array, map) is { } array && Copy(el.Index, map) is { } index ? new HElement { Array = array, Index = index, Type = el.Type } : null;
            case HArrayLength len:
                return Copy(len.Array, map) is { } of ? new HArrayLength(of) { Type = len.Type } : null;
            case HAddressOf addr:
                return Copy(addr.Target, map) is { } place ? new HAddressOf(place) { Type = addr.Type } : null;
            case HDeref d:
                return Copy(d.Pointer, map) is { } pointer ? new HDeref(pointer) { Type = d.Type } : null;
            case HUnary u:
                return Copy(u.Operand, map) is { } operand ? new HUnary(u.Op, operand) { Type = u.Type } : null;
            case HBinary b:
                return Copy(b.Left, map) is { } left && Copy(b.Right, map) is { } right ? Folded(new HBinary(b.Op, left, right) { Type = b.Type }) : null;
            case HCompare c:
                return Copy(c.Left, map) is { } cl && Copy(c.Right, map) is { } cr ? new HCompare(c.Op, cl, cr) { Type = c.Type } : null;
            case HConv c:
                return Copy(c.Operand, map) is { } converted ? Folded(new HConv(c.Kind, converted) { Type = c.Type }) : null;
            case HSelect s:
                return Copy(s.Condition, map) is { } condition && Copy(s.WhenTrue, map) is { } yes && Copy(s.WhenFalse, map) is { } no
                    ? new HSelect(condition, yes, no) { Type = s.Type } : null;
            case HCall call:
            {
                HExpr? self = null;
                if (call.This != null && (self = Copy(call.This, map)) == null) return null;
                if (All(call.Arguments) is not { } arguments) return null;
                var copy = new HCall
                {
                    Method = call.Method, DeclaringType = call.DeclaringType, MethodArguments = call.MethodArguments, This = self,
                    Arguments = arguments, Virtual = call.Virtual, Constrained = call.Constrained, Type = call.Type,
                };
                copy.Alternatives.AddRange(call.Alternatives);
                return copy;
            }
            case HNewObject n:
                return All(n.Arguments) is { } given
                    ? new HNewObject { Constructor = n.Constructor, DeclaringType = n.DeclaringType, Arguments = given, Type = n.Type } : null;
            case HNewArray na:
                return Copy(na.Length, map) is { } length ? new HNewArray(na.ElementType, length) { Type = na.Type } : null;
            case HTypeExpr t:
            {
                HExpr? inner = null;
                if (t.Operand != null && (inner = Copy(t.Operand, map)) == null) return null;
                return new HTypeExpr(t.Op, t.Target, inner) { Type = t.Type };
            }
            case HMethodPointer p:
                return new HMethodPointer { Method = p.Method, DeclaringType = p.DeclaringType, MethodArguments = p.MethodArguments, VirtualOn = p.VirtualOn, Type = p.Type };
            case HMemberToken m:
                return new HMemberToken { Method = m.Method, Field = m.Field, DeclaringType = m.DeclaringType, MethodArguments = m.MethodArguments, Type = m.Type };
            default:
                // (A cached delegate, an opaque operation: left where it is.)
                return null;
        }
    }

    /// <summary>Arithmetic on numbers written out, done (a merged value replaced by a branch's constant).</summary>
    private static HExpr Folded(HExpr e)
    {
        static long? Whole(object? v) => v switch { int i => i, long l => l, _ => null };
        switch (e)
        {
            case HConv { Operand: HConst { Value: var value } } c when Whole(value) is { } n:
                return c.Kind switch
                {
                    HConvKind.I4 or HConvKind.U4 => new HConst(unchecked((int)n), c.Type),
                    HConvKind.I8 => new HConst(n, c.Type),
                    HConvKind.U8 => new HConst(value is int i ? (long)unchecked((uint)i) : n, c.Type),
                    _ => e,
                };
            case HBinary { Left: HConst { Value: long a }, Right: HConst { Value: var right } } b when Whole(right) is { } r:
                return b.Op switch
                {
                    HBinaryOp.ShrUn => new HConst((long)((ulong)a >> (int)(r & 63)), b.Type),
                    HBinaryOp.Shr => new HConst(a >> (int)(r & 63), b.Type),
                    HBinaryOp.Shl => new HConst(a << (int)(r & 63), b.Type),
                    HBinaryOp.And => new HConst(a & r, b.Type),
                    HBinaryOp.Or => new HConst(a | r, b.Type),
                    _ => e,
                };
            case HBinary { Left: HConst { Value: int a }, Right: HConst { Value: int r } } b:
                return b.Op switch
                {
                    HBinaryOp.ShrUn => new HConst((int)((uint)a >> (r & 31)), b.Type),
                    HBinaryOp.Shr => new HConst(a >> (r & 31), b.Type),
                    HBinaryOp.Shl => new HConst(a << (r & 31), b.Type),
                    HBinaryOp.And => new HConst(a & r, b.Type),
                    HBinaryOp.Or => new HConst(a | r, b.Type),
                    _ => e,
                };
            default:
                return e;
        }
    }

    /// <summary>Whether the address of a variable (or of a part of it) is taken anywhere in a statement.</summary>
    private static bool AddressTaken(HStmt statement, HVar variable)
    {
        bool found = false;
        void Walk(HExpr? e)
        {
            if (found || e == null) return;
            switch (e)
            {
                case HAddressOf a:
                    HExpr root = a.Target;
                    while (root is HField { Object: { } owner }) root = owner;
                    if (root is HLocal l && ReferenceEquals(l.Variable, variable)) found = true;
                    else Walk(a.Target);
                    break;
                case HField f: Walk(f.Object); break;
                case HElement el: Walk(el.Array); Walk(el.Index); break;
                case HArrayLength len: Walk(len.Array); break;
                case HDeref d: Walk(d.Pointer); break;
                case HUnary u: Walk(u.Operand); break;
                case HBinary b: Walk(b.Left); Walk(b.Right); break;
                case HCompare c: Walk(c.Left); Walk(c.Right); break;
                case HConv c: Walk(c.Operand); break;
                case HSelect s: Walk(s.Condition); Walk(s.WhenTrue); Walk(s.WhenFalse); break;
                case HCall call: Walk(call.This); foreach (HExpr x in call.Arguments) Walk(x); break;
                case HNewObject n: foreach (HExpr x in n.Arguments) Walk(x); break;
                case HNewArray na: Walk(na.Length); break;
                case HTypeExpr t: Walk(t.Operand); break;
                case HCachedDelegate cd: Walk(cd.Creation); break;
                case HOpaque o: foreach (HExpr x in o.Operands) Walk(x); break;
            }
        }
        switch (statement)
        {
            case HAssign a: Walk(a.Target); Walk(a.Value); break;
            case HEval e: Walk(e.Expression); break;
        }
        return found;
    }

    /// <summary>Whether a statement reads a variable (giving it a value as a whole is no read).</summary>
    private static bool Reads(HStmt statement, HVar variable) => statement switch
    {
        HAssign { Target: HLocal } a => Mentions(a.Value, variable),
        _ => Mentions(statement, variable),
    };

    internal static bool Mentions(HStmt statement, HVar variable) => statement switch
    {
        HAssign a => Mentions(a.Target, variable) || Mentions(a.Value, variable),
        HEval e => Mentions(e.Expression, variable),
        HReturn r => r.Value != null && Mentions(r.Value, variable),
        HThrow t => t.Exception != null && Mentions(t.Exception, variable),
        HBranch b => Mentions(b.Condition, variable),
        HSwitch s => Mentions(s.Value, variable),
        _ => false,
    };

    internal static bool Mentions(HExpr? e, HVar variable) => e switch
    {
        null => false,
        HLocal l => ReferenceEquals(l.Variable, variable),
        HField f => Mentions(f.Object, variable),
        HElement el => Mentions(el.Array, variable) || Mentions(el.Index, variable),
        HArrayLength len => Mentions(len.Array, variable),
        HAddressOf a => Mentions(a.Target, variable),
        HDeref d => Mentions(d.Pointer, variable),
        HUnary u => Mentions(u.Operand, variable),
        HBinary b => Mentions(b.Left, variable) || Mentions(b.Right, variable),
        HCompare c => Mentions(c.Left, variable) || Mentions(c.Right, variable),
        HConv c => Mentions(c.Operand, variable),
        HCall call => Mentions(call.This, variable) || call.Arguments.Any(a => Mentions(a, variable)),
        HNewObject n => n.Arguments.Any(a => Mentions(a, variable)),
        HNewArray na => Mentions(na.Length, variable),
        HTypeExpr t => Mentions(t.Operand, variable),
        HSelect s => Mentions(s.Condition, variable) || Mentions(s.WhenTrue, variable) || Mentions(s.WhenFalse, variable),
        HOpaque o => o.Operands.Any(a => Mentions(a, variable)),
        HCachedDelegate cd => Mentions(cd.Creation, variable),
        _ => false,
    };

    private static bool ReadsMemory(HExpr? e) => e switch
    {
        null => false,
        HField or HElement or HDeref or HArrayLength => true,
        HAddressOf a => a.Target is HField { Object: { } o } ? ReadsMemory(o) : a.Target is HElement,
        HUnary u => ReadsMemory(u.Operand),
        HBinary b => ReadsMemory(b.Left) || ReadsMemory(b.Right),
        HCompare c => ReadsMemory(c.Left) || ReadsMemory(c.Right),
        HConv c => ReadsMemory(c.Operand),
        HTypeExpr t => ReadsMemory(t.Operand),
        HSelect s => ReadsMemory(s.Condition) || ReadsMemory(s.WhenTrue) || ReadsMemory(s.WhenFalse),
        _ => false,
    };

    /// <summary>Matches a constructor's statements against the statements at a creation site.</summary>
    private sealed class Unifier(HVar? created, int parameters)
    {
        /// <summary>The object the constructor runs on at the site: the new object's variable - or, where created is null, "this".</summary>
        public bool IsCreated(HExpr e) => created == null ? e is HArg { Index: < 0 } : e is HLocal l && ReferenceEquals(l.Variable, created);

        private bool MentionsCreated(HExpr e) => created == null ? MentionsThis(e) : Mentions(e, created);

        /// <summary>The site's local variables that stand for temporaries of the constructor.</summary>
        public IReadOnlyCollection<HVar> SiteLocals => _siteLocals;

        /// <summary>A constructor call that does nothing but fill the object it runs on (see QuietConstructor).</summary>
        public Func<HCall, bool>? Quiet;

        /// <summary>What a test of the constructor comes to with the values found for its parameters; null when that is not certain.</summary>
        public bool? Decides(HExpr condition) => Worth(condition, -1, 0) is long v ? v != 0 : null;

        /// <summary>Whether a statement found does nothing but fill the new object (nothing else can see it yet).</summary>
        public bool Inert(HStmt s) => s switch
        {
            HAssign { Target: HField { Object: { } o }, Value: var value } => IsCreated(o) && HirBuilder.IsPure(value),
            HEval { Expression: HCall { Method: { Name: ".ctor" } m, This: { } o } call } =>
                IsCreated(o) && ((m.Parameters.Length == 0 && m.DeclaringType.BaseType == null) || Quiet?.Invoke(call) == true),
            _ => false,
        };

        /// <summary>What the site has where the constructor has each parameter.</summary>
        public readonly HExpr?[] Arguments = new HExpr?[parameters];
        private readonly int[] _boundAt = new int[parameters];
        private readonly Dictionary<HVar, HVar> _locals = [];
        private readonly HashSet<HVar> _siteLocals = [];
        private int _statement;
        /// <summary>The constructor compared (for the types of its parameters); null where only their number is known.</summary>
        public MethodDef? Constructor;

        private static readonly bool NoSolving = Environment.GetEnvironmentVariable("REWIND_NO_SOLVED_ARGUMENTS") != null;

        /// <summary>The whole numbers tried for an argument: the small ones, and the round ones beyond.</summary>
        private static readonly long[] Tried = MakeTried();

        private static long[] MakeTried()
        {
            var tried = new List<long>();
            for (long n = -64; n <= 4096; n++) tried.Add(n);
            for (int k = 13; k <= 30; k++)
            {
                tried.Add((1L << k) - 1);
                tried.Add(1L << k);
            }
            for (long n = 5000; n <= 1_000_000_000; n *= 10)
            {
                tried.Add(n);
                tried.Add(n * 2);
            }
            tried.Add(int.MaxValue);
            tried.Add(int.MinValue);
            return [.. tried.Distinct()];
        }

        /// <summary>
        /// Finds the constant a parameter was handed that makes what the constructor computes with it come out
        /// as the constant the place has ("1f / (float)targetFPS" stands there as 0.033333335f: targetFPS was
        /// 30) - the compiler does that arithmetic itself where it knows the argument. Only for a whole number
        /// or a yes/no, and only when exactly one of the values tried gives that constant.
        /// </summary>
        private bool Solved(HExpr computed, object worked)
        {
            if (NoSolving || Constructor == null) return false;
            int parameter = -1;
            bool fine = true;
            void Look(HExpr? e)
            {
                switch (e)
                {
                    case HConst { Value: not null }:
                        break;
                    case HArg { Index: >= 0 } a when a.Index < Arguments.Length:
                        if (Arguments[a.Index] is { } bound) fine &= bound is HConst { Value: not null };
                        else if (parameter < 0 || parameter == a.Index) parameter = a.Index;
                        else fine = false;
                        break;
                    case HBinary b: Look(b.Left); Look(b.Right); break;
                    case HCompare c: Look(c.Left); Look(c.Right); break;
                    case HSelect s: Look(s.Condition); Look(s.WhenTrue); Look(s.WhenFalse); break;
                    case HConv c: Look(c.Operand); break;
                    case HUnary u: Look(u.Operand); break;
                    default: fine = false; break;
                }
            }
            Look(computed);
            if (!fine || Plain(worked) is not { } wanted) return false;
            if (parameter < 0) return Equal(Worth(computed, -1, 0), wanted);

            TypeSig type = Constructor.Parameters[parameter].Type;
            bool flag = type is PrimitiveSig { Element: Il2CppTypeEnum.Boolean };
            if (!flag && type is not PrimitiveSig { Element: Il2CppTypeEnum.I4 }) return false;
            long found = 0;
            int fits = 0;
            foreach (long candidate in flag ? [0L, 1L] : Tried)
            {
                if (!Equal(Worth(computed, parameter, candidate), wanted)) continue;
                found = candidate;
                if (++fits > 1) return false;
            }
            if (fits != 1) return false;
            Arguments[parameter] = flag ? new HConst(found != 0, type) : new HConst((int)found, type);
            _boundAt[parameter] = _statement;
            return true;
        }

        /// <summary>A constant as the arithmetic here has it: a whole number (yes/no as 1/0), a float or a double.</summary>
        private static object? Plain(object? value) => value switch
        {
            bool b => b ? 1L : 0L,
            int n => (long)n,
            long n => n,
            float f => f,
            double d => d,
            _ => null,
        };

        private static bool Equal(object? a, object b) => (a, b) switch
        {
            (long x, long y) => x == y,
            (float x, float y) => BitConverter.SingleToInt32Bits(x) == BitConverter.SingleToInt32Bits(y),
            (double x, double y) => BitConverter.DoubleToInt64Bits(x) == BitConverter.DoubleToInt64Bits(y),
            _ => false,
        };

        /// <summary>
        /// What an expression is worth with a parameter standing for a number; null where that is not certain
        /// (anything but plain arithmetic on 32-bit whole numbers, floats and doubles, each kept to its kind).
        /// </summary>
        private object? Worth(HExpr e, int parameter, long handed)
        {
            static object? Whole(long n) => n is >= int.MinValue and <= int.MaxValue ? n : null;
            switch (e)
            {
                case HConst c:
                    return Plain(c.Value) is long number ? Whole(number) : Plain(c.Value);
                case HArg a:
                    if (a.Index == parameter) return handed;
                    return a.Index >= 0 && a.Index < Arguments.Length && Arguments[a.Index] is HConst known && Plain(known.Value) is { } had ? (had is long w ? Whole(w) : had) : null;
                case HUnary { Op: HUnaryOp.Neg } u:
                    return Worth(u.Operand, parameter, handed) switch
                    {
                        long n => Whole(-n),
                        float f => -f,
                        double d => -d,
                        _ => null,
                    };
                case HUnary { Op: HUnaryOp.LogicalNot } u:
                    return Worth(u.Operand, parameter, handed) is long truth ? (truth == 0 ? 1L : 0L) : null;
                case HConv { Kind: HConvKind.R4 } c:
                    return Worth(c.Operand, parameter, handed) switch
                    {
                        long n => (float)(int)n,
                        float f => f,
                        double d => (float)d,
                        _ => null,
                    };
                case HConv { Kind: HConvKind.R8 } c:
                    return Worth(c.Operand, parameter, handed) switch
                    {
                        long n => (double)(int)n,
                        float f => (double)f,
                        double d => d,
                        _ => null,
                    };
                case HConv { Kind: HConvKind.I4 } c:
                    return Worth(c.Operand, parameter, handed) switch
                    {
                        long n => n,
                        float f when f > -2.0e9f && f < 2.0e9f => (long)(int)f,
                        double d when d > -2.0e9 && d < 2.0e9 => (long)(int)d,
                        _ => null,
                    };
                case HSelect s:
                    return Worth(s.Condition, parameter, handed) is long which ? Worth(which != 0 ? s.WhenTrue : s.WhenFalse, parameter, handed) : null;
                case HCompare c:
                {
                    int? order = (Worth(c.Left, parameter, handed), Worth(c.Right, parameter, handed)) switch
                    {
                        (long x, long y) => x.CompareTo(y),
                        // (A float that is no number is neither less nor more nor equal: left alone.)
                        (float x, float y) when !float.IsNaN(x) && !float.IsNaN(y) => x.CompareTo(y),
                        (double x, double y) when !double.IsNaN(x) && !double.IsNaN(y) => x.CompareTo(y),
                        _ => null,
                    };
                    if (order is not { } o) return null;
                    return c.Op switch
                    {
                        HCompareOp.Eq => o == 0 ? 1L : 0L,
                        HCompareOp.Ne => o != 0 ? 1L : 0L,
                        HCompareOp.Lt => o < 0 ? 1L : 0L,
                        HCompareOp.Le => o <= 0 ? 1L : 0L,
                        HCompareOp.Gt => o > 0 ? 1L : 0L,
                        HCompareOp.Ge => o >= 0 ? 1L : 0L,
                        _ => null,
                    };
                }
                case HBinary b:
                    return (b.Op, Worth(b.Left, parameter, handed), Worth(b.Right, parameter, handed)) switch
                    {
                        (HBinaryOp.Add, long x, long y) => Whole(x + y),
                        (HBinaryOp.Sub, long x, long y) => Whole(x - y),
                        (HBinaryOp.Mul, long x, long y) => Whole(x * y),
                        (HBinaryOp.Div, long x, long y) when y != 0 => Whole(x / y),
                        (HBinaryOp.Add, float x, float y) => x + y,
                        (HBinaryOp.Sub, float x, float y) => x - y,
                        (HBinaryOp.Mul, float x, float y) => x * y,
                        (HBinaryOp.Div, float x, float y) => x / y,
                        (HBinaryOp.Add, double x, double y) => x + y,
                        (HBinaryOp.Sub, double x, double y) => x - y,
                        (HBinaryOp.Mul, double x, double y) => x * y,
                        (HBinaryOp.Div, double x, double y) => x / y,
                        _ => null,
                    };
                default:
                    return null;
            }
        }

        /// <summary>Whether an expression of the constructor (a test it makes) is the same as one at the site.</summary>
        public bool Same(HExpr constructor, HExpr site, int index)
        {
            _statement = index;
            return Expression(constructor, site);
        }

        /// <summary>
        /// For a constructor compared along its branches: the values found for its parameters can be computed
        /// before it runs - they use no temporary of its, nothing it assigns, and what they read from memory was
        /// found before the first statement that could change memory.
        /// </summary>
        public bool ArgumentsHoldBefore(int firstEffect, IReadOnlyCollection<HVar> assigned)
        {
            for (int i = 0; i < Arguments.Length; i++)
            {
                if (Arguments[i] is not { } value) continue;
                foreach (HVar inner in _siteLocals)
                    if (Mentions(value, inner))
                        return false;
                foreach (HVar changed in assigned)
                    if (Mentions(value, changed))
                        return false;
                if (ReadsMemory(value) && _boundAt[i] > firstEffect) return false;
            }
            return true;
        }

        public bool Statement(HStmt constructor, HStmt site, int index)
        {
            _statement = index;
            switch (constructor, site)
            {
                case (HAssign c, HAssign s):
                    if (c.Target is HLocal cl)
                    {
                        // A temporary of the constructor: the site has one of its own in the same role.
                        if (s.Target is not HLocal sl || (created != null && ReferenceEquals(sl.Variable, created))) return false;
                        if (_locals.TryGetValue(cl.Variable, out HVar? known)) { if (!ReferenceEquals(known, sl.Variable)) return false; }
                        else if (!_siteLocals.Add(sl.Variable)) return false;
                        else _locals[cl.Variable] = sl.Variable;
                    }
                    else if (!Expression(c.Target, s.Target)) return false;
                    return Expression(c.Value, s.Value);
                case (HEval c, HEval s):
                    return Expression(c.Expression, s.Expression);
                default:
                    return false;
            }
        }

        private bool All(HExpr[] constructor, HExpr[] site)
        {
            if (constructor.Length != site.Length) return false;
            for (int i = 0; i < constructor.Length; i++)
                if (!Expression(constructor[i], site[i]))
                    return false;
            return true;
        }

        private static bool SameTypes(TypeSig[] a, TypeSig[] b)
        {
            if (a.Length != b.Length) return false;
            for (int i = 0; i < a.Length; i++)
                if (!ReferenceEquals(a[i], b[i]))
                    return false;
            return true;
        }

        private bool Expression(HExpr? constructor, HExpr? site)
        {
            if (constructor == null || site == null) return constructor == null && site == null;
            // A constant where the constructor computes: worked out by the compiler from a constant handed over.
            if (site is HConst { Value: { } worked } && constructor is HBinary or HSelect or HConv or HUnary && Solved(constructor, worked)) return true;
            switch (constructor)
            {
                case HArg { Index: < 0 }:
                    return IsCreated(site);
                case HArg a:
                    if (a.Index >= Arguments.Length) return false;
                    if (Arguments[a.Index] is { } bound) return HirCleanup.Same(bound, site);
                    if (!HirBuilder.IsPure(site) || MentionsCreated(site)) return false;
                    Arguments[a.Index] = site;
                    _boundAt[a.Index] = _statement;
                    return true;
                case HLocal l:
                    return site is HLocal sl && _locals.TryGetValue(l.Variable, out HVar? mapped) && ReferenceEquals(mapped, sl.Variable);
                case HConst c:
                    return site is HConst sc && Equals(c.Value, sc.Value);
                case HField f:
                    return site is HField sf && ReferenceEquals(f.Field, sf.Field) && Expression(f.Object, sf.Object);
                case HElement el:
                    return site is HElement se && Expression(el.Array, se.Array) && Expression(el.Index, se.Index);
                case HArrayLength len:
                    return site is HArrayLength sl2 && Expression(len.Array, sl2.Array);
                case HAddressOf addr:
                    return site is HAddressOf sa && Expression(addr.Target, sa.Target);
                case HDeref d:
                    return site is HDeref sd && Expression(d.Pointer, sd.Pointer);
                case HUnary u:
                    return site is HUnary su && u.Op == su.Op && Expression(u.Operand, su.Operand);
                case HBinary b:
                    return site is HBinary sb && b.Op == sb.Op && Expression(b.Left, sb.Left) && Expression(b.Right, sb.Right);
                case HCompare c:
                    return site is HCompare sc2 && c.Op == sc2.Op && Expression(c.Left, sc2.Left) && Expression(c.Right, sc2.Right);
                case HConv c:
                    return site is HConv sc3 && c.Kind == sc3.Kind && Expression(c.Operand, sc3.Operand);
                case HSelect s:
                    return site is HSelect ss && Expression(s.Condition, ss.Condition) && Expression(s.WhenTrue, ss.WhenTrue) && Expression(s.WhenFalse, ss.WhenFalse);
                case HTypeExpr t:
                    return site is HTypeExpr st && t.Op == st.Op && t.Op != HTypeOp.Allocate && ReferenceEquals(t.Target, st.Target) && Expression(t.Operand, st.Operand);
                case HCall call:
                    // Methods that share their machine code are told apart by guessing; the guess made in the
                    // constructor and the one made at the site can differ for what is the same call.
                    return site is HCall sc4 &&
                           (ReferenceEquals(call.Method, sc4.Method) ||
                            (call.Method.Parameters.Length == sc4.Method.Parameters.Length && call.Method.IsStatic == sc4.Method.IsStatic &&
                             (call.Alternatives.Contains(sc4.Method) || sc4.Alternatives.Contains(call.Method)))) &&
                           call.Virtual == sc4.Virtual &&
                           SameTypes(call.MethodArguments, sc4.MethodArguments) && Expression(call.This, sc4.This) && All(call.Arguments, sc4.Arguments);
                case HNewObject n:
                    return site is HNewObject sn && ReferenceEquals(n.Constructor, sn.Constructor) && All(n.Arguments, sn.Arguments);
                case HNewArray na:
                    return site is HNewArray sna && ReferenceEquals(na.ElementType, sna.ElementType) && Expression(na.Length, sna.Length);
                case HMethodPointer p:
                    return site is HMethodPointer sp && ReferenceEquals(p.Method, sp.Method) && SameTypes(p.MethodArguments, sp.MethodArguments) &&
                           p.VirtualOn?.Index == sp.VirtualOn?.Index;
                case HMemberToken m:
                    return site is HMemberToken sm && ReferenceEquals(m.Method, sm.Method) && ReferenceEquals(m.Field, sm.Field);
                case HCachedDelegate cached:
                    return site is HCachedDelegate kept && ReferenceEquals(cached.Cache.Field, kept.Cache.Field) && Expression(cached.Creation, kept.Creation);
                default:
                    return false;
            }
        }

        /// <summary>
        /// The values found for the parameters are computed once, before the constructor runs. That is the same
        /// as where they were found only if nothing the constructor did earlier could have changed them.
        /// </summary>
        public bool ArgumentsAreValid(List<HStmt> site, int start, int length)
        {
            // Statements that only fill the new object (which nothing else can see yet) change nothing an
            // argument could depend on.
            int firstEffect = length;
            for (int k = 0; k < length; k++)
            {
                if (!Inert(site[start + k]))
                {
                    firstEffect = k;
                    break;
                }
            }
            for (int i = 0; i < Arguments.Length; i++)
            {
                if (Arguments[i] is not { } value) continue;
                foreach (HVar inner in _siteLocals)
                    if (Mentions(value, inner))
                        return false;
                if (ReadsMemory(value) && _boundAt[i] > firstEffect) return false;
            }
            return true;
        }
    }
}
