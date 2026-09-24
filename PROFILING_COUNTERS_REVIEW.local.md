# Review: PROFILING_COUNTERS_PROPOSAL.local.md

Status: review notes, uncommitted. Written 2026-09-24 against the same
checkout as the proposal (branch `dead-code-2.8.0`).

Verdict: **the diagnosis is sound and the motivating case is convincing.**
One item in the implementation sketch would not survive contact with the
existing code, and the ordering understates the cheapest item. Details below.

---

## 0. What checks out

Every code reference in the proposal is exact against this checkout:

| claim | verified |
|---|---|
| `Reduce.hs:653` `unfoldDefinitionStep` | yes, exact |
| `Reduce.hs:906` `appDefE'` | yes, exact |
| `Reduce.hs:764` `reduceDefCopyTCM` | yes, exact |
| `ProfileOption` constructors | yes, `Utils/ProfileOptions.hs:33` |
| `tick`/`tickN`/`tickMax` in `Monad/Statistics.hs` | yes |
| `Conversion.hs:170` aggregate ticks | yes |
| `isDefAccount`, `Definition QName` account | yes, `Benchmarking.hs:115,133` |

So §3's table is a fair account of what exists, and the gap it describes --
*time spent elaborating* versus *number of times evaluated* -- is real.

---

## 1. The blocker: `tick` deep-forces the whole map

`Monad/Statistics.hs:41`:

```haskell
instance MonadStatistics TCM where
  modifyCounter x f = modifyStatistics $ force . update
    where
      -- Ulf, 2018-04-10: Neither of these approaches are strict enough in
      -- the map ... It's not enough to be strict in the values stored in
      -- the map, we also need to be strict in the *structure* of the map.
      -- A less hacky solution is to deepseq the map.
      force m = rnf m `seq` m
      update  = Map.insertWith (\ new old -> f old) x dummy
```

Every `tick` walks the entire statistics map. That is deliberate, documented,
and fine today: `Statistics = Map String Integer` (`Monad/Base.hs:3732`) holds
a handful of aggregate keys, so `rnf` over it is negligible.

§4.1 changes both factors at once. Keys go from a handful to one per `QName`
(thousands in a large development), and the tick site moves to
`unfoldDefinitionStep`, which runs millions of times. The cost is then
O(keys x ticks) -- quadratic in exactly the workload being measured, and the
profiler would dominate its own measurement.

**This is not what §5 recommends fixing.** §5 offers (a) render the `QName`
into a `String` key, or (b) generalise to `StatKey = StrKey | DefKey |
ClauseKey`, and recommends (b) "because rendering a `QName` per unfold would
itself be a measurable cost". That reasoning is correct but addresses the
smaller of the two costs. Option (b) removes the `prettyShow`; it leaves the
`rnf` exactly where it is.

§5's own "hot-path discipline" bullet states the right requirement -- "a
strict `IORef`/unboxed increment behind the profile flag, never a lazy `Map`
insert building thunks" -- and is then contradicted by the recommendation two
bullets earlier. Note also that the existing code is not lazy; it is
*over*-strict. The hazard is the opposite of the one the bullet names.

**Recommendation.** The hot counters need their own store, not a
generalisation of `Statistics`: a mutable map in an `IORef` (or a
`HashTable`) keyed on `NameId`, incremented unboxed, and folded into
`Statistics` once at end of run. `Utils/HashTable.hs` already exists and is
used this way by `TypeChecking/DeadCode.hs`. Keeping `Statistics` as-is for
the aggregate counters and adding a separate hot-counter store is a smaller
change than (b) *and* is the only version that is not quadratic.

---

## 2. §7 overstates the gating cost

> One `Bool` test per hook site, matching the existing `whenProfile` idiom.

`whenProfile` is `whenM (hasProfileOption opt)` (`Monad/Debug.hs:440`), and
`hasProfileOption` is `containsProfileOption opt <$> getProfileOptions` --
a read of the pragma options out of `TCState`, then `Set.member` on a
`Set ProfileOption` (`Utils/ProfileOptions.hs:48,104`). That is cheap, but it
is a state read plus a set lookup, not a `Bool` test.

At `Conversion.hs:170` granularity this is plainly fine, and that is the cited
precedent. But §4.1 and §4.2 sit inside `unfoldDefinitionStep` and `appDefE'`,
which are hotter by orders of magnitude. The gate should be measured on its
own, before any counter is added, so that the counter's cost is not confused
with the gate's. If it is not free, the fix is standard: hoist the flag into
a field read once per reduction, or into `ReduceEnv`.

---

## 3. `Reduce/Fast.hs` is a hard requirement, not a caveat

It is 1473 lines -- a genuinely separate evaluator, not a thin wrapper. §5
already says the numbers "silently under-report exactly where performance
matters most" if it is skipped, and offers the fallback that the output must
*say* the fast path is excluded. Both are right; the second is the important
one, and it should be treated as a release condition rather than a note. A
plausible-looking low number is worse than a missing number, because it
redirects the reader's attention somewhere else and they do not know it.

---

## 4. Ordering: §4.4 is first, not fourth

The proposal's own description of §4.4 -- static, no profiling machinery, no
run needed, "by far the cheapest item here to implement", and in the
motivating case "that single number, printed once, would have pointed at the
right three lines" -- makes it dominate every other item on value per unit of
effort. It is nonetheless ranked fourth.

Further, **half of §4.3 is also static.** §4.3 itself says the copy count "is
available statically there, so this half does not even need reduction data",
pointing at `applySection` in `Monad/Signature.hs`. Combining the two static
halves gives, with no reduction instrumentation whatsoever:

```
Apply.agda:105  OB = ASP.Obligations
                63 definitions copied, each abstracting 65 context variables
```

which is the motivating diagnosis from §2, in one line, at zero hot-path
risk. §2 claims such a line "would have replaced the whole exercise"; if that
is true, it is true of the static subset alone.

This also happens to be the shape this branch already ships three times
(`--dead-code`, `--duplicate-types`, `--search-type`): an elaboration-time
pass over information already in hand, a warning, and a report that is stable
enough to diff.

**Suggested plan.** Build the static subset first and alone. Then re-ask
whether §4.1 is still needed -- on the motivating case it may not be, and if
it is, §1 above has to be settled before it can be built at all.

---

## 5. Overlaps with work already on this branch

* **§4.8 (serialised size per definition) partly exists.** `--duplicate-types`
  and `--search-type` both report the **elaborated body size** of every
  definition, in internal-syntax nodes, computed with `termSize` over clause
  bodies. It is run-independent and is already the ranking tiebreaker in both.
  §4.5 is its dynamic counterpart. Worth reading
  `TypeChecking/DuplicateTypes.hs` (`bodySize`) before building either.
* **§8 question 3** -- attribute unfoldings to the copy, the original, or both
  -- the proposal assumes "both, with the copy as the key and the original
  shown alongside". That is what `--write-ast` already does for assumption
  sites (the site is the key, the covered definitions are listed beside it),
  so it is consistent with the branch.
* **§8 question 2** -- clause indices are unstable across edits, so they are a
  poor key for a CI gate. The same class of problem was settled for the AST
  dump by refusing to order on anything allocation-ordered (`NameId` is
  allocated in typechecking order and shifts when anything earlier is added --
  see the stability note in `TypeChecking/ASTDump.hs`). A fingerprint over the
  clause's elaborated pattern/body would be the analogous fix here.

---

## 6. Smaller notes

* §6's machine-readable output (`--profile-output=FILE.json`) matches
  `--ast-file` / `--dup-file` / `--search-file` on this branch. If it is
  built, it should take the same `-` means stdout convention and the same
  "ordered by printed name, stable under unrelated edits" rule, or CI diffs
  will churn.
* §8 question 4 (is `Sections` the right name): yes on the stated grounds --
  `where`-lifting and module application share `applySection`. Worth saying in
  the flag's help text, since a reader will not guess that `where` blocks are
  covered by something called "sections".
* §4.2's *stuck* count is the most interesting number in the proposal after
  §4.1, and the argument for it ("a clause tried thousands of times that never
  reduces is the signature of a `with`-abstraction that has stopped
  computing") is the clearest statement of a real pathology in the document.
  It is unfortunately also on the hot path, so it inherits §1 entirely.

---

## 7. Summary

| item | verdict |
|---|---|
| §4.4 where-width lint | **build first**, alone, static, no hot-path risk |
| §4.3 static half (copy count) | **build with it**, same hook (`applySection`) |
| §4.1 unfold count | right question, blocked on §1; needs its own counter store |
| §4.2 clause tried/matched/stuck | valuable, inherits §1 and the `Reduce/Fast` problem |
| §4.5 peak normal-form size | reasonable; see §5 above for the static analogue |
| §4.6 per-`QName` conversion | cheap, key is the only thing missing, as claimed |
| §4.7 constraint re-wakeup | plausible, unmeasured; no objection |
| §4.8 serialised size | partly exists already; see §5 |
| §4.9 | correctly identified as already present |
