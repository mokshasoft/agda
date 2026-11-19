# test/Rewrite: the in-place rewrites

`--remove-dead-imports` and `--repair-reexports` rewrite source files. Each
directory here is a scenario (its modules, `main`, `runs`: one line of flags per
run); `<scenario>.golden` records each run's report, every rewritten module in
full, and whether the result checks again under `-W error`.

Run: `AGDA_BIN=<agda> agda-tests -p '/Rewrite/'` (add `--accept` to regenerate,
then READ the diff: a golden is a claim that the output is what a human would
write, not just what the tool did).

## Every bug found so far, and the scenario that pins it

Found on the Once formalisation (2026-10-07/08), each one a shape the earlier
goldens did not have.

| # | Bug | Scenario |
|---|---|---|
| D1 | `using (module P)`: the kept item lost its `module` keyword | dead-basic |
| D2 | an emptied renaming list left `renaming ()` | dead-basic |
| D3 | a statement with an alias (`as R`) deleted though `R.x` is used | dead-basic |
| D4 | `import M` left behind though another statement still binds `M` | dead-basic |
| D5 | a deleted statement left its trailing comment / indentation | dead-basic |
| D6 | wholesale opens (no `using`) never reported; applications logged as `_` | dead-basic |
| D7 | a single dead item of `open M args using (…)` not found | dead-basic |
| D8 | an instance named in an application's list removed (copies are not in the signature at scope-check time) | dead-instapp |
| D9 | a rewrite mid-run made Agda check the module again | (all: rewrites happen at the end of the run) |
| D10 | a statement inside `let`/not starting its line rewritten | dead-shapes |
| D11 | `public` statements and duplicates | dead-shapes |
| D12 | a multi-line `using` list collapsed onto one line | dead-layout |
| D13 | a dead statement inside a `where` block; a wholesale open used only for an instance (kept) | dead-layout |
| D14 | a module item used only through a nested qualifier (`ShapeC.CaseShape.shape`, `module RS = ResuspC.Resusp n`) removed: the full qualifier's lineage starts inside the item's module (found on Once, plan 0.152, 2026-11-18) | dead-qualhead |
| D15 | a statement on `M` left empty deleted although `M.x` is written before the only surviving statement on `M` (a later statement does not scope an earlier use): it becomes `import M` unless a top-level statement on `M` survives before the first qualified use (found on Once, plan 0.152, 2026-11-18) | dead-qual-later |
| R1 | an applied facade (`open import F args`): lineage hop `.#F-1234` not recognised | repair-basic |
| R2 | qualified uses rewritten fully qualified (`Once.Parser.Entry`) | repair-alias, repair-basic |
| R3 | a qualified OPERATOR use refused / garbled | repair-basic |
| R4 | `public` after the directive's `)` not found | repair-layout |
| R5 | a submodule re-export reached through a chain refused | repair-basic (RepairH) |
| R6 | the same module imported twice (no merging, across statements and targets) | repair-merge, repair-basic, repair-importer-shapes |
| R7 | a redundant `import X` next to an `open import X` | repair-basic |
| R8 | a chain of re-exports removed in one run garbled qualified names | repair-chain3 |
| R9 | the qualifier taken as only its first component (`Once.X.y`) | repair-basic (`RepairF.Pair.fst`) |
| R10 | a record module opened in the facade but defined elsewhere | repair-fullyqualified |
| R11 | a `module N` item not dropped from the importer's list | repair-moduleitem |
| R12 | an instance listed in the importer's `using` (used by instance search only) | repair-instance-listed |
| R13 | `hiding (x)` on the facade after `x` stopped being exported | repair-importer-shapes |
| R14 | no import of the facade to put a new import after | repair-fallback |
| R15 | an overloaded constructor/field moved as its FIRST candidate only (`_*_` of `Type` and of `IRTy`: the facade's lost) | repair-overloaded |
| R16 | an importer `open import F as A …` ignored entirely (logged as `open A`: its uses not moved, its `hiding` of re-exported names kept) | repair-hiding-alias |
| R17 | an `import X as A` added after an importer whose directive wraps: indented as the continuation line (a parse error at top level) | repair-record-qualifier |
| R18 | a qualifier naming a RECORD module reached through the facade (`NamedCtx.size`) replaced by the module alias alone (`Classify.size`: not in scope) | repair-record-qualifier |
| R19 | a module item used as the head of a qualifier (`Inner.twice`, `Ctx.size`) through the target was requalified (`Q.PN.twice`, dropping `Inner`) and the item never moved: the head is a module item used, it moves to the source's `using`, and the qualified use keeps its text (found on Once, plan 0.152 A(2b), 2026-11-18) | repair-named-instance, repair-record-qualifier |
| R20 | a re-export that renames (`renaming (map to mmap) public`) was refused ("it renames"): each importer now writes the renaming entry itself (a new `open import X using (…) renaming (…)`, or `using () renaming (…)` beside its own statement on X); a renamed name used qualified is refused (found on Once, plan 0.152 A(2), IRObsCorrect.Prelude, 2026-11-18) | repair-renaming |
| R21 | a needed name merged into the importer's own `open import X using (…)` that sat inside a nested module (`module PairTrace where open import Data.List.Properties using (…)`): a use in a sibling module lost it (NotInScope). Only a top-level statement is a merge target; a new statement goes after a top-level statement the names came through first (found on Once, plan 0.152 A(2), IRObsCorrect/Pair/Chain, 2026-11-19) | repair-merge-nested |
| R22 | an importer reaching a facade's submodule re-export through its own NAMED instance (`module StackSlots = StackSlots x86-32-layout …` + `open StackSlots public`) was taken for the bare facade (only `.#` generated hops counted as applied): it got `import F` + `open F.N using (x)`, the UNAPPLIED copy (UnequalTerms: the parameters became arguments), and a second `import F` beside the plain one. Now the lineage's application hops are read: a named instance right after the statement gives `open FI.N using (x)` / `FI.N.x`; an application elsewhere on the way is refused; a plain `import M` is reused (found on Once, plan 0.152 A(2b), X86-32/Layout, 2026-11-19) | repair-instance-submodule |
| R23 | a target inside an anonymous section (`module _ (val : V) where module RunTrace = … ; open RunTrace public`): the lineage's `_` hop (the section, opened into the facade) hid the crossing, so `RTx.run-events-noncall val …` was not rewritten ("applied, 0 importer(s)"; NotInScope). A `_` hop is now no hop: the use becomes `Fx.GI.g t` (the section parameter stays an argument). R22's named-instance route excludes generated `.#` applications (repair-appliedchain stays refused) (found on Once, plan 0.152 A(2b), Arith/Backend/*/RunTrace, 2026-11-19) | repair-section-instance |
| R24 | a named instance made from an ALIAS (`import EventEngine as Engine` + `module EE = Engine args`): the lineage writes the hop as `Engine`, not the facade's name, so neither `EE.fetch-block-head` nor `open EE using (…)` was seen to cross the target (NotInScope). A hop that is an `import M as A` alias of the importer is read as M (found on Once, plan 0.152 A(2b), RiscV64/ConcFlatSim, 2026-11-19) | repair-alias-instance |
| R25 | a target `open C using (…) public` whose module `C` is in the facade only through another open (`open FlatSimulation public`, itself a target in the same run): importers got `using (module C)` + `open C using (…)` — a module the facade no longer exports (ModuleDoesntExport, then NotInScope). Importers now name the module by its path inside the facade (`using (module FlatSimulation)` + `open FlatSimulation.C using (…)`; `_` components dropped); a path through an anonymous application is refused (found on Once, plan 0.152 A(2b), X86-32.agda / ConcFlatSim, 2026-11-19) | repair-submodule-path |
| R26 | R22's named-instance route when the instance is applied with a directive (`module FlatSimulation = FlatSimulation args using (…)`): its copy holds only what it lists, so `open FlatSimulation.CompiledCorrespondence` named a module the copy lacks (NoSuchModule). The application's directive is not logged, so the route is refused with a reason ("add the submodule to it by hand") (found on Once, plan 0.152 A(2b), RiscV64/ConcFlatSim, 2026-11-19) | repair-instance-restricted |
| R27 | R24 generalised: the alias was made in ANOTHER module (`import X86-32.FlatCorrespondence as FC; module C = FC FS word-eq` in FlatSimulation; `open C using (HeapView)` in ArithBlockValue): the hop `FC` is written as there, and a hop from an interface has no range to find its file. Every module of the run records its `import M as A` lines; a hop `A` that some module binds to the facade is read as the facade (found on Once, plan 0.152 A(2b), X86-32/ArithBlockValue, 2026-11-19) | repair-alias-elsewhere |

## Scope-only rounds

`--only-scope-checking` with `--repair-reexports`: every module the run checks from source is only
scope-checked (the repair reads scope only; an overloaded name already means every candidate), no
interface is written, and a module made this run is reused from the decoded-module cache by its source
hash (without that, each importer re-made it: 787 checks for 85 modules on Once). Instances of such a
module (no signature) are read off its declarations, a module application's copies included. A later
full run is the verification. On Once's IRObsCorrect batch (85 modules): 74 s vs ~25 min, the same
messages and sources (repair-scope-only: a diamond import and an instance that must move).

## Further patterns pinned (no bug found, but plausible)

* renamings in the facade: each importer writes the entry itself (R20); in the importer: refused with a reason (repair-renames)
* an applied facade reached through a chain: refused (repair-appliedchain)
* importer statement inside a nested module: indentation (repair-nested)
* a wholesale importer relying on a re-exported instance (repair-instance)
* an alias already taken in the importer: primed (repair-alias, `Taken`)

Not testable as a golden: memory (a lazily kept decision held whole modules;
found on a 300-module run and fixed by forcing each decision).
