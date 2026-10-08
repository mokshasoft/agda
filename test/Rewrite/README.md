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

## Further patterns pinned (no bug found, but plausible)

* renamings, in the facade and in the importer: refused with a reason (repair-renames)
* an applied facade reached through a chain: refused (repair-appliedchain)
* importer statement inside a nested module: indentation (repair-nested)
* a wholesale importer relying on a re-exported instance (repair-instance)
* an alias already taken in the importer: primed (repair-alias, `Taken`)

Not testable as a golden: memory (a lazily kept decision held whole modules;
found on a 300-module run and fixed by forcing each decision).
