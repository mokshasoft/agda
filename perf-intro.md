# Profiling a slow Agda development: a short introduction

This branch adds reports that say *where checking time and memory go*, per
definition and per source line. Upstream `--profile` says how long things
took in aggregate. These reports add: how often each definition was
evaluated, which definition's checking caused it, and what each piece of
checking cost in time and memory.

## Quick start

```sh
agda Slow.agda --profile=reduction --profile=allocation --profile=definitions \
     --counters-folded=slow
```

This writes:

* `agda-counters.json`: the main report. Choose another name with
  `--counters-file=PATH` (`-` for stdout) and plain text with
  `--counters-format=text`.
* `slow.time.folded`, `slow.allocation.folded`, `slow.unfoldings.folded`:
  flame-graph input. Open them in <https://www.speedscope.app> or pass them
  to `flamegraph.pl`.

Each `--profile` option adds one measure. Use any combination:

| option | measures |
|---|---|
| `--profile=reduction` | how often each definition is unfolded, and which checking caused it |
| `--profile=allocation` | bytes allocated while checking each site |
| `--profile=definitions` | CPU time per site (upstream's option; the time also goes into this report) |
| `--profile=conversion` | conversion checks per head symbol (only together with one of the above, or `--counters-file`) |

## What is measured: sites

Checking is divided into **sites**:

* each definition;
* each module application, `module M = N args`;
* the work after each declaration: `[highlighting]`, and `[constraints]`
  (solving its leftover constraints, freezing its metas);
* the checks after each mutual block: `[positivity]`, `[termination]`,
  `[confluence]`, `[injectivity]`, `[projection-likeness]`.

A site that isn't a definition is named after the first name written in its
declaration or block, for example `[termination] M.f`. Names Agda generates,
such as the `with-NNNN` functions, are skipped. Such a site's `range` covers
the whole declaration or block, and its `block` gives the block's size:
`members` (hand-written names, with the first ten in `names`), `generated`,
`clauses`, and `hasDataOrRecord`.

Some checks are split into sub-sites, nested in them, so that their cost can
be divided:

* `[positivity/graph]` builds the occurrence graph and `[positivity/closure]`
  closes it. Their `details` give the graph's `nodes`, `edges`,
  `closedEdges` and `cyclicComponents`.
* `[termination/dot-patterns]`, `[termination/call-arguments]`,
  `[termination/call-matrix]` and `[termination/reduce-away-call]` are the
  places where the termination checker reduces. A sub-site is entered once
  per call, and `entries` says how many times.

Sites nest: a `where` definition sits inside its parent. Every cost is given
twice, as the site's **own** share and **including** what is nested in it.

Only the modules of your project are counted (the git repository or
`.agda-lib` of the file you check). A library that gets re-checked because
its interfaces are stale does not add its own work. Library definitions
*unfolded by your code* are still counted: that is often exactly where the
cost shows.

## The report

* **`sites`**: one row per site with every measure you asked for. Start
  here. Sort by `bytes` or `timeMicros` (own share) to find the worst
  offenders.
* **`modules`**: the sites' own shares summed by file, largest first. The
  modules add up to the whole run.
* **`unfoldingsByCause`**: for each site, the unfoldings its checking
  caused, the five definitions it unfolded most (`unfoldedMost`), and the
  five *functions* it unfolded most (`unfoldedMostFunctions`). Constructors
  and datatypes tend to fill the first list; the second is the one to act
  on.
* **`unfoldings`**: how often each definition was unfolded, anywhere.
  Filter on `"kind": "function"`: datatypes and postulates are counted
  whenever reduction meets them, which is cheap.
* **`countedModules`**: which modules were checked, not loaded from an
  interface. Compare two reports only when these agree.
  **`uncountedModules`** lists the modules that were checked but not
  counted, with the reason, which is usually that they are outside the
  project.

Every row has `name`, `kind`, `source` and `range`, so a `where` definition
inside a module named `_` can still be found. A definition's range is where
it is bound, which also holds for modules read back from an interface. In
the folded stacks each frame carries its line, `M.f:120`.

## When checking never finishes

The reports are written however the run ends:

* **Type error, heap overflow, Ctrl-C:** the report is written as the run
  dies, marked `"complete": false`. It lists the sites being checked at that
  moment, innermost first, with the time and bytes each had used so far.
  That is usually the answer to "where did it blow up?".  A snapshot cannot
  read the bytes of the sites still running, so it gives
  `"allocatedSoFar": null` for them.
* **Killed outright** (`kill -9`, an out-of-memory killer, a job runner's
  timeout): nothing can be written at that point, so the report is rewritten
  every `--counters-snapshot=SECONDS` (default 60; `0` turns it off) while
  the run goes. The last snapshot survives, marked with
  `snapshotAtSeconds`.

Use `timeout --foreground -s INT`, not plain `timeout`. Plain `timeout`
sends SIGTERM, which leaves only the last snapshot.

## A static check: `--wide-sections=N`

This needs no run: it can be used on code that never finishes. It lists
every `where` block and module application whose definitions abstract over
at least `N` context variables, ranked by width × definitions. A one-line
`module OB = X.Obligations args` inside a deep `where` can create sixty
definitions, each sixty binders wide, and the source never shows it. With
`--profile=reduction` each section also shows how often its definitions
were unfolded. Output goes to `--wide-file` (default
`agda-wide-sections.json`).

## Reading the numbers

* **Counts, bytes and time answer different questions.** Many unfoldings
  point at repeated evaluation. Many bytes with few unfoldings point at
  building large terms during elaboration. That is a different problem with
  a different fix.
* **Bytes allocated, not bytes live.** A heap overflow is about what stays
  live, but a site that allocates gigabytes is still the first place to
  look.
* **Module-application copies are inlined where they are used.** A copy's
  unfoldings count its use sites; the work of running it shows up on the
  original definition.
* **Byte and time figures depend on GHC and the machine.** Compare them
  within one build. Unfolding counts are exact and repeatable.

## Example, from a real development

In `Apply.agda` (about 16 minutes), 80% of 78.6 million unfoldings came from
checking one `where` definition. `run17` was a 17-step `FlatSteps` chain
whose intermediate states Agda had to infer by evaluation, and the report
gave its line (173). `PairAssemble.agda`, which ran out of heap, turned out
to be a different problem. The report named the site it died in
(`dispatch-g`, line 378) and showed 17 GB allocated with fewer than 100,000
unfoldings: elaboration, not evaluation.
