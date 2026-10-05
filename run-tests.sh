#!/usr/bin/env bash
# Run the Succeed/Fail goldens the way test/Succeed/Tests.hs does.
# The cabal test-suite was removed on this branch, so this stands in for it.
cd "$(dirname "$0")" || exit 1
AGDA=${AGDA:-$(ls -t dist-newstyle/build/*/*/Agda-*/x/agda/build/agda/agda 2>/dev/null | head -1)}
[ -x "$AGDA" ] || { echo "no agda binary; run: cabal build exe:agda" >&2; exit 1; }
MODE=${1:-check}   # check | accept
# Agda's output is full of Unicode, and GHC encodes it by the locale. Under a
# non-UTF-8 locale every test fails on the first arrow, so the locale is set
# here rather than inherited. C.UTF-8 is built into glibc since 2.35 and
# needs no locale archive, which a Nix shell may not provide.
export LC_ALL=C.UTF-8
pass=0; fail=0
run_succeed() {
  local t=$1 dir=test/Succeed
  rm -rf $dir/_build $dir/*/_build 2>/dev/null
  local got
  got=$($AGDA -v0 -i$dir -itest/ -vimpossible:10 -vwarning:1 --no-libraries \
          $(cat $dir/$t.flags) $dir/$t.agda 2>&1 | clean)
  compare "$dir/$t.warn" "$got" "$t"
}
run_fail() {
  local t=$1 dir=test/Fail
  rm -rf $dir/_build 2>/dev/null
  local got
  got=$($AGDA -v0 -i$dir -itest/ -vimpossible:10 -vwarning:1 --no-libraries \
          $(cat $dir/$t.flags) $dir/$t.agda 2>&1 | clean | sed -n '/error:/,$p')
  compare "$dir/$t.err" "$got" "$t"
}
# A failing module whose golden is the WHOLE output, not just the error:
# for --wide-sections the incomplete report printed before the error is the
# point of the test.
run_fail_whole() {
  local t=$1 dir=test/Fail
  rm -rf $dir/_build 2>/dev/null
  local got
  got=$($AGDA -v0 -i$dir -itest/ -vimpossible:10 -vwarning:1 --no-libraries \
          $(cat $dir/$t.flags) $dir/$t.agda 2>&1 | clean)
  compare "$dir/$t.err" "$got" "$t"
}
# Bad option values are rejected during option parsing, before any type
# checking, so they print `Error: ...` rather than an `error: [Code]` block
# and run_fail's extraction finds nothing.  They get their own category,
# comparing the whole output, with goldens in test/Fail/<name>.opterr.
run_optfail() {
  local t=$1 flags=$2 dir=test/Fail
  rm -rf $dir/_build 2>/dev/null
  local got
  got=$($AGDA -v0 -i$dir -itest/ --no-libraries $flags \
          $dir/OptionErrorDummy.agda 2>&1 | clean)
  compare "$dir/$t.opterr" "$got" "$t"
}

# Mirror test/Utils.hs `cleanOutput'`: the real harness rewrites machine- and
# version-specific paths out of Agda's output before comparing it against a
# golden. Without this a golden embeds the absolute path of whoever generated
# it and fails for everyone else.
# The prefix stops at a double quote too, as in test/Utils.hs, so that a JSON
# report's quoted paths keep their opening quote.
clean() {
  sed -e 's|[^ ("]*test/Fail/||g' \
      -e 's|[^ ("]*test/Succeed/||g' \
      -e 's|[^ ("]*test/Common/||g' \
      -e 's|[^ ("]*lib/prim|agda-default-include-path|g' \
      -e 's|Agda-[0-9][.0-9]*|\xc2\xabAgda-package\xc2\xbb|g'
}

# A JSON report's golden must itself be JSON. Normalisation once broke this
# silently: every golden still matched the output, and none of them parsed.
# The report comes first in the golden; Agda's warnings may follow it.
check_json() {
  local golden=$1 t=$2
  if python3 -c 'import json,sys; json.JSONDecoder().raw_decode(open(sys.argv[1], encoding="utf-8").read().lstrip())' "$golden" 2>/dev/null; then
    echo "PASS  $t (valid JSON)"; pass=$((pass+1))
  else
    echo "FAIL  $t (golden is not valid JSON)"; fail=$((fail+1))
  fi
}

# --profile=allocation and --profile=definitions report bytes and CPU time,
# which depend on the GHC version, the build and the machine, so their test
# checks the report's structure rather than a golden. --profile=definitions
# also prints its own table after the report, so only the first JSON value
# is read.
check_sites() {
  local t=ProfileAllocation dir=test/Succeed
  rm -rf $dir/_build 2>/dev/null
  if $AGDA -v0 -i$dir -itest/ --no-libraries --profile=allocation \
       --profile=definitions --counters-file=- $dir/$t.agda 2>&1 | python3 -c '
import json, sys
doc, _ = json.JSONDecoder().raw_decode(sys.stdin.read().lstrip())
a = {r["name"].replace("ProfileAllocation.", ""): r for r in doc["counters"]["sites"]}
for d in ["double", "f", "_.g", "test", "[termination] f"]:
    assert d in a, "no row for " + d
for d in ["double", "f", "_.g", "test"]:
    assert 0 < a[d]["bytes"] <= a[d]["bytesWithNested"], d
    assert 0 <= a[d]["timeMicros"] <= a[d]["timeMicrosWithNested"], d
assert a["f"]["bytesWithNested"] >= a["f"]["bytes"] + a["_.g"]["bytesWithNested"], "f lacks g"
assert a["[termination] f"]["kind"] == "termination"
assert "[constraints] f" in a, "no row for the constraints after f"
'; then
    echo "PASS  $t (structure)"; pass=$((pass+1))
  else
    echo "FAIL  $t (structure)"; fail=$((fail+1))
  fi
}

# The report of a run that checks two modules, ProfileSites and the
# ProfileSitesImport it imports: the imported module's sites keep their
# ranges, a mutual block with with-functions is named after the first name
# written in it and has the whole block's range and size, the checks split
# into sub-sites are there, and the module totals add up.  Bytes vary, so
# this checks structure; the folded stacks are checked for line numbers.
check_profile_sites() {
  local t=ProfileSites dir=test/Succeed tmp
  rm -rf $dir/_build 2>/dev/null
  tmp=$(mktemp -d)
  $AGDA -v0 -i$dir -itest/ --no-libraries --profile=allocation --profile=reduction \
    --counters-file=$tmp/report.json --counters-folded=$tmp/stacks \
    $dir/$t.agda >/dev/null 2>&1
  if python3 - "$tmp" <<'PY'
import json, sys, os
tmp = sys.argv[1]
doc = json.load(open(os.path.join(tmp, "report.json"), encoding="utf-8"))
c = doc["counters"]
sites = {r["name"]: r for r in c["sites"]}
imp = [r for r in c["sites"] if r.get("source", "").endswith("ProfileSitesImport.agda")]
assert imp, "no site of the imported module"
for r in imp:
    assert "range" in r, "imported site without a range: " + r["name"]
assert doc["complete"], "the run did not finish"
assert not [n for n in sites if "with-" in n], "a site is named after a with-function"
withs = [r for r in c["unfoldings"] if "with-" in r["name"]]
assert withs, "no with-function was unfolded"
for r in withs:
    assert r.get("withFunctionOf") in ("ProfileSites.even?", "ProfileSites.odd?"), r
    assert "range" in r, r
pos = sites["[positivity] ProfileSites.even?"]
b = pos["block"]
assert b["members"] == 2 and b["names"] == ["ProfileSites.even?", "ProfileSites.odd?"], b
assert b["generated"] == 2 and not b["hasDataOrRecord"], b
src = open("test/Succeed/ProfileSites.agda", encoding="utf-8").read().splitlines()
first = src.index("even? : Nat → Bool") + 1
last = src.index("... | b = b") + 1
assert pos["range"].endswith(":%d.1-%d.12" % (first, last)), pos["range"]
g = sites["[positivity/graph] ProfileSites.even?"]
assert g["details"]["nodes"] > 0 and g["details"]["edges"] > 0, g
assert "closedEdges" in sites["[positivity/closure] ProfileSites.even?"]["details"]
assert sites["[termination/call-arguments] ProfileSites.even?"]["entries"] >= 2
assert doc["uncountedModules"] == [], doc["uncountedModules"]
assert sorted(doc["countedModules"]) == ["ProfileSites", "ProfileSitesImport"]
mods = {m["source"]: m for m in c["modules"]}
for src, m in mods.items():
    rs = [r for r in c["sites"] if r.get("source") == src]
    assert m["sites"] == len(rs), src
    assert m["bytes"] == sum(r["bytes"] for r in rs), src
    assert m["unfoldingsCaused"] == sum(r["unfoldingsCaused"] for r in rs), src
assert sum(m["bytes"] for m in c["modules"]) == sum(r["bytes"] for r in c["sites"])
for cause in c["unfoldingsByCause"]:
    for u in cause["unfoldedMost"]:
        assert "kind" in u, u
    for u in cause["unfoldedMostFunctions"]:
        assert u["kind"] == "function", u
stacks = open(os.path.join(tmp, "stacks.allocation.folded"), encoding="utf-8").read().splitlines()
assert any(";ProfileSitesImport.double:13 " in l for l in stacks), "no line on an imported frame"
PY
  then
    echo "PASS  $t (structure)"; pass=$((pass+1))
  else
    echo "FAIL  $t (structure)"; fail=$((fail+1))
  fi
  rm -rf "$tmp"
}

# The folded stacks of --counters-folded. Unfolding counts are exact, so the
# unfoldings file is compared against a golden, ProfileAllocation.folded.
check_folded() {
  local t=ProfileAllocation dir=test/Succeed tmp
  rm -rf $dir/_build 2>/dev/null
  tmp=$(mktemp -d)
  $AGDA -v0 -i$dir -itest/ --no-libraries --profile=reduction \
    --counters-file=$tmp/report.json --counters-folded=$tmp/stacks \
    $dir/$t.agda >/dev/null 2>&1
  if [ -s "$tmp/stacks.unfoldings.folded" ]; then
    compare "$dir/$t.folded" "$(clean < $tmp/stacks.unfoldings.folded)" "$t (folded)"
  else
    # Never compared, and never accepted: an empty golden would pass forever.
    echo "FAIL  $t (folded): no stacks.unfoldings.folded written"; fail=$((fail+1))
  fi
  rm -rf "$tmp"
}

compare() {
  local golden=$1 got=$2 t=$3
  if [ "$MODE" = accept ]; then printf '%s\n' "$got" > "$golden"; echo "ACCEPT $t"; return; fi
  if [ ! -e "$golden" ]; then
    # Otherwise empty output would match a missing golden and pass.
    echo "FAIL  $t (no golden: $golden; run ./run-tests.sh accept)"; fail=$((fail+1))
  elif [ "$got" = "$(cat "$golden")" ]; then
    echo "PASS  $t"; pass=$((pass+1))
  else
    echo "FAIL  $t"; diff <(printf '%s\n' "$got") "$golden" | head -25; fail=$((fail+1))
  fi
}
for t in WriteASTBasic WriteASTTransitive WriteASTRecordFields WriteASTPragmas \
         WriteASTPragmaSites DeadCodeAnalysis DeadCodeMultiModule \
         DeadCodeRecordFields DeadCodeWithBuiltins \
         DuplicateTypesBasic DuplicateTypesModules DuplicateTypesFields \
         DuplicateTypesJSON DuplicateTypesClean SearchTypeBasic \
         SearchTypeInstance SearchTypePrefix SearchTypeRanking \
         SearchTypeJSON SearchTypeUnanchored SearchTypeUnanchoredOff \
         SearchTypeHigherOrder SearchTypeLimit WideSections WideSectionsJSON \
         ProfileCountersJSON ProfileCountersText ProfileConversionAlone \
         WideSectionsUnfold ProfileSites; do
  run_succeed $t
done
[ "$MODE" = accept ] || check_sites
[ "$MODE" = accept ] || check_profile_sites
check_folded
for t in DuplicateTypesJSON SearchTypeJSON WideSectionsJSON ProfileCountersJSON; do
  [ "$MODE" = accept ] || check_json test/Succeed/$t.warn $t
done
for t in DeadCodeInvalidEntry WriteASTInvalidEntry SearchTypeNotInScope; do run_fail $t; done
run_fail_whole WideSectionsAbort
run_fail_whole ProfileCountersAbort
run_optfail DupFormatBadValue    "--duplicate-types --dup-format=bogus"
run_optfail SearchFormatBadValue "--search-type=Tm --search-format=xml"
run_optfail SearchLimitBadValue  "--search-type=Tm --search-limit=-3"
run_optfail WideFormatBadValue   "--wide-sections=1 --wide-format=xml"
run_optfail WideSectionsBadValue "--wide-sections=many"
run_optfail CountersFormatBadValue "--profile=reduction --counters-format=csv"
rm -rf test/Succeed/_build test/Succeed/*/_build test/Fail/_build 2>/dev/null
echo "======== $pass passed, $fail failed ========"
[ $fail -eq 0 ]
