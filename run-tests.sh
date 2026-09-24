#!/usr/bin/env bash
# Run the Succeed/Fail goldens the way test/Succeed/Tests.hs does.
# The cabal test-suite was removed on this branch, so this stands in for it.
cd "$(dirname "$0")" || exit 1
AGDA=${AGDA:-$(ls -t dist-newstyle/build/*/*/Agda-*/x/agda/build/agda/agda 2>/dev/null | head -1)}
[ -x "$AGDA" ] || { echo "no agda binary; run: cabal build exe:agda" >&2; exit 1; }
MODE=${1:-check}   # check | accept
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
clean() {
  sed -e 's|[^ (]*test/Fail/||g' \
      -e 's|[^ (]*test/Succeed/||g' \
      -e 's|[^ (]*test/Common/||g' \
      -e 's|[^ (]*lib/prim|agda-default-include-path|g' \
      -e 's|Agda-[0-9][.0-9]*|\xc2\xabAgda-package\xc2\xbb|g'
}

compare() {
  local golden=$1 got=$2 t=$3
  if [ "$MODE" = accept ]; then printf '%s\n' "$got" > "$golden"; echo "ACCEPT $t"; return; fi
  if [ "$got" = "$(cat "$golden" 2>/dev/null)" ]; then
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
         SearchTypeHigherOrder SearchTypeLimit WideSections; do
  run_succeed $t
done
for t in DeadCodeInvalidEntry WriteASTInvalidEntry SearchTypeNotInScope; do run_fail $t; done
run_optfail DupFormatBadValue    "--duplicate-types --dup-format=bogus"
run_optfail SearchFormatBadValue "--search-type=Tm --search-format=xml"
run_optfail SearchLimitBadValue  "--search-type=Tm --search-limit=-3"
rm -rf test/Succeed/_build test/Succeed/*/_build test/Fail/_build 2>/dev/null
echo "======== $pass passed, $fail failed ========"
[ $fail -eq 0 ]
