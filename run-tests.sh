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
          $(cat $dir/$t.flags) $dir/$t.agda 2>&1)
  compare "$dir/$t.warn" "$got" "$t"
}
run_fail() {
  local t=$1 dir=test/Fail
  rm -rf $dir/_build 2>/dev/null
  local got
  got=$($AGDA -v0 -i$dir -itest/ -vimpossible:10 -vwarning:1 --no-libraries \
          $(cat $dir/$t.flags) $dir/$t.agda 2>&1 | sed -n '/error:/,$p')
  compare "$dir/$t.err" "$got" "$t"
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
         SearchTypeJSON SearchTypeUnanchored SearchTypeUnanchoredOff; do
  run_succeed $t
done
for t in DeadCodeInvalidEntry WriteASTInvalidEntry SearchTypeNotInScope; do run_fail $t; done
rm -rf test/Succeed/_build test/Succeed/*/_build test/Fail/_build 2>/dev/null
echo "======== $pass passed, $fail failed ========"
[ $fail -eq 0 ]
