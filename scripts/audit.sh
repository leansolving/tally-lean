#!/bin/bash
# Axiom audit and keyword check (the trust statement of README.md, made mechanical).
set -euo pipefail
cd "$(dirname "$0")/.."
raw=$(lake env lean scripts/Audit.lean)
# join the wrapped continuation lines of `#print axioms` to their first line
out=$(printf '%s\n' "$raw" | awk '/^ / {printf " %s", $0; next} {printf "\n%s", $0} END {print ""}' | sed 's/  */ /g')
printf '%s\n' "$out"
std='\[propext, (Classical.choice, )?Quot.sound\]'
bad=$(printf '%s\n' "$out" | grep "depends on axioms" | grep -vE "noTwoOnes_ten|A006506_16" | grep -vE "$std" || true)
if [ -n "$bad" ]; then echo "AUDIT FAIL: non-standard axioms:"; echo "$bad"; exit 1; fi
n=$(printf '%s\n' "$out" | grep -c "depends on axioms")
[ "$n" -eq 15 ] || { echo "AUDIT FAIL: expected 15 axiom lines, got $n"; exit 1; }
for c in noTwoOnes_ten A006506_16; do
  printf '%s\n' "$out" | grep "$c" | grep -q "native_decide" || { echo "AUDIT FAIL: control $c shows no native_decide axiom"; exit 1; }
done
if grep -rnE "sorry|admit|implemented_by|extern|partial|unsafe" Tally/; then echo "AUDIT FAIL: forbidden keyword in Tally/"; exit 1; fi
grep -rq "theorem" Tally/Spec.lean || { echo "AUDIT FAIL: grep control"; exit 1; }
echo "AUDIT OK: 13 kernel-checked theorems on the standard axioms, 2 native_decide controls, no forbidden keywords"
