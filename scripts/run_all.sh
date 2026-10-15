#!/usr/bin/env bash
# run_all.sh -- re-run every check of "The Number of Terms in Greedy Fibonacci--Lucas
# Representations" (Kimberling's limit, the records of A214973 and Kurkov's formula).
#
#   C       verification/c/kimberling.c          Theorems 1.4 and 1.5 for n <= 10^8: the bounds
#                                                for T and Z, e_k, Z(F_k), the records
#   C++     verification/cpp/kurkov.cpp          Theorem 1.6 for n <= 10^8, from the fibbinary
#                                                numbers listed by successor; the pairing lemma
#   Shell   verification/shell/check_small.sh    Bash integer arithmetic only, n <= 3000
#   Python  verification/python/verify_fiblucas.py   all three theorems from the OEIS
#                                                definitions, n <= 10^6, and the OEIS terms
#   Julia   verification/julia/verify_lemmas.jl  every lemma of the proofs, BigInt where the
#                                                statement is about all k (if julia is on PATH or
#                                                $JULIA is set)
#   Lean    verification/lean                    the theorems for every n, over Mathlib v4.34.1
#                                                (if lake is on PATH; LEAN=0 skips it)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/kimberling" "$V/c/kimberling.c" || fail "compile kimberling.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/kurkov" "$V/cpp/kurkov.cpp" || fail "compile kurkov.cpp"
"$BUILD/kimberling" > "$BUILD/c.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/c.txt" \
  && ok "C: Theorems 1.4 and 1.5 for n <= 10^8" || fail "C (see build/c.txt)"
"$BUILD/kurkov" > "$BUILD/cpp.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/cpp.txt" \
  && ok "C++: Theorem 1.6 for n <= 10^8" || fail "C++ (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_small.sh" > "$BUILD/sh.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/sh.txt" \
  && ok "check_small.sh" || fail "check_small.sh (see build/sh.txt)"

echo "== Python"
python3 "$V/python/verify_fiblucas.py" > "$BUILD/py.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py.txt" \
  && ok "verify_fiblucas.py" || fail "verify_fiblucas.py (see build/py.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_lemmas.jl" > "$BUILD/jl.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl.txt" \
    && ok "verify_lemmas.jl" || fail "verify_lemmas.jl (see build/jl.txt)"
fi

echo "== Lean"
if [ "${LEAN:-1}" = 0 ]; then echo "Lean skipped (LEAN=0)";
elif ! command -v lake > /dev/null; then echo "lake not found: skipping (install elan)"; else
  if grep -rqE '\bsorry\b|\badmit\b|native_decide|^axiom ' "$V/lean/FibLucas" "$V/lean/FibLucas.lean"; then
    fail "Lean sources contain sorry, admit, native_decide or an axiom"
  fi
  out=$(cd "$V/lean" && { lake exe cache get > /dev/null 2>&1 || true; } && lake build 2>&1 \
        && lake env lean Axioms.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<< "$out")
  if [ $st -eq 0 ] && ! grep -q "error\|sorryAx" <<< "$out" && [ "$n" = 10 ]; then
    ok "Lean: ten theorems, axioms propext, Classical.choice, Quot.sound only"
  else fail "Lean (see build/lean.txt)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
