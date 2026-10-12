#!/usr/bin/env bash
# check_small.sh -- the three theorems for small n, in Bash integer arithmetic only.
#
#   * A214973(1..99) by the greedy algorithm over the Fibonacci and Lucas numbers equals the
#     terms listed in the OEIS;
#   * the records of A214973 on [1, 8855] are 1, 6, 27, 116, 493, 2090, 8855 = A049651(1..7);
#   * Kurkov's formula A214973(n) = A329320(A048679(n)) for 1 <= n <= NMAX (default 3000);
#   * |5T(x) - K(x) x| <= 19x for 1 <= x <= NMAX.
# Prints "ALL OK" if every check passes.
set -u
NMAX=${1:-3000}
fails=0
fail() { echo "FAIL: $*"; fails=$((fails + 1)); }

F=(0 1); L=(2 1)
for ((k = 2; k < 60; k++)); do
  F[k]=$((F[k - 1] + F[k - 2])); L[k]=$((L[k - 1] + L[k - 2]))
done
# S = A116470 in increasing order, up to 10^6
S=()
for v in $(for ((k = 1; k < 32; k++)); do echo "${F[k]}"; echo "${L[k]}"; done; echo 2) ; do
  ((v <= 1000000)) && S+=("$v")
done
mapfile -t S < <(printf '%s\n' "${S[@]}" | sort -n | uniq)

# Each function leaves its value in RET.
greedy() {  # number of terms of the greedy representation of $1 by S
  local n=$1 c=0 i
  while ((n > 0)); do
    for ((i = ${#S[@]} - 1; i >= 0; i--)); do ((S[i] <= n)) && break; done
    n=$((n - S[i])); c=$((c + 1))
  done
  RET=$c
}

a003714() {  # Zeckendorf representation of $1 read as a binary word
  local n=$1 r=0 k
  while ((n > 0)); do
    for ((k = 59; k >= 2; k--)); do ((F[k] <= n)) && break; done
    r=$((r + (1 << (k - 2)))); n=$((n - F[k]))
  done
  RET=$r
}

a048679() {  # rewrite 0 -> 0, 01 -> 1 on 0x, from the top
  local x=$1 j=0 out=0
  while (((x >> j) > 0)); do j=$((j + 1)); done   # position of the leading zero
  while ((j >= 0)); do
    if ((j >= 1 && ((x >> (j - 1)) & 1) == 1)); then out=$((2 * out + 1)); j=$((j - 2))
    else out=$((2 * out)); j=$((j - 1)); fi
  done
  RET=$out
}

a035263() {  # parity of the 2-adic valuation of 2n
  local m=$((2 * $1)) v=0
  while ((m % 2 == 0)); do m=$((m / 2)); v=$((v + 1)); done
  RET=$((v % 2))
}

a329320() {
  local y=$1 top=0 s=0 k
  while (((y >> (top + 1)) > 0)); do top=$((top + 1)); done
  for ((k = 0; k <= top; k++)); do a035263 $((1 + (y >> k))); s=$((s + 1 - RET)); done
  RET=$s
}

OEIS="1,1,1,1,1,2,1,1,2,2,1,2,1,2,2,2,2,1,2,2,1,2,2,2,2,2,3,2,1,2,2,2,2,1,2,2,2,2,2,3,2,2,3,3,2,3,1,2,2,2,2,2,3,2,1,2,2,2,2,2,3,2,2,3,3,2,3,2,3,3,3,3,2,3,3,1,2,2,2,2,2,3,2,2,3,3,2,3,1,2,2,2,2,2,3,2,2,3,3"
IFS=, read -r -a terms <<< "$OEIS"
for ((n = 1; n <= ${#terms[@]}; n++)); do
  greedy $n
  [ "$RET" = "${terms[n - 1]}" ] || fail "A214973($n)"
done
echo "A214973(1..${#terms[@]}) agrees with the OEIS"

LIM=$((NMAX > 8855 ? NMAX : 8855))
a=(0); best=0; rec=()
for ((n = 1; n <= LIM; n++)); do
  greedy $n; a[n]=$RET
  if ((a[n] > best)); then best=${a[n]}; rec+=("$n"); fi
done
[ "${rec[*]:0:7}" = "1 6 27 116 493 2090 8855" ] || fail "records: ${rec[*]}"
echo "records of A214973 on [1, $LIM]: ${rec[*]}"

T=0; k=2
for ((x = 1; x <= NMAX; x++)); do
  T=$((T + a[x - 1]))
  while ((F[k + 1] <= x)); do k=$((k + 1)); done
  d=$((5 * T - k * x)); ((d < 0)) && d=$((-d))
  ((d <= 19 * x)) || fail "T bound at $x"
done
echo "|5T(x) - K(x)x| <= 19x for 1 <= x <= $NMAX"

for ((n = 1; n <= NMAX; n++)); do
  a003714 $n; a048679 "$RET"; a329320 "$RET"
  [ "${a[n]}" = "$RET" ] || fail "Kurkov at $n"
done
echo "A214973(n) = A329320(A048679(n)) for 1 <= n <= $NMAX"

if ((fails > 0)); then echo "$fails FAILURES"; exit 1; fi
echo "ALL OK"
