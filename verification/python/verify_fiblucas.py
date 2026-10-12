#!/usr/bin/env python3
"""Checks of the three theorems from the OEIS definitions, for n <= N (default 1000000).

Every sequence is computed from its OEIS name, without the identities of the proof:

  S        A116470, the Fibonacci and Lucas numbers 1, 2, 3, 4, 5, 7, 8, 11, ...
  A214973  number of terms of the greedy representation of n by S
  A007895  number of terms of the Zeckendorf representation of n
  A214981, A179180  partial sums of A214973 and A007895 over 1..n
  A049651  (F(3n+1) - 1)/2
  A003714  fibbinary numbers, the Zeckendorf representation read as a binary word
  A048679  A003714 with the rewrite 0 -> 0, 01 -> 1 applied to its binary expansion
  A035263  parity of the 2-adic valuation of 2n
  A329320  sum_{k=0}^{floor(log2 n)} (1 - A035263(1 + floor(n/2^k)))

Checks:
  (1) the computed sequences agree with the terms listed in the OEIS;
  (2) Theorem 1.4: |5T(x) - K(x) x| <= 19x and |5Z(x) - c K(x) x| <= 13x for 1 <= x <= N,
      with T(x) = A214981(x-1), Z(x) = A179180(x-1), K(x) = max{k : F_k <= x},
      c = (5 - sqrt 5)/2 (tested exactly in integers); e_k = 5T(F_k) - k F_k satisfies
      e_{k+1} = e_k + e_{k-2} + e_{k-3} and |e_k| <= 2F_k; 5Z(F_k) = k(2F_k - F_{k-1}) - 2F_k;
      6/5 < c < 7/5;
  (3) Theorem 1.5: n first occurs in A214973 at A049651(n), and the records of A214973 are
      exactly the values A049651(n);
  (4) Theorem 1.6: A214973(n) = A329320(A048679(n)) for 1 <= n <= N;
  (5) the lemmas of the proof of Theorem 1.6: A048679(n) = sum_i 2^(k_i - 2 - (s - i)) for the
      Zeckendorf indices k_1 > ... > k_s of n, A329320(y) = sum of ceil(l/2) over the blocks of
      ones of y (lengths l), and A214973(n) = sum of ceil(l/2) over the chains k, k-2, k-4, ...
      of Zeckendorf indices, for n <= N and y < 2^20.
Prints "ALL OK" if every check passes.
"""
import sys
from bisect import bisect_right
from math import isqrt

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
FAILS = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("FAIL:", msg)


fib = [0, 1]
while len(fib) < 100:
    fib.append(fib[-1] + fib[-2])
lucas = [2, 1]
while len(lucas) < 100:
    lucas.append(lucas[-1] + lucas[-2])
S = sorted({f for f in fib if f > 0} | set(lucas))
FIBPOS = sorted({f for f in fib if f > 0})


def greedy_count(n, basis):
    c = 0
    while n > 0:
        n -= basis[bisect_right(basis, n) - 1]
        c += 1
    return c


def zeckendorf(n):
    """Indices k >= 2 of the Zeckendorf representation, largest first."""
    out = []
    while n > 0:
        k = bisect_right(fib, n, 2) - 1  # the largest k >= 2 with F_k <= n
        out.append(k)
        n -= fib[k]
    return out


def a003714(n):
    return sum(2 ** (k - 2) for k in zeckendorf(n))


def a048679(n):
    s = "0" + bin(a003714(n))[2:]  # the leading zero carries the top digit
    out, i = "", 0
    while i < len(s):
        if s[i:i + 2] == "01":
            out += "1"
            i += 2
        elif s[i] == "0":
            out += "0"
            i += 1
        else:
            raise ValueError("not fibbinary")
    return int(out, 2)


def v2(m):
    c = 0
    while m % 2 == 0:
        m //= 2
        c += 1
    return c


def a035263(n):
    return v2(2 * n) % 2


def a329320(n):
    top = n.bit_length() - 1 if n > 0 else 0
    return sum(1 - a035263(1 + n // 2 ** k) for k in range(top + 1))


# ---------------------------------------------------------------- the sequences up to N
a = [0] * (N + 1)
z = [0] * (N + 1)
for n in range(1, N + 1):
    a[n] = greedy_count(n, S)
    z[n] = greedy_count(n, FIBPOS)  # the greedy Fibonacci representation is Zeckendorf's
W = [0] * (N + 1)  # A214981
V = [0] * (N + 1)  # A179180
for n in range(1, N + 1):
    W[n] = W[n - 1] + a[n]
    V[n] = V[n - 1] + z[n]

# ---------------------------------------------------------------- (1) OEIS terms
OEIS = {
    "A214973": (1, "1,1,1,1,1,2,1,1,2,2,1,2,1,2,2,2,2,1,2,2,1,2,2,2,2,2,3,2,1,2,2,2,2,1,2,2,2,2,2,3,2,2,3,3,2,3,1,2,2,2,2,2,3,2,1,2,2,2,2,2,3,2,2,3,3,2,3,2,3,3,3,3,2,3,3,1,2,2,2,2,2,3,2,2,3,3,2,3,1,2,2,2,2,2,3,2,2,3,3"),
    "A214981": (1, "1,2,3,4,5,7,8,9,11,13,14,16,17,19,21,23,25,26,28,30,31,33,35,37,39,41,44,46,47,49,51,53,55,56,58,60,62,64,66,69,71,73,76,79,81,84,85,87,89,91,93,95,98,100,101,103,105,107,109,111,114,116,118,121,124"),
    "A179180": (0, "0,1,2,3,5,6,8,10,11,13,15,17,20,21,23,25,27,30,32,35,38,39,41,43,45,48,50,53,56,58,61,64,67,71,72,74,76,78,81,83,86,89,91,94,97,100,104,106,109,112,115,119,122,126,130,131,133,135,137,140,142,145"),
    "A049651": (0, "0,1,6,27,116,493,2090,8855,37512,158905,673134,2851443,12078908,51167077,216747218,918155951,3889371024,16475640049,69791931222,295643364939,1252365390980,5305104928861,22472785106426,95196245354567,403257766524696,1708227311453353,7236167012338110"),
    "A048679": (0, "0,1,2,4,3,8,5,6,16,9,10,12,7,32,17,18,20,11,24,13,14,64,33,34,36,19,40,21,22,48,25,26,28,15,128,65,66,68,35,72,37,38,80,41,42,44,23,96,49,50,52,27,56,29,30,256,129,130,132,67,136,69,70,144,73,74,76,39,160,81"),
    "A329320": (0, "0,1,1,1,1,2,1,2,1,2,2,2,1,2,2,2,1,2,2,2,2,3,2,3,1,2,2,2,2,3,2,3,1,2,2,2,2,3,2,3,2,3,3,3,2,3,3,3,1,2,2,2,2,3,2,3,2,3,3,3,2,3,3,3,1,2,2,2,2,3,2,3,2,3,3,3,2,3,3,3,2,3,3,3,3,4,3"),
    "A003714": (0, "0,1,2,4,5,8,9,10,16,17,18,20,21,32,33,34,36,37,40,41,42,64,65,66,68,69,72,73,74,80,81,82,84,85,128,129,130,132,133,136,137,138,144,145,146,148,149,160,161,162,164,165,168,169,170,256,257,258,260,261,264"),
    "A035263": (1, "1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1"),
}
COMPUTE = {
    "A214973": lambda n: a[n],
    "A214981": lambda n: W[n],
    "A179180": lambda n: V[n],
    "A049651": lambda n: (fib[3 * n + 1] - 1) // 2,
    "A048679": a048679,
    "A329320": a329320,
    "A003714": a003714,
    "A035263": a035263,
}
for name, (offset, data) in OEIS.items():
    terms = [int(t) for t in data.split(",")]
    got = [COMPUTE[name](offset + i) for i in range(len(terms))]
    check(got == terms, f"{name}: computed terms differ from the OEIS data")
print(f"(1) {len(OEIS)} sequences agree with their OEIS terms")

# ---------------------------------------------------------------- (2) Theorem 1.4
def T(x):
    return W[x - 1] if x >= 1 else 0


def Z(x):
    return V[x - 1] if x >= 1 else 0


def abs_le_c(A2, B2, R2):
    """|A2 + B2*sqrt5| <= R2 for integers A2, B2 >= 0, R2 >= 0 (exact)."""
    hi = R2 - A2  # need B2*sqrt5 <= hi
    lo = -R2 - A2  # need B2*sqrt5 >= lo
    ok_hi = hi >= 0 and 5 * B2 * B2 <= hi * hi
    ok_lo = lo <= 0 or 5 * B2 * B2 >= lo * lo
    return ok_hi and ok_lo


worstT = worstZ = 0.0
c_float = (5 - 5 ** 0.5) / 2
k = 2
for x in range(1, N + 1):
    while fib[k + 1] <= x:
        k += 1
    t5 = 5 * T(x) - k * x
    check(abs(t5) <= 19 * x, f"T bound fails at x={x}")
    # 5Z - c K x = (10 Z - 5 K x + K x sqrt5)/2
    check(abs_le_c(10 * Z(x) - 5 * k * x, k * x, 26 * x), f"Z bound fails at x={x}")
    worstT = max(worstT, abs(t5) / x)
    worstZ = max(worstZ, abs(5 * Z(x) - c_float * k * x) / x)
print(f"(2) T and Z bounds hold for 1 <= x <= {N}; "
      f"max |5T-Kx|/x = {worstT:.4f}, max |5Z-cKx|/x = {worstZ:.4f}")

ks = [k for k in range(1, 100) if fib[k] <= N + 1]
e = {k: 5 * T(fib[k]) - k * fib[k] for k in ks}
for k in ks:
    check(abs(e[k]) <= 2 * fib[k], f"|e_{k}| > 2F_{k}")
    check(5 * Z(fib[k]) == k * (2 * fib[k] - fib[k - 1]) - 2 * fib[k], f"5Z(F_{k}) formula at k={k}")
    if k >= 5:
        check(e[k] == e[k - 1] + e[k - 3] + e[k - 4], f"e recurrence at k={k}")
    if k >= 4:
        check(T(fib[k + 1]) == T(fib[k]) + T(fib[k - 2]) + T(fib[k - 3]) + fib[k - 1]
              if fib[k + 1] <= N + 1 else True, f"T(F_k+1) recursion at k={k}")
print(f"    e_k and 5Z(F_k) checked for k <= {ks[-1]}")

# c = (5 - sqrt5)/2 lies in (6/5, 7/5) iff 11/5 < sqrt5 < 13/5 iff 121 < 125 < 169
check(121 < 125 < 169, "c not in (1.2, 1.4)")
for n in [10, 100, 1000, 10000, 100000, 1000000]:
    if n <= N:
        print(f"    V({n})/W({n}) = {V[n] / W[n]:.6f}")
print(f"    (5 - sqrt 5)/2 = {(5 - 5 ** 0.5) / 2:.6f}")

# ---------------------------------------------------------------- (3) Theorem 1.5
first = {}
for n in range(1, N + 1):
    first.setdefault(a[n], n)
records = []
best = 0
for n in range(1, N + 1):
    if a[n] > best:
        best = a[n]
        records.append(n)
j = 1
while (fib[3 * j + 1] - 1) // 2 <= N:
    r = (fib[3 * j + 1] - 1) // 2
    check(first.get(j) == r, f"first occurrence of {j} is {first.get(j)}, not {r}")
    j += 1
check(records == [(fib[3 * i + 1] - 1) // 2 for i in range(1, j)], "records differ from A049651")
check(max(a[1:]) == j - 1, "a value above the records appears")
print(f"(3) first occurrences of 1..{j - 1} are A049651(1..{j - 1}); records = A049651")

# ---------------------------------------------------------------- (4) Theorem 1.6
for n in range(1, N + 1):
    if a[n] != a329320(a048679(n)):
        check(False, f"Kurkov formula fails at n={n}")
        break
print(f"(4) A214973(n) = A329320(A048679(n)) for 1 <= n <= {N}")

# ---------------------------------------------------------------- (5) lemmas for Theorem 1.6
def blocks(y):
    """lengths of the maximal blocks of ones in the binary word of y"""
    out, run = [], 0
    while y:
        if y & 1:
            run += 1
        elif run:
            out.append(run)
            run = 0
        y >>= 1
    if run:
        out.append(run)
    return out


def chains(ks):
    """lengths of the maximal runs k, k-2, k-4, ... in a decreasing list"""
    out = []
    for i, k in enumerate(ks):
        if i > 0 and ks[i - 1] - k == 2:
            out[-1] += 1
        else:
            out.append(1)
    return out


for y in range(1 << 20):
    if a329320(y) != sum((l + 1) // 2 for l in blocks(y)):
        check(False, f"A329320 block formula fails at y={y}")
        break
for n in range(1, N + 1):
    ks = zeckendorf(n)
    s = len(ks)
    if (a048679(n) != sum(2 ** (k - 2 - (s - i)) for i, k in enumerate(ks, 1))
            or a[n] != sum((l + 1) // 2 for l in chains(ks))):
        check(False, f"compression or chain formula fails at n={n}")
        break
print(f"(5) A048679 exponents and chain formula for n <= {N}; A329320 block formula for y < 2^20")

if FAILS:
    print(f"{len(FAILS)} FAILURES")
    sys.exit(1)
print("ALL OK")
