"""Writes figures/ratio.dat: n, V(n)/W(n) and (W(n) - n log_phi(n)/5)/n,
(V(n) - c n log_phi(n)/5)/n at about 400 values of n up to N (default 10^7),
computed from the definitions of A214973 and A007895."""
import math
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
phi = (1 + 5 ** 0.5) / 2
c = (5 - 5 ** 0.5) / 2

fib = [0, 1]
while fib[-1] <= N:
    fib.append(fib[-1] + fib[-2])
luc = [2, 1]
while luc[-1] <= N:
    luc.append(luc[-1] + luc[-2])
S = sorted({f for f in fib if f >= 1} | set(luc))

marks = sorted({max(1, int(round(10 ** (e / 57)))) for e in range(0, 57 * 7 + 1)})
marks = [m for m in marks if m <= N]
mi = 0
a = [0] * (N + 1)
z = [0] * (N + 1)
gi = 0  # S[gi] is the largest element of S that is at most n
fi = 2  # fib[fi] is the largest Fibonacci number that is at most n
W = V = 0
out = []
for n in range(1, N + 1):
    while gi + 1 < len(S) and S[gi + 1] <= n:
        gi += 1
    while fib[fi + 1] <= n:
        fi += 1
    a[n] = 1 + a[n - S[gi]]
    z[n] = 1 + z[n - fib[fi]]
    W += a[n]
    V += z[n]
    if mi < len(marks) and n == marks[mi]:
        L = math.log(n) / math.log(phi)
        out.append((n, V / W, (W - n * L / 5) / n, (V - c * n * L / 5) / n))
        mi += 1
assert a[595] == 4
with open(sys.argv[2] if len(sys.argv) > 2 else "ratio.dat", "w") as f:
    for row in out:
        f.write("%d %.6f %.6f %.6f\n" % row)
print(out[-1])
