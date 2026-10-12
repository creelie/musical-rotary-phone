/* kimberling.c -- Theorems 1.4 and 1.5 for every n <= N (default 10^8).
 *
 * a(n) = A214973(n) is the number of terms of the greedy representation of n by
 * S = A116470 (the Fibonacci and Lucas numbers): a(0) = 0 and a(n) = 1 + a(n - s), where s is
 * the largest element of S with s <= n.  z(n) = A007895(n) is the same count for the Fibonacci
 * numbers alone (the greedy Fibonacci representation is Zeckendorf's).
 *
 * With T(x) = sum_{i<x} a(i), Z(x) = sum_{i<x} z(i), K(x) = max{k : F_k <= x} and
 * c = (5 - sqrt 5)/2 the program checks, for 1 <= x <= N + 1:
 *   |5T(x) - K(x) x| <= 19 x   and   |5Z(x) - c K(x) x| <= 13 x  (exact integer test);
 * for F_k <= N + 1:
 *   e_k = 5T(F_k) - k F_k satisfies |e_k| <= 2F_k and e_{k+1} = e_k + e_{k-2} + e_{k-3},
 *   5Z(F_k) = k(2F_k - F_{k-1}) - 2F_k;
 * that S meets [F_k, F_{k+1}) exactly in {F_k, L_{k-1}} for 4 <= k <= 60; and that the
 * records of a on [1, N] are at the positions A049651(j) = (F_{3j+1} - 1)/2, where the value
 * j first occurs.  Prints "ALL OK" if every check passes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef __int128 i128;

static int fails = 0;
#define CHECK(cond, ...) do { if (!(cond)) { fails++; if (fails < 20) { printf("FAIL: "); \
  printf(__VA_ARGS__); printf("\n"); } } } while (0)

static int cmp_u64(const void *p, const void *q) {
  uint64_t a = *(const uint64_t *)p, b = *(const uint64_t *)q;
  return a < b ? -1 : a > b;
}

/* |A + B sqrt5| <= R for B >= 0, R >= 0, exactly */
static int abs_le_sqrt5(i128 A, i128 B, i128 R) {
  i128 hi = R - A, lo = -R - A;
  int ok_hi = hi >= 0 && 5 * B * B <= hi * hi;
  int ok_lo = lo <= 0 || 5 * B * B >= lo * lo;
  return ok_hi && ok_lo;
}

int main(int argc, char **argv) {
  int64_t N = argc > 1 ? atoll(argv[1]) : 100000000LL;
  uint64_t F[92], L[92];
  F[0] = 0; F[1] = 1; L[0] = 2; L[1] = 1;
  for (int k = 2; k < 92; k++) { F[k] = F[k - 1] + F[k - 2]; L[k] = L[k - 1] + L[k - 2]; }

  /* S = A116470, sorted without repetitions */
  uint64_t S[184]; int ns = 0;
  for (int k = 1; k < 90; k++) { S[ns++] = F[k]; S[ns++] = L[k]; }
  S[ns++] = L[0];
  qsort(S, ns, sizeof S[0], cmp_u64);
  int m = 0;
  for (int i = 0; i < ns; i++) if (m == 0 || S[i] != S[m - 1]) S[m++] = S[i];
  ns = m;

  /* S meets [F_k, F_{k+1}) exactly in {F_k, L_{k-1}} for k >= 4 */
  for (int k = 4; k <= 60; k++) {
    int cnt = 0, okk = 1;
    for (int i = 0; i < ns; i++)
      if (S[i] >= F[k] && S[i] < F[k + 1]) { cnt++; if (S[i] != F[k] && S[i] != L[k - 1]) okk = 0; }
    CHECK(cnt == 2 && okk, "S on [F_%d, F_%d)", k, k + 1);
  }

  uint8_t *a = malloc(N + 1), *z = malloc(N + 1);
  if (!a || !z) { printf("out of memory\n"); return 2; }
  a[0] = z[0] = 0;
  int is = 0, iff = 2;            /* S[is] and F[iff] are the largest elements <= n */
  for (int64_t n = 1; n <= N; n++) {
    while (is + 1 < ns && S[is + 1] <= (uint64_t)n) is++;
    while (F[iff + 1] <= (uint64_t)n) iff++;
    a[n] = 1 + a[n - S[is]];
    z[n] = 1 + z[n - F[iff]];
  }

  /* bounds for 1 <= x <= N + 1 */
  int64_t T = 0, Z = 0;           /* T(x), Z(x) */
  int k = 1;                      /* K(x) */
  int64_t TF[92], ZF[92]; int kmax = 0;
  double worstT = 0, worstZ = 0;
  const double c = (5.0 - 2.23606797749978969641) / 2.0;
  for (int64_t x = 1; x <= N + 1; x++) {
    T += a[x - 1]; Z += z[x - 1];
    while (F[k + 1] <= (uint64_t)x) k++;
    if (F[k] == (uint64_t)x) { TF[k] = T; ZF[k] = Z; kmax = k; if (k == 2) { TF[1] = T; ZF[1] = Z; } }
    int64_t d = 5 * T - (int64_t)k * x;
    CHECK(d <= 19 * x && -d <= 19 * x, "T bound at x=%lld", (long long)x);
    /* 5Z - cKx = (10Z - 5Kx + Kx sqrt5)/2 */
    CHECK(abs_le_sqrt5((i128)10 * Z - (i128)5 * k * x, (i128)k * x, (i128)26 * x),
          "Z bound at x=%lld", (long long)x);
    double dt = (d < 0 ? -d : d) / (double)x, dz = (5.0 * Z - c * k * (double)x) / (double)x;
    if (dz < 0) dz = -dz;
    if (dt > worstT) worstT = dt;
    if (dz > worstZ) worstZ = dz;
  }
  printf("bounds hold for 1 <= x <= %lld: max |5T-Kx|/x = %.4f, max |5Z-cKx|/x = %.4f\n",
         (long long)(N + 1), worstT, worstZ);

  int64_t e[92];
  for (int j = 1; j <= kmax; j++) {
    e[j] = 5 * TF[j] - (int64_t)j * F[j];
    CHECK(e[j] <= 2 * (int64_t)F[j] && -e[j] <= 2 * (int64_t)F[j], "|e_%d| > 2F_%d", j, j);
    CHECK(5 * ZF[j] == (int64_t)j * (2 * (int64_t)F[j] - (int64_t)F[j - 1]) - 2 * (int64_t)F[j],
          "5Z(F_%d)", j);
    if (j >= 5) CHECK(e[j] == e[j - 1] + e[j - 3] + e[j - 4], "e recurrence at %d", j);
  }
  printf("e_k and 5Z(F_k) checked for k <= %d\n", kmax);

  /* records and first occurrences */
  int64_t first[64]; memset(first, 0, sizeof first);
  int best = 0, nrec = 0, recok = 1;
  for (int64_t n = 1; n <= N; n++) {
    if (!first[a[n]]) first[a[n]] = n;
    if (a[n] > best) {
      best = a[n]; nrec++;
      if ((uint64_t)n != (F[3 * best + 1] - 1) / 2 || best != nrec) recok = 0;
    }
  }
  CHECK(recok, "records differ from A049651");
  for (int j = 1; j <= best; j++)
    CHECK((uint64_t)first[j] == (F[3 * j + 1] - 1) / 2, "first occurrence of %d", j);
  CHECK((F[3 * (best + 1) + 1] - 1) / 2 > (uint64_t)N, "a record is missing");
  printf("records of A214973 on [1, %lld]: the values 1..%d, first at A049651(1..%d)\n",
         (long long)N, best, best);

  int64_t W = 0, V = 0;
  for (int64_t n = 1; n <= N; n++) {
    W += a[n]; V += z[n];
    if (n == 1000 || n == 1000000 || n == N)
      printf("V(%lld)/W(%lld) = %.6f\n", (long long)n, (long long)n, (double)V / W);
  }
  printf("(5 - sqrt 5)/2 = %.6f\n", c);

  free(a); free(z);
  if (fails) { printf("%d FAILURES\n", fails); return 1; }
  printf("ALL OK\n");
  return 0;
}
