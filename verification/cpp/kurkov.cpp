// kurkov.cpp -- Theorem 1.6, A214973(n) = A329320(A048679(n)), for 1 <= n <= N (default 10^8).
//
// The sequences are computed from definitions that do not use Zeckendorf representations:
//   A214973(n)  greedy count over S = A116470 (the Fibonacci and Lucas numbers):
//               a(0) = 0, a(n) = 1 + a(n - s) with s the largest element of S, s <= n;
//   A003714(n)  the n-th nonnegative integer (from n = 0) with no two adjacent ones in binary,
//               listed by a successor function;
//   A048679(n)  the rewrite 0 -> 0, 01 -> 1 applied to the binary word of A003714(n) with one
//               leading zero, read from the most significant digit;
//   A035263(n)  generated as the trajectory of 1 under the morphism 0 -> 11, 1 -> 10 (the name
//               of A035263) and compared with the parity of the 2-adic valuation of 2n;
//   A329320(y)  sum_{k=0}^{floor(log2 y)} (1 - A035263(1 + floor(y/2^k))).
// It also checks the pairing lemma of the paper: a(n) = W(Zeckendorf indices of n), where W counts a
// summand F_k followed by F_{k-2} once and every other summand once.
// Prints "ALL OK" if every check passes.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <string>

using u64 = std::uint64_t;
static int fails = 0;
static void check(bool c, const std::string& msg) {
  if (!c) { if (++fails < 20) std::printf("FAIL: %s\n", msg.c_str()); }
}

static int top_bit(u64 x) { return 63 - __builtin_clzll(x); }

// the least integer >= y with no two adjacent ones in binary
static u64 fibbinary_ceil(u64 y) {
  while (u64 p = y & (y >> 1)) {
    int i = top_bit(p);  // bits i + 1 and i of y are both one
    y = ((y >> i) + 1) << i;
  }
  return y;
}

static u64 compress(u64 x) {  // 0 -> 0, 01 -> 1 on 0x read from the top
  u64 out = 0;
  int j = x ? top_bit(x) + 1 : 0;  // position of the leading zero
  while (j >= 0) {
    bool bj = (x >> j) & 1, bnext = j >= 1 && ((x >> (j - 1)) & 1);
    if (bj) { std::printf("not fibbinary\n"); std::exit(2); }
    if (bnext) { out = 2 * out + 1; j -= 2; } else { out = 2 * out; j -= 1; }
  }
  return out;
}

static int a035263_val(u64 n) { return (1 + __builtin_ctzll(n)) & 1; }  // v_2(2n) mod 2

static int a329320(u64 y) {
  int top = y ? top_bit(y) : 0, s = 0;
  for (int k = 0; k <= top; k++) s += 1 - a035263_val(1 + (y >> k));
  return s;
}

int main(int argc, char** argv) {
  long long N = argc > 1 ? std::atoll(argv[1]) : 100000000LL;

  // A035263 from the morphism 0 -> 11, 1 -> 10, against the 2-adic formula
  std::vector<char> w{1};
  while (w.size() < (1u << 22)) {
    std::vector<char> v;
    v.reserve(2 * w.size());
    for (char c : w) { v.push_back(1); v.push_back(c ? 0 : 1); }
    w.swap(v);
  }
  bool morph_ok = true;
  for (std::size_t i = 0; i < w.size(); i++) morph_ok &= (w[i] == a035263_val(i + 1));
  check(morph_ok, "A035263: morphism and 2-adic formula differ");
  std::printf("A035263: morphism = parity of v_2(2n) for n <= %zu\n", w.size());

  u64 F[92], L[92];
  F[0] = 0; F[1] = 1; L[0] = 2; L[1] = 1;
  for (int k = 2; k < 92; k++) { F[k] = F[k - 1] + F[k - 2]; L[k] = L[k - 1] + L[k - 2]; }
  std::vector<u64> S;
  for (int k = 1; k < 90; k++) { S.push_back(F[k]); S.push_back(L[k]); }
  std::sort(S.begin(), S.end());
  S.erase(std::unique(S.begin(), S.end()), S.end());

  std::vector<std::uint8_t> a(N + 1, 0);
  std::size_t is = 0;
  for (long long n = 1; n <= N; n++) {
    while (is + 1 < S.size() && S[is + 1] <= (u64)n) is++;
    a[n] = 1 + a[n - S[is]];
  }

  // the first terms of A048679 (OEIS)
  const int A048679[] = {0, 1, 2, 4, 3, 8, 5, 6, 16, 9, 10, 12, 7, 32, 17, 18, 20, 11, 24, 13, 14,
                         64, 33, 34, 36, 19, 40, 21, 22, 48, 25, 26, 28, 15, 128, 65, 66, 68, 35};
  u64 x = 0;  // A003714(n)
  long long bad = 0, badW = 0;
  for (long long n = 0; n <= N; n++) {
    if (n > 0) x = fibbinary_ceil(x + 1);
    u64 c = compress(x);
    if (n < (long long)(sizeof A048679 / sizeof A048679[0])) check((long long)c == A048679[n], "A048679 term");
    if (n >= 1 && a[n] != a329320(c)) { if (bad++ < 5) std::printf("Kurkov fails at n=%lld\n", n); }
    // pairing lemma: a(n) = W(Zeckendorf indices)
    if (n >= 1) {
      int idx[64], m = 0;
      u64 r = n;
      int k = 91;
      while (r) { while (F[k] > r) k--; idx[m++] = k; r -= F[k]; }
      int Wn = 0;
      for (int i = 0; i < m;) {
        Wn++;
        if (i + 1 < m && idx[i + 1] + 2 == idx[i]) i += 2; else i += 1;
      }
      if (Wn != a[n]) badW++;
    }
  }
  check(bad == 0, "Kurkov's formula");
  check(badW == 0, "pairing lemma");
  std::printf("A214973(n) = A329320(A048679(n)) for 1 <= n <= %lld\n", N);
  std::printf("a(n) = W(zeckendorf(n)) for 1 <= n <= %lld\n", N);
  if (fails) { std::printf("%d FAILURES\n", fails); return 1; }
  std::printf("ALL OK\n");
  return 0;
}
