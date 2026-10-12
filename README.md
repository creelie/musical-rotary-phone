# The number of terms in greedy Fibonacci–Lucas representations

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).

Let a(n) be the number of terms in the greedy representation of n by the
Fibonacci and Lucas numbers 1, 2, 3, 4, 5, 7, 8, 11, 13, 18, ... (OEIS
[A214973](https://oeis.org/A214973)). This repository proves three conjectures
on this sequence:

- **Kimberling** ([A214981](https://oeis.org/A214981); C. Kimberling, Lucas
  representations of positive integers, J. Integer Seq. 23 (2020), Article
  20.9.5, Section 6): the limit of V(n)/W(n) exists and lies in (1.2, 1.4),
  where W(n) = a(1) + ... + a(n) and V(n) is the number of Zeckendorf
  summands of 1, ..., n ([A179180](https://oeis.org/A179180)).
- **Greathouse** (A214973, 2021): a(A049651(n)) = n, and this is the first
  occurrence of n, so A049651 gives the record positions of A214973.
- **Kurkov** (A214973, 2021): a(n) = A329320(A048679(n)) for n > 0.

## Results

**Theorem 1.4.** With T(x) = W(x-1), Z(x) = V(x-1), K(x) the index k with
F_k <= x < F_{k+1} and c = (5 - sqrt 5)/2, for every x >= 1

    |5T(x) - K(x) x| <= 19x,    |5Z(x) - c K(x) x| <= 13x.

Hence W(n) = (1/5) n log_phi n + O(n), |V(n)/W(n) - c| <= 51/(K(n+1) - 19)
when K(n+1) > 19, and V(n)/W(n) -> (5 - sqrt 5)/2 = 1.38196..., which lies in
(1.2, 1.4).

**Theorem 1.5.** For every j >= 1, a((F_{3j+1} - 1)/2) = j and a(m) < j for
every m < (F_{3j+1} - 1)/2.

**Theorem 1.6.** For every n >= 0, a(n) = A329320(A048679(n)). Equivalently,
if the Zeckendorf indices of n form maximal chains k, k-2, k-4, ... of lengths
l_1, ..., l_t, then a(n) = ceil(l_1/2) + ... + ceil(l_t/2).

The greedy algorithm over the Fibonacci and Lucas numbers is the Zeckendorf
algorithm in which a leading summand F_k followed by F_{k-2} is merged into
the Lucas number L_{k-1} = F_k + F_{k-2}. The bounds of Theorem 1.4 come from
the recursion e_{k+1} = e_k + e_{k-2} + e_{k-3} for e_k = 5T(F_k) - k F_k and
the exact value 5Z(F_k) = k L_{k-1} - 2F_k.

## Contents

| Path | Contents |
|---|---|
| `paper/` | LaTeX source (`main.tex`, Taylor & Francis `interact` class from the Fibonacci Quarterly template) and the compiled `main.pdf` |
| `verification/lean/` | Lean 4 + Mathlib formalization (6 files, 1460 lines); `FibLucas/Defs.lean` holds the definitions, `Limit.lean`, `Records.lean` and `Kurkov.lean` the theorems |
| `verification/c/` | `kimberling.c`: Theorems 1.4 and 1.5 for n <= 10^8, the second bound in exact integer arithmetic |
| `verification/cpp/` | `kurkov.cpp`: Theorem 1.6 and the pairing lemma for n <= 10^8 |
| `verification/python/` | `verify_fiblucas.py`: the three theorems from the OEIS definitions for n <= 10^6, and the OEIS terms |
| `verification/julia/` | `verify_lemmas.jl`: every lemma of the proofs, in BigInt arithmetic where the statement is about all k |
| `verification/shell/` | `check_small.sh`: Bash integer arithmetic only, n <= 3000 and the records up to 8855 |
| `scripts/run_all.sh` | runs the Lean build, the axiom check and all programs |
| `scripts/build_paper.sh` | builds the files in `dist/` |
| `journal/JOURNAL.md` | target journal, format rules and AI policy |
| `dist/` | the paper PDF, the LaTeX source zip, the arXiv tarball and `MasterKimberlingFibonacciLucasZip.zip`, which holds every file of the repository |

## Lean statements

```lean
theorem T_bound : ∀ x : ℕ, |5 * (T x : ℤ) - greatestFib x * x| ≤ 19 * x
theorem Z_bound : ∀ x : ℕ, |5 * (Z x : ℝ) - c * greatestFib x * x| ≤ 13 * x

theorem tendsto_ratio :
    Tendsto (fun n => (a179180 n : ℝ) / a214981 n) atTop (𝓝 ((5 - √5) / 2))

theorem kimberling_conjecture :
    ∃ L : ℝ, Tendsto (fun n => (a179180 n : ℝ) / a214981 n) atTop (𝓝 L) ∧
      6 / 5 < L ∧ L < 7 / 5

theorem greathouse_conjecture (n : ℕ) :
    a214973 (a049651 n) = n ∧ ∀ m < a049651 n, a214973 m < n

theorem first_occurrence (n : ℕ) (_hn : 0 < n) :
    a214973 (a049651 n) = n ∧ ∀ m, 1 ≤ m → m < a049651 n → a214973 m ≠ n

theorem kurkov_formula (n : ℕ) : a214973 n = a329320 (a048679 n)
theorem kurkov_conjecture (n : ℕ) (_hn : 0 < n) : a214973 n = a329320 (a048679 n)
```

The sequences are defined from their OEIS names: `a214973` by the greedy
recursion over the positive Fibonacci and Lucas numbers, `a007895 n` as the
length of Mathlib's Zeckendorf representation, `a214981` and `a179180` as sums
over 1 <= i <= n, `a049651 n = (fib (3n+1) - 1)/2`, `a048679` by the rewrite
0 -> 0, 01 -> 1 on the binary digits of `a003714 n`, `a035263 n` as the parity
of the 2-adic valuation of 2n, and `a329320` by its defining sum.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each of
the eight theorems above (`verification/lean/Axioms.lean`); there is no
`sorry`, `admit`, `native_decide` or added axiom. The asymptotic formula with
log_phi n is proved in the paper and not formalized; the limit and the bounds
are.

## Running the checks

Requirements: elan (Lean 4.34.1, fetched from `verification/lean/lean-toolchain`),
python3, julia, a C compiler and a C++17 compiler.

    scripts/run_all.sh          # Lean build (with the Mathlib cache), axiom check, all programs
    LEAN=0 scripts/run_all.sh   # programs only

To build the paper and the release files: `scripts/build_paper.sh`.

## Archive

Zenodo, all versions: [10.5281/zenodo.23315122](https://doi.org/10.5281/zenodo.23315122);
release v1.0.0: [10.5281/zenodo.23315123](https://doi.org/10.5281/zenodo.23315123).

## License

MIT, see `LICENSE`.
