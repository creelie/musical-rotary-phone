**The number of terms in greedy Fibonacci–Lucas representations**, by Deep Bhattacharjee.

Let a(n) be the number of terms in the greedy representation of n by the Fibonacci and Lucas numbers ([A214973](https://oeis.org/A214973)). The paper proves three conjectures on this sequence:

- **Kimberling** ([A214981](https://oeis.org/A214981); J. Integer Seq. 23 (2020), Article 20.9.5): the limit of V(n)/W(n) exists and lies in (1.2, 1.4), where W(n) = a(1) + ⋯ + a(n) and V(n) counts the Zeckendorf summands of 1, …, n. The limit is (5 − √5)/2 = 1.38196…, and W(n) = (1/5) n log_φ n + O(n).
- **Greathouse** (A214973, 2021): n first occurs in A214973 at A049651(n) = (F_{3n+1} − 1)/2.
- **Kurkov** (A214973, 2021): a(n) = A329320(A048679(n)) for n > 0.

| Step | Content |
|---|---|
| Lemmas 2.1–2.2 | S ∩ [F_k, F_{k+1}) = {F_k, L_{k−1}}; the greedy algorithm is the Zeckendorf algorithm with F_k + F_{k−2} merged into L_{k−1} |
| Lemmas 3.1–3.3 | e_k = 5T(F_k) − kF_k satisfies e_{k+1} = e_k + e_{k−2} + e_{k−3} and \|e_k\| ≤ 2F_k; 5Z(F_k) = k L_{k−1} − 2F_k; a gap lemma |
| Propositions 3.4–3.5 | \|5T(x) − K(x)x\| ≤ 19x and \|5Z(x) − cK(x)x\| ≤ 13x |
| Theorem 1.4 | the limit (5 − √5)/2, with \|V(n)/W(n) − c\| ≤ 51/(K(n+1) − 19) |
| Theorem 1.5 | the records of A214973 |
| Theorem 1.6 | Kurkov's formula, via a(n) = Σ ⌈ℓ_i/2⌉ over the chains of Zeckendorf indices |

The proofs are by hand and formalized in Lean 4 with Mathlib: the eight main theorems, including `kimberling_conjecture`, `greathouse_conjecture` and `kurkov_conjecture`, depend only on the axioms propext, Classical.choice and Quot.sound. Independent checks: C and C++ (n ≤ 10^8), Python (from the OEIS definitions, n ≤ 10^6), Julia (every lemma of the proofs) and Bash.

Files:
- `kimberling-fibonacci-lucas.pdf`: the paper
- `kimberling-fibonacci-lucas-tex.zip`: LaTeX source (`main.tex`, `interact.cls`)
- `kimberling-fibonacci-lucas-arxiv.tar.gz`: the same source, ready for arXiv
- `MasterKimberlingFibonacciLucasZip.zip`: every file of the repository with the three files above

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.

Zenodo, all versions: [10.5281/zenodo.23315122](https://doi.org/10.5281/zenodo.23315122); release v1.0.0: [10.5281/zenodo.23315123](https://doi.org/10.5281/zenodo.23315123).
