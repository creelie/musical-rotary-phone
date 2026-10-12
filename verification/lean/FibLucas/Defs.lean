import Mathlib

/-!
# Definitions

The integer sequences of the paper, each defined literally from its OEIS name.

* `lucas` : the Lucas numbers, OEIS A000032.
* `InB` : membership in OEIS A116470, the Fibonacci and Lucas numbers
  `1, 2, 3, 4, 5, 7, 8, 11, 13, 18, 21, 29, ...`.
* `greedyTerm n` : the largest term of A116470 that is at most `n`.
* `a214973 n` : the number of terms in the greedy representation of `n` by A116470.
* `a214981 n` : partial sums of A214973 over `1, ..., n`.
* `a007895 n` : the number of terms in the Zeckendorf representation of `n`.
* `a179180 n` : partial sums of A007895 over `1, ..., n`.
* `a049651 n = (F(3n+1) - 1)/2`.
* `a003714`, `a048679`, `a035263`, `a329320` : the sequences of Kurkov's formula.
-/

open Nat

namespace FibLucas

/-- The Lucas numbers `L 0 = 2`, `L 1 = 1`, `L (n+2) = L (n+1) + L n` (OEIS A000032). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

@[simp] lemma lucas_zero : lucas 0 = 2 := rfl
@[simp] lemma lucas_one : lucas 1 = 1 := rfl
lemma lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

lemma lucas_pos : ∀ n, 0 < lucas n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by rw [lucas_add_two]; have := lucas_pos n; omega

lemma le_lucas : ∀ n, n ≤ lucas n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      rw [lucas_add_two]; have := le_lucas (n + 1); have := lucas_pos n; omega

/-- `InB s` says that `s` is a term of OEIS A116470: a positive Fibonacci number or a Lucas
number. -/
def InB (s : ℕ) : Prop := 0 < s ∧ ∃ k, fib k = s ∨ lucas k = s

lemma inB_iff_bounded (s : ℕ) :
    InB s ↔ 0 < s ∧ ∃ k < s + 2, fib k = s ∨ lucas k = s := by
  constructor
  · rintro ⟨hs, k, hk⟩
    refine ⟨hs, k, ?_, hk⟩
    rcases hk with hk | hk
    · have := le_fib_add_one k; omega
    · have := le_lucas k; omega
  · rintro ⟨hs, k, -, hk⟩
    exact ⟨hs, k, hk⟩

instance : DecidablePred InB := fun s =>
  decidable_of_iff _ (inB_iff_bounded s).symm

lemma inB_one : InB 1 := ⟨one_pos, 1, Or.inl fib_one⟩

/-- The greedy term of `n`: the largest term of A116470 that is at most `n` (`0` if `n = 0`). -/
def greedyTerm (n : ℕ) : ℕ := Nat.findGreatest InB n

lemma greedyTerm_le (n : ℕ) : greedyTerm n ≤ n := Nat.findGreatest_le n

lemma greedyTerm_pos {n : ℕ} (hn : 0 < n) : 0 < greedyTerm n :=
  Nat.findGreatest_pos.2 ⟨1, one_pos, hn, inB_one⟩

/-- OEIS A214973: the number of terms in the greedy representation of `n` using Fibonacci and
Lucas numbers. The greedy algorithm subtracts `greedyTerm n` and repeats until `0` is reached;
`a214973 0 = 0` counts the empty representation. -/
def a214973 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else 1 + a214973 (n - greedyTerm n)
termination_by n
decreasing_by exact Nat.sub_lt (Nat.pos_of_ne_zero h) (greedyTerm_pos (Nat.pos_of_ne_zero h))

lemma a214973_zero : a214973 0 = 0 := by rw [a214973]; simp

lemma a214973_of_pos {n : ℕ} (hn : 0 < n) : a214973 n = 1 + a214973 (n - greedyTerm n) := by
  rw [a214973]; simp [hn.ne']

/-- OEIS A214981: the number of terms in the greedy Lucas-and-Fibonacci representations of
`1, 2, ..., n`; partial sums of A214973. -/
def a214981 (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, a214973 i

/-- OEIS A007895: the number of terms in the Zeckendorf representation of `n`. -/
def a007895 (n : ℕ) : ℕ := (zeckendorf n).length

/-- OEIS A179180: partial sums of A007895, the total number of summands in the Zeckendorf
representations of `1, 2, ..., n`. -/
def a179180 (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, a007895 i

/-- OEIS A049651: `a(n) = (F(3n+1) - 1)/2`. -/
def a049651 (n : ℕ) : ℕ := (fib (3 * n + 1) - 1) / 2

/-- OEIS A003714, the fibbinary numbers: if `n = F(i₁) + ... + F(iₖ)` is the Zeckendorf
representation of `n`, then `a(n) = 2^(i₁-2) + ... + 2^(iₖ-2)`. -/
def a003714 (n : ℕ) : ℕ := ((zeckendorf n).map fun i => 2 ^ (i - 2)).sum

/-- The rewrite `0 → 0`, `01 → 1` on a binary word, here given least significant digit first.
Reading the word from its most significant end, each `1` of a fibbinary number is preceded by a
`0` (a leading zero for the top digit); in least-significant-first order this `0` is the digit
after the `1`, and the pair becomes a single `1`. -/
def compress : List ℕ → List ℕ
  | [] => []
  | d :: rest => if d = 1 then 1 :: compress rest.tail else d :: compress rest
termination_by l => l.length
decreasing_by
  · simp only [List.length_cons, List.length_tail]; omega
  · simp only [List.length_cons]; omega

/-- OEIS A048679: compressed fibbinary numbers, the rewrite `0 → 0`, `01 → 1` applied to the
binary expansion of A003714. -/
def a048679 (n : ℕ) : ℕ := Nat.ofDigits 2 (compress (Nat.digits 2 (a003714 n)))

/-- OEIS A035263: the parity of the 2-adic valuation of `2n`. -/
def a035263 (n : ℕ) : ℕ := padicValNat 2 (2 * n) % 2

/-- OEIS A329320: `a(n) = Sum_{k=0..floor(log_2(n))} 1 - A035263(1 + floor(n/2^k))`. -/
def a329320 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (Nat.log 2 n + 1), (1 - a035263 (1 + n / 2 ^ k))

end FibLucas
