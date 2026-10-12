import FibLucas.Greedy

/-!
# Greathouse's conjecture on the records of A214973

`a214973 (a049651 n) = n`, and `a214973 m < n` for every `m < a049651 n`. Hence `a049651 n` is the
first occurrence of `n` in A214973, and A049651 (without its initial term) is the records
transform of A214973.
-/

open Nat

namespace FibLucas

/-- `R j = F 2 + F 5 + ... + F (3j - 1)`. -/
def R : ℕ → ℕ
  | 0 => 0
  | j + 1 => R j + fib (3 * j + 2)

lemma R_succ (j : ℕ) : R (j + 1) = R j + fib (3 * j + 2) := rfl

lemma two_mul_R_add_one : ∀ j, 2 * R j + 1 = fib (3 * j + 1)
  | 0 => rfl
  | j + 1 => by
      have ih := two_mul_R_add_one j
      have h4 : fib (3 * j + 4) = fib (3 * j + 2) + fib (3 * j + 3) := fib_add_two
      have h3 : fib (3 * j + 3) = fib (3 * j + 1) + fib (3 * j + 2) := fib_add_two
      rw [R_succ, show 3 * (j + 1) + 1 = 3 * j + 4 by ring]
      omega

lemma a049651_eq_R (j : ℕ) : a049651 j = R j := by
  unfold a049651; rw [← two_mul_R_add_one]; omega

lemma fib_le_R (t : ℕ) : fib (3 * t + 2) ≤ R (t + 1) := by rw [R_succ]; omega

lemma R_lt_fib (t : ℕ) : R (t + 1) < fib (3 * t + 3) := by
  have h := two_mul_R_add_one (t + 1)
  rw [show 3 * (t + 1) + 1 = (3 * t + 2) + 2 by ring, fib_add_two,
    show 3 * t + 2 + 1 = 3 * t + 3 by ring] at h
  have : fib (3 * t + 2) ≤ fib (3 * t + 3) := fib_le_fib_succ
  omega

/-- If `a214973 m ≥ j` then `m ≥ R j`. -/
theorem R_le_of_le_a214973 : ∀ m j, j ≤ a214973 m → R j ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro j hj
  rcases j with _ | i
  · simp [R]
  have hR1 : R 1 = 1 := rfl
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m
    · rw [a214973_zero] at hj; omega
    · rw [a214973_one] at hj
      obtain rfl : i = 0 := by omega
      rw [hR1]
    · rw [a214973_two] at hj
      obtain rfl : i = 0 := by omega
      rw [hR1]; omega
  have hk4 : 4 ≤ greatestFib m := le_greatestFib.2 (by have : fib 4 = 3 := rfl; omega)
  obtain ⟨q, hq⟩ : ∃ q, greatestFib m = q + 4 := ⟨greatestFib m - 4, by omega⟩
  have hF : fib (q + 4) ≤ m := by have := fib_greatestFib_le m; rwa [hq] at this
  have hF' : m < fib (q + 5) := by have := lt_fib_greatestFib_add_one m; rwa [hq] at this
  have hL3 := lucas_three q
  rcases i with _ | t
  · rw [hR1]; omega
  -- `j = t + 2`, and `R (t + 2) = R (t + 1) + F (3t + 5)`
  have hRt : R (t + 1 + 1) = R (t + 1) + fib (3 * t + 5) := by
    rw [R_succ]; ring_nf
  rw [hRt]
  have hfR := fib_le_R t
  rcases lt_or_ge m (lucas (q + 3)) with hL | hL
  · rw [a214973_of_lt_lucas hF hL] at hj
    have hr : m - fib (q + 4) < fib (q + 2) := by omega
    have ihr := ih (m - fib (q + 4)) (by have := fib_pos.2 (show 0 < q + 4 by omega); omega)
      (t + 1) (by omega)
    have h1 : fib (3 * t + 2) < fib (q + 2) := by omega
    have h2 : 3 * t + 2 < q + 2 := (fib_lt_fib (by omega)).1 h1
    have h3 : fib (3 * t + 5) ≤ fib (q + 4) := fib_mono (by omega)
    omega
  · rw [a214973_of_lucas_le hL hF'] at hj
    have hr : m - lucas (q + 3) < fib (q + 1) := by
      have h5 : fib (q + 5) = fib (q + 3) + fib (q + 4) := fib_add_two
      have h3 : fib (q + 3) = fib (q + 1) + fib (q + 2) := fib_add_two
      omega
    have ihr := ih (m - lucas (q + 3)) (by have := lucas_pos (q + 3); omega) (t + 1) (by omega)
    have h1 : fib (3 * t + 2) < fib (q + 1) := by omega
    have h2 : 3 * t + 2 < q + 1 := (fib_lt_fib (by omega)).1 h1
    have h3 : fib (3 * t + 5) ≤ fib (q + 4) := fib_mono (by omega)
    omega

/-- `a214973 (R j) = j`. -/
theorem a214973_R : ∀ j, a214973 (R j) = j
  | 0 => a214973_zero
  | 1 => a214973_one
  | t + 2 => by
      have hRt : R (t + 2) = R (t + 1) + fib (3 * t + 5) := by
        rw [R_succ]; ring_nf
      have hlt := R_lt_fib t
      have hL3 := lucas_three (3 * t + 1)
      rw [show 3 * t + 1 + 2 = 3 * t + 3 by ring, show 3 * t + 1 + 4 = 3 * t + 5 by ring] at hL3
      have h1 : fib (3 * t + 1 + 4) ≤ R (t + 2) := by
        rw [hRt, show 3 * t + 1 + 4 = 3 * t + 5 by ring]; omega
      have h2 : R (t + 2) < lucas (3 * t + 1 + 3) := by
        rw [hRt, show 3 * t + 1 + 3 = 3 * t + 4 by ring]
        rw [show 3 * t + 1 + 3 = 3 * t + 4 by ring] at hL3
        omega
      rw [a214973_of_lt_lucas h1 h2, show 3 * t + 1 + 4 = 3 * t + 5 by ring, hRt,
        Nat.add_sub_cancel, a214973_R (t + 1)]
      ring

/-- **Greathouse's conjecture (A214973, 2021).** For `n > 0`, `a(A049651(n)) = n`, and every
earlier term of A214973 is smaller than `n`; in particular `A049651(n)` is the first occurrence
of `n` in A214973, and A049651 (apart from its initial term) is the records transform of
A214973. -/
theorem greathouse_conjecture (n : ℕ) :
    a214973 (a049651 n) = n ∧ ∀ m < a049651 n, a214973 m < n := by
  rw [a049651_eq_R]
  refine ⟨a214973_R n, fun m hm => ?_⟩
  by_contra h
  have := R_le_of_le_a214973 m n (not_lt.1 h)
  omega

/-- The first-occurrence form: for `n > 0` the term `n` of A214973 first appears at
position `A049651(n)`. -/
theorem first_occurrence (n : ℕ) (_hn : 0 < n) :
    a214973 (a049651 n) = n ∧ ∀ m, 1 ≤ m → m < a049651 n → a214973 m ≠ n := by
  obtain ⟨h1, h2⟩ := greathouse_conjecture n
  exact ⟨h1, fun m _ hm => (h2 m hm).ne⟩

end FibLucas
