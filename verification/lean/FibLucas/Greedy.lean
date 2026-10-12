import FibLucas.Defs

/-!
# The greedy step

For `k ≥ 4` the interval `[F k, F (k+1))` contains exactly two terms of A116470, namely `F k`
and `L (k-1) = F (k-2) + F k`. The greedy algorithm therefore subtracts `F k` on
`[F k, L (k-1))` and `L (k-1)` on `[L (k-1), F (k+1))`. We write `k = m + 4`.
-/

open Nat

namespace FibLucas

lemma lucas_succ_eq (n : ℕ) : lucas (n + 1) = fib n + fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | n + 2, ih =>
      rw [show n + 2 + 1 = (n + 1) + 2 by ring, lucas_add_two, ih (n + 1) (by omega),
        ih n (by omega)]
      simp only [fib_add_two]
      ring

lemma lucas_mono_succ (a d : ℕ) : lucas (a + 1) ≤ lucas (a + 1 + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc lucas (a + 1) ≤ lucas (a + 1 + d) := ih
      _ ≤ lucas (a + 1 + (d + 1)) := by
        rw [show a + 1 + (d + 1) = (a + d) + 2 by ring, lucas_add_two,
          show a + d + 1 = a + 1 + d by ring]
        omega

lemma lucas_le_lucas {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : lucas a ≤ lucas b := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - (a + 1), by omega⟩
  exact lucas_mono_succ a d

lemma fib_le_fib {a b : ℕ} (h : a ≤ b) : fib a ≤ fib b := fib_mono h

/-- `F (m+4) < L (m+3) < F (m+5)` and `L (m+3) = F (m+2) + F (m+4)`. -/
lemma lucas_three (m : ℕ) : lucas (m + 3) = fib (m + 2) + fib (m + 4) := lucas_succ_eq (m + 2)

lemma fib_lt_lucas (m : ℕ) : fib (m + 4) < lucas (m + 3) := by
  rw [lucas_three]; have := fib_pos.2 (show 0 < m + 2 by omega); omega

lemma lucas_lt_fib (m : ℕ) : lucas (m + 3) < fib (m + 5) := by
  have h5 : fib (m + 5) = fib (m + 3) + fib (m + 4) := fib_add_two
  have h1 : fib (m + 2) < fib (m + 3) := fib_lt_fib_succ (by omega)
  rw [lucas_three]
  omega

/-- No term of A116470 lies strictly between `F (m+4)` and `L (m+3)`. -/
lemma not_inB_of_fib_lt {m s : ℕ} (h1 : fib (m + 4) < s) (h2 : s < lucas (m + 3)) :
    ¬ InB s := by
  rintro ⟨-, j, hj | hj⟩
  · subst hj
    rcases le_or_gt j (m + 4) with hjm | hjm
    · exact absurd (fib_mono hjm) (not_le.2 h1)
    · have : fib (m + 5) ≤ fib j := fib_mono (by omega)
      have := lucas_lt_fib m
      omega
  · subst hj
    rcases le_or_gt j (m + 2) with hjm | hjm
    · -- `L j ≤ F (m+4)`
      have hle : lucas j ≤ fib (m + 4) := by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · have : fib 4 ≤ fib (m + 4) := fib_mono (by omega)
          simp only [lucas_zero]
          have h4 : fib 4 = 3 := rfl
          omega
        · have h := lucas_le_lucas hj0 hjm
          rw [lucas_succ_eq (m + 1)] at h
          have : fib (m + 1) ≤ fib (m + 2) := fib_le_fib_succ
          rw [show m + 4 = (m + 2) + 2 by ring, fib_add_two, show m + 2 + 1 = m + 3 by ring]
          rw [show m + 1 + 2 = m + 3 by ring] at h
          omega
      omega
    · have := lucas_le_lucas (show 1 ≤ m + 3 by omega) (show m + 3 ≤ j by omega)
      omega

/-- No term of A116470 lies strictly between `L (m+3)` and `F (m+5)`. -/
lemma not_inB_of_lucas_lt {m s : ℕ} (h1 : lucas (m + 3) < s) (h2 : s < fib (m + 5)) :
    ¬ InB s := by
  rintro ⟨-, j, hj | hj⟩
  · subst hj
    rcases le_or_gt j (m + 4) with hjm | hjm
    · have := fib_mono hjm
      have := fib_lt_lucas m
      omega
    · have : fib (m + 5) ≤ fib j := fib_mono (by omega)
      omega
  · subst hj
    rcases le_or_gt j (m + 3) with hjm | hjm
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have : fib 4 ≤ fib (m + 4) := fib_mono (by omega)
        have := fib_lt_lucas m
        have h4 : fib 4 = 3 := rfl
        simp only [lucas_zero] at h1
        omega
      · have := lucas_le_lucas hj0 hjm
        omega
    · have h := lucas_le_lucas (show 1 ≤ m + 4 by omega) (show m + 4 ≤ j by omega)
      rw [lucas_succ_eq (m + 3)] at h
      rw [show m + 3 + 2 = m + 5 by ring] at h
      omega

lemma inB_fib {k : ℕ} (hk : 0 < k) : InB (fib k) := ⟨fib_pos.2 hk, k, Or.inl rfl⟩

lemma inB_lucas (k : ℕ) : InB (lucas k) := ⟨lucas_pos k, k, Or.inr rfl⟩

/-- On `[F (m+4), L (m+3))` the greedy term is `F (m+4)`. -/
lemma greedyTerm_of_lt_lucas {m n : ℕ} (h1 : fib (m + 4) ≤ n) (h2 : n < lucas (m + 3)) :
    greedyTerm n = fib (m + 4) := by
  unfold greedyTerm
  rw [Nat.findGreatest_eq_iff]
  refine ⟨h1, fun _ => inB_fib (by omega), fun s hs hsn => not_inB_of_fib_lt hs (by omega)⟩

/-- On `[L (m+3), F (m+5))` the greedy term is `L (m+3)`. -/
lemma greedyTerm_of_lucas_le {m n : ℕ} (h1 : lucas (m + 3) ≤ n) (h2 : n < fib (m + 5)) :
    greedyTerm n = lucas (m + 3) := by
  unfold greedyTerm
  rw [Nat.findGreatest_eq_iff]
  refine ⟨h1, fun _ => inB_lucas _, fun s hs hsn => not_inB_of_lucas_lt hs (by omega)⟩

lemma greedyTerm_one : greedyTerm 1 = 1 := by
  unfold greedyTerm
  rw [Nat.findGreatest_eq_iff]
  exact ⟨le_rfl, fun _ => inB_one, fun s hs hsn => by omega⟩

lemma greedyTerm_two : greedyTerm 2 = 2 := by
  unfold greedyTerm
  rw [Nat.findGreatest_eq_iff]
  exact ⟨le_rfl, fun _ => inB_fib (k := 3) (by omega), fun s hs hsn => by omega⟩

/-- The greedy recursion on `[F (m+4), L (m+3))`. -/
lemma a214973_of_lt_lucas {m n : ℕ} (h1 : fib (m + 4) ≤ n) (h2 : n < lucas (m + 3)) :
    a214973 n = 1 + a214973 (n - fib (m + 4)) := by
  have hn : 0 < n := lt_of_lt_of_le (fib_pos.2 (by omega)) h1
  rw [a214973_of_pos hn, greedyTerm_of_lt_lucas h1 h2]

/-- The greedy recursion on `[L (m+3), F (m+5))`. -/
lemma a214973_of_lucas_le {m n : ℕ} (h1 : lucas (m + 3) ≤ n) (h2 : n < fib (m + 5)) :
    a214973 n = 1 + a214973 (n - lucas (m + 3)) := by
  have hn : 0 < n := lt_of_lt_of_le (lucas_pos _) h1
  rw [a214973_of_pos hn, greedyTerm_of_lucas_le h1 h2]

lemma a214973_one : a214973 1 = 1 := by
  rw [a214973_of_pos one_pos, greedyTerm_one, Nat.sub_self, a214973_zero]

lemma a214973_two : a214973 2 = 1 := by
  rw [a214973_of_pos two_pos, greedyTerm_two, Nat.sub_self, a214973_zero]

/-- The Zeckendorf recursion: on `[F k, F (k+1))` with `k ≥ 2`, the leading term is `F k`. -/
lemma a007895_of_mem {k n : ℕ} (hk : 2 ≤ k) (h1 : fib k ≤ n) (h2 : n < fib (k + 1)) :
    a007895 n = 1 + a007895 (n - fib k) := by
  have hn : 0 < n := lt_of_lt_of_le (fib_pos.2 (by omega)) h1
  have hg : greatestFib n = k := by
    apply le_antisymm
    · have := (greatestFib_lt (m := n) (n := k + 1)).2 h2; omega
    · exact le_greatestFib.2 h1
  unfold a007895
  rw [zeckendorf_of_pos hn, hg, List.length_cons]
  ring

lemma a007895_zero : a007895 0 = 0 := by simp [a007895]

/-! ## Shifted blocks of a summatory function -/

/-- If `f i = 1 + f (i - a)` on `[a, b)`, then for `a ≤ x ≤ b` the sum of `f` below `x` is the sum
below `a`, plus `x - a`, plus the sum below `x - a`. -/
lemma sum_range_shift (f : ℕ → ℕ) {a b x : ℕ} (hab : ∀ i, a ≤ i → i < b → f i = 1 + f (i - a))
    (hax : a ≤ x) (hxb : x ≤ b) :
    ∑ i ∈ Finset.range x, f i =
      ∑ i ∈ Finset.range a, f i + (x - a) + ∑ i ∈ Finset.range (x - a), f i := by
  obtain ⟨y, rfl⟩ : ∃ y, x = a + y := ⟨x - a, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  have : ∑ j ∈ Finset.range y, f (a + j) = ∑ j ∈ Finset.range y, (1 + f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hab (a + j) (by omega) (by omega), Nat.add_sub_cancel_left]
  rw [this, Finset.sum_add_distrib]
  simp
  ring

end FibLucas
