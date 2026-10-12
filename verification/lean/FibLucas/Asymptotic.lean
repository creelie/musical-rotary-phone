import FibLucas.Greedy

/-!
# The two summatory functions

`T x = ∑_{i<x} a214973 i` and `Z x = ∑_{i<x} a007895 i`. With `K x = greatestFib x` (the `k` with
`F k ≤ x < F (k+1)`) we prove

* `|5 T x - K x · x| ≤ 19 x`,
* `|5 Z x - (2 + ψ) K x · x| ≤ 13 x`, where `ψ = (1 - √5)/2`,

and deduce that `Z x / T x → 2 + ψ = (5 - √5)/2`.
-/

open Nat Real Finset Filter Topology

namespace FibLucas

/-- `T x = ∑_{i<x} a214973 i`. -/
def T (x : ℕ) : ℕ := ∑ i ∈ range x, a214973 i

/-- `Z x = ∑_{i<x} a007895 i`. -/
def Z (x : ℕ) : ℕ := ∑ i ∈ range x, a007895 i

/-! ## Block decompositions -/

lemma T_of_le_lucas {m x : ℕ} (h1 : fib (m + 4) ≤ x) (h2 : x ≤ lucas (m + 3)) :
    T x = T (fib (m + 4)) + (x - fib (m + 4)) + T (x - fib (m + 4)) :=
  sum_range_shift a214973 (b := lucas (m + 3)) (fun _ hi hi' => a214973_of_lt_lucas hi hi') h1 h2

lemma T_of_lucas_le {m x : ℕ} (h1 : lucas (m + 3) ≤ x) (h2 : x ≤ fib (m + 5)) :
    T x = T (lucas (m + 3)) + (x - lucas (m + 3)) + T (x - lucas (m + 3)) :=
  sum_range_shift a214973 (b := fib (m + 5)) (fun _ hi hi' => a214973_of_lucas_le hi hi') h1 h2

lemma lucas_sub_fib (m : ℕ) : lucas (m + 3) - fib (m + 4) = fib (m + 2) := by
  rw [lucas_three]; omega

lemma fib_sub_lucas (m : ℕ) : fib (m + 5) - lucas (m + 3) = fib (m + 1) := by
  have h5 : fib (m + 5) = fib (m + 3) + fib (m + 4) := fib_add_two
  have h3 : fib (m + 3) = fib (m + 1) + fib (m + 2) := fib_add_two
  rw [lucas_three]; omega

lemma T_lucas (m : ℕ) : T (lucas (m + 3)) = T (fib (m + 4)) + fib (m + 2) + T (fib (m + 2)) := by
  rw [T_of_le_lucas (fib_lt_lucas m).le le_rfl, lucas_sub_fib]

lemma T_fib_rec (m : ℕ) :
    T (fib (m + 5)) = T (lucas (m + 3)) + fib (m + 1) + T (fib (m + 1)) := by
  rw [T_of_lucas_le (lucas_lt_fib m).le le_rfl, fib_sub_lucas]

lemma Z_of_mem {k x : ℕ} (hk : 2 ≤ k) (h1 : fib k ≤ x) (h2 : x ≤ fib (k + 1)) :
    Z x = Z (fib k) + (x - fib k) + Z (x - fib k) :=
  sum_range_shift a007895 (b := fib (k + 1)) (fun _ hi hi' => a007895_of_mem hk hi hi') h1 h2

lemma Z_fib_rec (m : ℕ) :
    Z (fib (m + 3)) = Z (fib (m + 2)) + fib (m + 1) + Z (fib (m + 1)) := by
  have h3 : fib (m + 3) = fib (m + 1) + fib (m + 2) := fib_add_two
  have h := Z_of_mem (k := m + 2) (x := fib (m + 3)) (by omega) (fib_mono (by omega)) le_rfl
  rw [show fib (m + 3) - fib (m + 2) = fib (m + 1) by omega] at h
  exact h

/-! ## Values at Fibonacci numbers -/

lemma T_one : T 1 = 0 := by simp [T, a214973_zero]
lemma T_two : T 2 = 1 := by simp [T, Finset.sum_range_succ, a214973_zero, a214973_one]
lemma T_three : T 3 = 2 := by
  simp [T, Finset.sum_range_succ, a214973_zero, a214973_one, a214973_two]

/-- `e j = 5 T (F j) - j F j`. -/
def e (j : ℕ) : ℤ := 5 * (T (fib j) : ℤ) - j * fib j

lemma e_rec (m : ℕ) : e (m + 5) = e (m + 4) + e (m + 2) + e (m + 1) := by
  unfold e
  rw [T_fib_rec, T_lucas]
  have h5 : (fib (m + 5) : ℤ) = fib (m + 3) + fib (m + 4) := by exact_mod_cast fib_add_two
  have h4 : (fib (m + 4) : ℤ) = fib (m + 2) + fib (m + 3) := by exact_mod_cast fib_add_two
  have h3 : (fib (m + 3) : ℤ) = fib (m + 1) + fib (m + 2) := by exact_mod_cast fib_add_two
  push_cast
  linear_combination (-(↑m : ℤ) - 5) * h5 - h4 - ((↑m : ℤ) + 6) * h3

lemma e_bound : ∀ j, 1 ≤ j → |e j| ≤ 2 * fib j
  | 0, h => absurd h (by omega)
  | 1, _ => by simp [e, T_one]
  | 2, _ => by simp [e, T_one]
  | 3, _ => by
      have : fib 3 = 2 := rfl
      simp [e, this, T_two]
  | 4, _ => by
      have : fib 4 = 3 := rfl
      simp [e, this, T_three]
  | m + 5, _ => by
      rw [e_rec]
      have h1 := e_bound (m + 4) (by omega)
      have h2 := e_bound (m + 2) (by omega)
      have h3 := e_bound (m + 1) (by omega)
      have h5 : (fib (m + 5) : ℤ) = fib (m + 3) + fib (m + 4) := by exact_mod_cast fib_add_two
      have h3' : (fib (m + 3) : ℤ) = fib (m + 1) + fib (m + 2) := by exact_mod_cast fib_add_two
      calc |e (m + 4) + e (m + 2) + e (m + 1)|
          ≤ |e (m + 4)| + |e (m + 2)| + |e (m + 1)| := abs_add_three _ _ _
        _ ≤ 2 * fib (m + 4) + 2 * fib (m + 2) + 2 * fib (m + 1) := by linarith
        _ = 2 * fib (m + 5) := by rw [h5, h3']; ring

lemma Z_one : Z 1 = 0 := by simp [Z, a007895_zero]

/-- `5 Z (F (m+1)) = (m+1)(2 F (m+1) - F m) - 2 F (m+1)`. -/
lemma Z_fib : ∀ m : ℕ,
    5 * (Z (fib (m + 1)) : ℤ) = (m + 1) * (2 * fib (m + 1) - fib m) - 2 * fib (m + 1)
  | 0 => by simp [Z_one]
  | 1 => by
      have : fib 2 = 1 := rfl
      simp [this, Z_one]
  | m + 2 => by
      have hr := Z_fib_rec m
      have ih1 := Z_fib (m + 1)
      have ih0 := Z_fib m
      rw [show m + 2 + 1 = m + 3 by ring, hr]
      rw [show m + 1 + 1 = m + 2 by ring] at ih1
      have h3 : (fib (m + 3) : ℤ) = fib (m + 1) + fib (m + 2) := by exact_mod_cast fib_add_two
      have h2 : (fib (m + 2) : ℤ) = fib m + fib (m + 1) := by exact_mod_cast fib_add_two
      push_cast at ih1 ih0 ⊢
      linear_combination ih1 + ih0 - (2 * (↑m : ℤ) + 4) * h3 + ((↑m : ℤ) + 1) * h2

/-! ## Auxiliary inequalities -/

lemma succ_mul_fib_le (n d : ℕ) : (d + 1) * fib (n + 1) ≤ 2 * fib (n + d + 1) := by
  have h1 : fib (n + d + 1) = fib n * fib d + fib (n + 1) * fib (d + 1) := fib_add n d
  have h2 : d + 1 ≤ fib (d + 1) + 1 := le_fib_add_one (d + 1)
  have h3 : 0 < fib (d + 1) := fib_pos.2 (by omega)
  have h4 : d + 1 ≤ 2 * fib (d + 1) := by omega
  calc (d + 1) * fib (n + 1) ≤ 2 * fib (d + 1) * fib (n + 1) := Nat.mul_le_mul_right _ h4
    _ = 2 * (fib (n + 1) * fib (d + 1)) := by ring
    _ ≤ 2 * fib (n + d + 1) := by rw [h1]; omega

lemma le_two_mul_fib {k : ℕ} (hk : 1 ≤ k) : k ≤ 2 * fib k := by
  have := le_fib_add_one k
  have := fib_pos.2 (show 0 < k by omega)
  omega

/-- If `greatestFib r ≤ k` then `(k - greatestFib r) r ≤ 2 F k`. -/
lemma gap_mul_le {r k : ℕ} (h : greatestFib r ≤ k) :
    ((k : ℤ) - greatestFib r) * r ≤ 2 * fib k := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  set j := greatestFib r with hj
  rcases Nat.eq_or_lt_of_le h with hjk | hjk
  · rw [hjk]; simp
  have hrj : r < fib (j + 1) := lt_fib_greatestFib_add_one r
  have hkey := succ_mul_fib_le j (k - j - 1)
  rw [show j + (k - j - 1) + 1 = k by omega, show k - j - 1 + 1 = k - j by omega] at hkey
  have hcast : ((k : ℤ) - j) = ((k - j : ℕ) : ℤ) := by push_cast [hjk.le]; ring
  rw [hcast]
  have : (k - j) * r ≤ (k - j) * fib (j + 1) := Nat.mul_le_mul_left _ hrj.le
  exact_mod_cast this.trans hkey

lemma gap_nonneg {r k : ℕ} (h : greatestFib r ≤ k) : 0 ≤ ((k : ℤ) - greatestFib r) * r := by
  apply mul_nonneg _ (by positivity)
  have : (greatestFib r : ℤ) ≤ k := by exact_mod_cast h
  linarith

/-! ## The bound for `T` -/

theorem T_bound : ∀ x : ℕ, |5 * (T x : ℤ) - greatestFib x * x| ≤ 19 * x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  rcases Nat.lt_or_ge x 3 with hx | hx
  · interval_cases x
    · simp [T]
    · have : greatestFib 1 = 2 := by
        rw [show (1 : ℕ) = fib 2 from rfl, greatestFib_fib (by omega)]
      simp [T_one, this]
    · have : greatestFib 2 = 3 := by
        rw [show (2 : ℕ) = fib 3 from rfl, greatestFib_fib (by omega)]
      rw [T_two, this]; norm_num
  -- `k = greatestFib x ≥ 4`
  have hk4 : 4 ≤ greatestFib x := le_greatestFib.2 (by have : fib 4 = 3 := rfl; omega)
  obtain ⟨m, hm⟩ : ∃ m, greatestFib x = m + 4 := ⟨greatestFib x - 4, by omega⟩
  have hF : fib (m + 4) ≤ x := by have := fib_greatestFib_le x; rwa [hm] at this
  have hF' : x < fib (m + 5) := by have := lt_fib_greatestFib_add_one x; rwa [hm] at this
  have he4 := e_bound (m + 4) (by omega)
  have he2 := e_bound (m + 2) (by omega)
  have hL := lucas_three m
  have h4 : fib (m + 4) = fib (m + 2) + fib (m + 3) := fib_add_two
  have h23 : fib (m + 2) < fib (m + 3) := fib_lt_fib_succ (by omega)
  rw [hm]
  rcases le_or_gt x (lucas (m + 3)) with hxL | hxL
  · -- the greedy term is `F (m+4)`
    set r := x - fib (m + 4) with hr
    have hT := T_of_le_lucas hF hxL
    rw [← hr] at hT
    have hrx : r < x := by have := fib_pos.2 (show 0 < m + 4 by omega); omega
    have hrF : r ≤ fib (m + 2) := by omega
    have hKr : greatestFib r ≤ m + 4 := by
      have : greatestFib r < m + 3 := greatestFib_lt.2 (by omega)
      omega
    have ihr := ih r hrx
    have hg := gap_mul_le hKr
    have hg0 := gap_nonneg hKr
    have hxr : (x : ℤ) = fib (m + 4) + r := by
      have : x = fib (m + 4) + r := by omega
      exact_mod_cast this
    have hid : 5 * (T x : ℤ) - ((m + 4 : ℕ) : ℤ) * x =
        e (m + 4) + 5 * r + (5 * (T r : ℤ) - greatestFib r * r) -
          (((m + 4 : ℕ) : ℤ) - greatestFib r) * r := by
      rw [hT, hxr]; unfold e; push_cast; ring
    rw [hid]
    have hrF' : (r : ℤ) ≤ fib (m + 4) := by exact_mod_cast (hrF.trans (by omega))
    rw [abs_le] at he4 ihr ⊢
    constructor <;> linarith
  · -- the greedy term is `L (m+3)`
    set r := x - lucas (m + 3) with hr
    have hT := T_of_lucas_le hxL.le hF'.le
    rw [← hr] at hT
    have hTL := T_lucas m
    have hrx : r < x := by have := lucas_pos (m + 3); omega
    have hr1 : r < fib (m + 1) := by have := fib_sub_lucas m; omega
    have hKr : greatestFib r ≤ m + 4 := by
      have : greatestFib r < m + 1 := greatestFib_lt.2 hr1
      omega
    have ihr := ih r hrx
    have hg := gap_mul_le hKr
    have hg0 := gap_nonneg hKr
    have hxr : (x : ℤ) = fib (m + 2) + fib (m + 4) + r := by
      have : x = fib (m + 2) + fib (m + 4) + r := by omega
      exact_mod_cast this
    have hid : 5 * (T x : ℤ) - ((m + 4 : ℕ) : ℤ) * x =
        e (m + 4) + e (m + 2) + 3 * fib (m + 2) + 5 * r + (5 * (T r : ℤ) - greatestFib r * r) -
          (((m + 4 : ℕ) : ℤ) - greatestFib r) * r := by
      rw [hT, hTL, hxr]; unfold e; push_cast; ring
    rw [hid]
    have hr1' : (r : ℤ) ≤ fib (m + 4) := by
      have : fib (m + 1) ≤ fib (m + 4) := fib_mono (by omega)
      exact_mod_cast (hr1.le.trans this)
    have hpos : (0 : ℤ) ≤ fib (m + 2) := by positivity
    rw [abs_le] at he4 he2 ihr ⊢
    constructor <;> linarith

/-! ## The bound for `Z` -/

/-- The constant `c = 2 + ψ = (5 - √5)/2`. -/
noncomputable def c : ℝ := 2 + goldenConj

lemma c_eq : c = (5 - √5) / 2 := by
  unfold c goldenConj; ring

lemma c_pos : 0 < c := by
  have := neg_one_lt_goldenConj; unfold c; linarith

lemma c_le_two : c ≤ 2 := by
  have := goldenConj_neg; unfold c; linarith

lemma abs_goldenConj_pow_le_one (n : ℕ) : |goldenConj ^ n| ≤ 1 := by
  rw [abs_pow]
  apply pow_le_one₀ (abs_nonneg _)
  rw [abs_le]
  constructor
  · exact neg_one_lt_goldenConj.le
  · exact goldenConj_neg.le.trans zero_le_one

/-- `|5 Z (F k) - c k F k| ≤ 4 F k` for `k ≥ 1`. -/
lemma Z_fib_bound (m : ℕ) :
    |5 * (Z (fib (m + 1)) : ℝ) - c * (m + 1 : ℕ) * fib (m + 1)| ≤ 4 * fib (m + 1) := by
  have hZ := Z_fib m
  have hZ' : 5 * (Z (fib (m + 1)) : ℝ) =
      (m + 1) * (2 * fib (m + 1) - fib m) - 2 * fib (m + 1) := by exact_mod_cast hZ
  have hpsi : goldenConj * fib (m + 1) + fib m = goldenConj ^ (m + 1) :=
    goldenConj_mul_fib_succ_add_fib m
  have hid : 5 * (Z (fib (m + 1)) : ℝ) - c * (m + 1 : ℕ) * fib (m + 1) =
      -((m + 1 : ℕ) : ℝ) * goldenConj ^ (m + 1) - 2 * fib (m + 1) := by
    rw [hZ', ← hpsi]; unfold c; push_cast; ring
  rw [hid]
  have hp := abs_goldenConj_pow_le_one (m + 1)
  have hk : ((m + 1 : ℕ) : ℝ) ≤ 2 * fib (m + 1) := by
    exact_mod_cast le_two_mul_fib (k := m + 1) (by omega)
  have hk0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
  have h1 : |((m + 1 : ℕ) : ℝ) * goldenConj ^ (m + 1)| ≤ ((m + 1 : ℕ) : ℝ) := by
    rw [abs_mul, abs_of_nonneg hk0]
    exact mul_le_of_le_one_right hk0 hp
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

theorem Z_bound : ∀ x : ℕ, |5 * (Z x : ℝ) - c * greatestFib x * x| ≤ 13 * x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [Z]
  have hk2 : 2 ≤ greatestFib x := le_greatestFib.2 (by have : fib 2 = 1 := rfl; omega)
  obtain ⟨m, hm⟩ : ∃ m, greatestFib x = m + 2 := ⟨greatestFib x - 2, by omega⟩
  have hF : fib (m + 2) ≤ x := by have := fib_greatestFib_le x; rwa [hm] at this
  have hF' : x < fib (m + 3) := by have := lt_fib_greatestFib_add_one x; rwa [hm] at this
  have h3 : fib (m + 3) = fib (m + 1) + fib (m + 2) := fib_add_two
  set r := x - fib (m + 2) with hr
  have hZ := Z_of_mem (k := m + 2) (by omega) hF hF'.le
  rw [← hr] at hZ
  have hrx : r < x := by have := fib_pos.2 (show 0 < m + 2 by omega); omega
  have hr1 : r < fib (m + 1) := by omega
  have hKr : greatestFib r ≤ m + 2 := by
    have : greatestFib r < m + 1 := greatestFib_lt.2 hr1
    omega
  have ihr := ih r hrx
  have hg := gap_mul_le hKr
  have hg0 := gap_nonneg hKr
  have hg' : (((m + 2 : ℕ) : ℝ) - greatestFib r) * r ≤ 2 * fib (m + 2) := by exact_mod_cast hg
  have hg0' : (0 : ℝ) ≤ (((m + 2 : ℕ) : ℝ) - greatestFib r) * r := by exact_mod_cast hg0
  have hf := Z_fib_bound (m + 1)
  rw [show m + 1 + 1 = m + 2 by ring] at hf
  have hxr : (x : ℝ) = fib (m + 2) + r := by
    have : x = fib (m + 2) + r := by omega
    exact_mod_cast this
  rw [hm]
  have hid : 5 * (Z x : ℝ) - c * ((m + 2 : ℕ) : ℝ) * x =
      (5 * (Z (fib (m + 2)) : ℝ) - c * ((m + 2 : ℕ) : ℝ) * fib (m + 2)) + 5 * r +
        (5 * (Z r : ℝ) - c * greatestFib r * r) -
          c * ((((m + 2 : ℕ) : ℝ) - greatestFib r) * r) := by
    rw [hZ, hxr]; push_cast; ring
  rw [hid]
  have hrF : (r : ℝ) ≤ fib (m + 2) := by
    have : fib (m + 1) ≤ fib (m + 2) := fib_le_fib_succ
    exact_mod_cast (hr1.le.trans this)
  have hc0 := c_pos
  have hc2 := c_le_two
  have hcg : c * ((((m + 2 : ℕ) : ℝ) - greatestFib r) * r) ≤ 2 * (2 * fib (m + 2)) := by
    calc c * ((((m + 2 : ℕ) : ℝ) - greatestFib r) * r)
        ≤ 2 * ((((m + 2 : ℕ) : ℝ) - greatestFib r) * r) :=
          mul_le_mul_of_nonneg_right hc2 hg0'
      _ ≤ 2 * (2 * fib (m + 2)) := by linarith
  have hcg0 : 0 ≤ c * ((((m + 2 : ℕ) : ℝ) - greatestFib r) * r) := mul_nonneg hc0.le hg0'
  rw [abs_le] at hf ihr ⊢
  constructor <;> linarith

end FibLucas
