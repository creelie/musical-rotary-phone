import FibLucas.Asymptotic

/-!
# Kimberling's limit conjecture

`A179180(n) / A214981(n) → (5 - √5)/2`, and `(5 - √5)/2 ∈ (1.2, 1.4)`.
-/

open Nat Real Finset Filter Topology

namespace FibLucas

lemma sum_Icc_one_eq_sum_range (f : ℕ → ℕ) (hf : f 0 = 0) (n : ℕ) :
    ∑ i ∈ Icc 1 n, f i = ∑ i ∈ range (n + 1), f i := by
  rw [Finset.range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_eq_sum_Ico_succ_bot (show 0 < n + 1 by omega), hf, zero_add]

lemma a214981_eq (n : ℕ) : a214981 n = T (n + 1) :=
  sum_Icc_one_eq_sum_range _ a214973_zero n

lemma a179180_eq (n : ℕ) : a179180 n = Z (n + 1) :=
  sum_Icc_one_eq_sum_range _ a007895_zero n

/-- **Kimberling's conjecture (A214981), value of the limit.** The ratio of the total number of
Zeckendorf summands of `1, ..., n` to the total number of terms of the greedy Fibonacci-and-Lucas
representations of `1, ..., n` tends to `(5 - √5)/2`. -/
theorem tendsto_ratio :
    Tendsto (fun n => (a179180 n : ℝ) / a214981 n) atTop (𝓝 ((5 - √5) / 2)) := by
  rw [← c_eq, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (19 + 51 / ε)
  refine ⟨fib M, fun n hn => ?_⟩
  rw [a179180_eq, a214981_eq, Real.dist_eq]
  set x := n + 1 with hx
  have hK : M ≤ greatestFib x := le_greatestFib.2 (by omega)
  have hT : |5 * (T x : ℝ) - greatestFib x * x| ≤ 19 * x := by exact_mod_cast T_bound x
  have hZ := Z_bound x
  set K : ℝ := ((greatestFib x : ℕ) : ℝ) with hKdef
  set X : ℝ := ((x : ℕ) : ℝ) with hXdef
  set A : ℝ := ((T x : ℕ) : ℝ) with hA
  set B : ℝ := ((Z x : ℕ) : ℝ) with hB
  have hX : 0 < X := by rw [hXdef]; positivity
  have hKM : (M : ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hK
  have hεM : 51 / ε < K - 19 := by linarith
  have h51 : 51 < ε * (K - 19) := by
    rw [div_lt_iff₀ hε] at hεM; linarith
  have hK19 : 0 < K - 19 := by
    have : 0 < 51 / ε := by positivity
    linarith
  rw [abs_le] at hT hZ
  have hApos : (K - 19) * X ≤ 5 * A := by nlinarith
  have hA0 : 0 < A := by
    have : 0 < (K - 19) * X := mul_pos hK19 hX
    linarith
  have hc0 := c_pos
  have hc2 := c_le_two
  have hid : B / A - c = (5 * B - c * (5 * A)) / (5 * A) := by
    field_simp
  have h5A : (0 : ℝ) < 5 * A := by linarith
  rw [hid, abs_div, abs_of_pos h5A, div_lt_iff₀ h5A]
  have hnum : |5 * B - c * (5 * A)| ≤ 51 * X := by
    have e1 : 5 * B - c * (5 * A) = (5 * B - c * K * X) - c * (5 * A - K * X) := by ring
    rw [e1, abs_le]
    have hcT1 : c * (5 * A - K * X) ≤ 2 * (19 * X) := by
      calc c * (5 * A - K * X) ≤ c * (19 * X) := mul_le_mul_of_nonneg_left hT.2 hc0.le
        _ ≤ 2 * (19 * X) := mul_le_mul_of_nonneg_right hc2 (by positivity)
    have hcT2 : -(2 * (19 * X)) ≤ c * (5 * A - K * X) := by
      calc -(2 * (19 * X)) ≤ -(c * (19 * X)) := by
            have := mul_le_mul_of_nonneg_right hc2 (show 0 ≤ 19 * X by positivity)
            linarith
        _ = c * (-(19 * X)) := by ring
        _ ≤ c * (5 * A - K * X) := mul_le_mul_of_nonneg_left hT.1 hc0.le
    constructor <;> linarith [hZ.1, hZ.2]
  calc |5 * B - c * (5 * A)| ≤ 51 * X := hnum
    _ < ε * (K - 19) * X := by nlinarith
    _ ≤ ε * (5 * A) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hApos hε.le

lemma limit_gt : (6 : ℝ) / 5 < (5 - √5) / 2 := by
  have : √5 < 13 / 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

lemma limit_lt : (5 - √5) / 2 < (7 : ℝ) / 5 := by
  have : 11 / 5 < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- **Kimberling's conjecture (A214981; J. Integer Seq. 23 (2020), Article 20.9.5,
Conjecture 2).** Let `V(n)` be the number of terms in the Zeckendorf representations of
`1, ..., n` and `W(n)` the number of terms in the greedy Fibonacci-and-Lucas representations of
`1, ..., n`. Then `lim V(n)/W(n)` exists and lies in the interval `(1.2, 1.4)`. -/
theorem kimberling_conjecture :
    ∃ L : ℝ, Tendsto (fun n => (a179180 n : ℝ) / a214981 n) atTop (𝓝 L) ∧
      6 / 5 < L ∧ L < 7 / 5 :=
  ⟨_, tendsto_ratio, limit_gt, limit_lt⟩

end FibLucas
