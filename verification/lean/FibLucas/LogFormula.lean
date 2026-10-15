import FibLucas.Limit

/-!
# The asymptotic formulas with `log_φ n`

With `W(n) = A214981(n)` and `V(n) = A179180(n)`, for every `n ≥ 1`

* `|W(n) - n log_φ n / 5| ≤ 10 n`,
* `|V(n) - c n log_φ n / 5| ≤ 10 n`, where `c = (5 - √5)/2`.

The proof combines `T_bound` and `Z_bound` with `log_φ x < K(x) ≤ log_φ x + 2`, which follows
from `φ^(k-2) ≤ F_k ≤ φ^(k-1)`.
-/

open Real Finset Filter Topology
open Nat (fib greatestFib fib_add_two le_greatestFib lt_fib_greatestFib_add_one fib_greatestFib_le le_fib_add_one)
open scoped goldenRatio

namespace FibLucas

lemma fib_succ_le_goldenRatio_pow (k : ℕ) : (fib (k + 1) : ℝ) ≤ φ ^ k := by
  have h := goldenRatio_mul_fib_succ_add_fib k
  have h0 : (0 : ℝ) ≤ fib k := Nat.cast_nonneg _
  have : φ * (fib (k + 1) : ℝ) ≤ φ * φ ^ k := by rw [← _root_.pow_succ']; linarith
  exact le_of_mul_le_mul_left this goldenRatio_pos

lemma goldenRatio_pow_le_fib (k : ℕ) : φ ^ k ≤ (fib (k + 2) : ℝ) := by
  have h := fib_succ_sub_goldenConj_mul_fib k
  have h2 : (fib (k + 2) : ℝ) = fib k + fib (k + 1) := by exact_mod_cast fib_add_two
  have h0 : (0 : ℝ) ≤ fib k := Nat.cast_nonneg _
  have hψ : -1 < ψ := neg_one_lt_goldenConj
  have hψ0 : ψ < 0 := goldenConj_neg
  nlinarith

/-- `log_φ x < K(x)` for `x ≥ 1`. -/
lemma logb_lt_greatestFib {x : ℕ} (hx : 1 ≤ x) : logb φ x < greatestFib x := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  rw [Real.logb_lt_iff_lt_rpow one_lt_goldenRatio hx0, Real.rpow_natCast]
  calc (x : ℝ) < fib (greatestFib x + 1) := by exact_mod_cast lt_fib_greatestFib_add_one x
    _ ≤ φ ^ greatestFib x := fib_succ_le_goldenRatio_pow _

/-- `K(x) ≤ log_φ x + 2` for `x ≥ 1`. -/
lemma greatestFib_le_logb {x : ℕ} (hx : 1 ≤ x) : (greatestFib x : ℝ) ≤ logb φ x + 2 := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hK : 2 ≤ greatestFib x := le_greatestFib.2 (by simpa using hx)
  obtain ⟨m, hm⟩ : ∃ m, greatestFib x = m + 2 := ⟨greatestFib x - 2, by omega⟩
  have hle : (m : ℝ) ≤ logb φ x := by
    rw [Real.le_logb_iff_rpow_le one_lt_goldenRatio hx0, Real.rpow_natCast]
    calc φ ^ m ≤ fib (m + 2) := goldenRatio_pow_le_fib m
      _ ≤ x := by rw [← hm]; exact_mod_cast fib_greatestFib_le x
  rw [hm]; push_cast; linarith

/-- `K(x) ≤ x + 1`. -/
lemma greatestFib_le_add_one (x : ℕ) : (greatestFib x : ℝ) ≤ x + 1 := by
  have h1 := le_fib_add_one (greatestFib x)
  have h2 := fib_greatestFib_le x
  exact_mod_cast (show greatestFib x ≤ x + 1 by omega)

lemma one_lt_three_mul_log_goldenRatio : 1 < 3 * Real.log φ := by
  have hφ3 : φ ^ 3 = 2 * φ + 1 := by
    have := goldenRatio_sq
    calc φ ^ 3 = φ * φ ^ 2 := by ring
      _ = 2 * φ + 1 := by rw [this]; nlinarith [this]
  have he : Real.exp 1 < φ ^ 3 := by
    have := Real.exp_one_lt_d9
    have := one_lt_goldenRatio
    rw [hφ3]; linarith
  have := Real.log_lt_log (Real.exp_pos 1) he
  rwa [Real.log_exp, Real.log_pow] at this

/-- `n (log_φ (n+1) - log_φ n) ≤ 3` for `n ≥ 1`. -/
lemma mul_logb_succ_sub_le {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (logb φ (n + 1) - logb φ n) ≤ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log φ := Real.log_pos one_lt_goldenRatio
  have h3 := one_lt_three_mul_log_goldenRatio
  have hsub : logb φ (n + 1) - logb φ n = Real.log ((n + 1) / n) / Real.log φ := by
    rw [Real.log_div (by positivity) hn0.ne', Real.logb, Real.logb, sub_div]
  have hlog : Real.log ((n + 1) / n) ≤ 1 / n := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n + 1) / n by positivity)
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  rw [hsub, mul_div_assoc', div_le_iff₀ hl]
  have : (n : ℝ) * Real.log ((n + 1) / n) ≤ 1 := by
    calc (n : ℝ) * Real.log ((n + 1) / n) ≤ n * (1 / n) := mul_le_mul_of_nonneg_left hlog hn0.le
      _ = 1 := by field_simp
  linarith

lemma logb_mono_succ {n : ℕ} (hn : 1 ≤ n) : logb φ n ≤ logb φ (n + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.logb_le_logb_of_le one_lt_goldenRatio hn0 (by linarith)

/-- **The asymptotic formula for `W(n) = A214981(n)`.** For every `n ≥ 1`,
`|W(n) - n log_φ n / 5| ≤ 10 n`; in particular `W(n) = (1/5) n log_φ n + O(n)`. -/
theorem a214981_asymptotic {n : ℕ} (hn : 1 ≤ n) :
    |(a214981 n : ℝ) - n * logb φ n / 5| ≤ 10 * n := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ n + 1 := by omega
  have hT : |5 * (T (n + 1) : ℝ) - greatestFib (n + 1) * ((n + 1 : ℕ) : ℝ)| ≤ 19 * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast T_bound (n + 1)
  have hK1 := logb_lt_greatestFib hx
  have hK2 := greatestFib_le_logb hx
  have hK3 := greatestFib_le_add_one (n + 1)
  have hd := mul_logb_succ_sub_le hn
  have hm := logb_mono_succ hn
  have hL0 : 0 ≤ logb φ n := Real.logb_nonneg one_lt_goldenRatio hn0
  rw [a214981_eq]
  push_cast at hT hK1 hK2 hK3 ⊢
  set K : ℝ := (greatestFib (n + 1) : ℝ)
  set L1 := logb φ ((n : ℝ) + 1)
  set L0 := logb φ (n : ℝ)
  set A : ℝ := (T (n + 1) : ℝ)
  rw [abs_le] at hT ⊢
  have hX : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hK2 hX, mul_le_mul_of_nonneg_left hK1.le hX]

/-- **The asymptotic formula for `V(n) = A179180(n)`.** For every `n ≥ 1`,
`|V(n) - c n log_φ n / 5| ≤ 10 n` with `c = (5 - √5)/2`; in particular
`V(n) = (c/5) n log_φ n + O(n)`. -/
theorem a179180_asymptotic {n : ℕ} (hn : 1 ≤ n) :
    |(a179180 n : ℝ) - (5 - √5) / 2 * n * logb φ n / 5| ≤ 10 * n := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ n + 1 := by omega
  have hZ := Z_bound (n + 1)
  have hK1 := logb_lt_greatestFib hx
  have hK2 := greatestFib_le_logb hx
  have hK3 := greatestFib_le_add_one (n + 1)
  have hd := mul_logb_succ_sub_le hn
  have hm := logb_mono_succ hn
  have hL0 : 0 ≤ logb φ n := Real.logb_nonneg one_lt_goldenRatio hn0
  have hc0 := c_pos
  have hc2 := c_le_two
  rw [a179180_eq, ← c_eq]
  push_cast at hZ hK1 hK2 hK3 ⊢
  set K : ℝ := (greatestFib (n + 1) : ℝ)
  set L1 := logb φ ((n : ℝ) + 1)
  set L0 := logb φ (n : ℝ)
  set B : ℝ := (Z (n + 1) : ℝ)
  rw [abs_le] at hZ ⊢
  have hX : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have e1 : 0 ≤ c * ((n + 1) * (L1 + 2 - K)) := by
    have := mul_le_mul_of_nonneg_left hK2 hX
    apply mul_nonneg hc0.le; nlinarith
  have e2 : 0 ≤ c * ((n + 1) * (K - L1)) := by
    have := mul_le_mul_of_nonneg_left hK1.le hX
    apply mul_nonneg hc0.le; nlinarith
  have e3 : c * ((n + 1) * (L1 + 2 - K)) ≤ 2 * ((n + 1) * (L1 + 2 - K)) := by
    apply mul_le_mul_of_nonneg_right hc2; have := mul_le_mul_of_nonneg_left hK2 hX; nlinarith
  have e4 : c * ((n + 1) * (K - L1)) ≤ 2 * ((n + 1) * (K - L1)) := by
    apply mul_le_mul_of_nonneg_right hc2; have := mul_le_mul_of_nonneg_left hK1.le hX; nlinarith
  have e5 : 0 ≤ c * (L1 + n * (L1 - L0)) := by
    apply mul_nonneg hc0.le; nlinarith
  have e6 : c * (L1 + n * (L1 - L0)) ≤ 2 * (L1 + n * (L1 - L0)) := by
    apply mul_le_mul_of_nonneg_right hc2; nlinarith
  constructor <;> nlinarith

end FibLucas
