import FibLucas.Greedy

/-!
# Kurkov's formula

`a214973 n = a329320 (a048679 n)`.

Write the Zeckendorf representation of `n` as `F k₁ + ... + F kᵣ` with `k₁ > ... > kᵣ ≥ 2`. The
greedy algorithm pairs a summand `F k` with a following `F (k - 2)` into `L (k - 1)`, from the top
down; the count is `W`. Compression sends the summand `F kᵢ` to the bit `kᵢ - 2 - (r - i)`, so that
gaps of two in the Zeckendorf indices become adjacent bits; A329320 counts each maximal block of
`ℓ` ones as `⌈ℓ/2⌉`, which is `W` again.
-/

open Nat

namespace FibLucas

/-! ## The greedy count read off the Zeckendorf representation -/

/-- A summand `F k` followed by `F (k - 2)` is paired into `L (k - 1)`; every other summand stands
alone. -/
def W : List ℕ → ℕ
  | [] => 0
  | [_] => 1
  | k :: k' :: rest => if k' + 2 = k then 1 + W rest else 1 + W (k' :: rest)

lemma W_nil : W [] = 0 := rfl

lemma W_single (k : ℕ) : W [k] = 1 := rfl

lemma W_cons_cons (k k' : ℕ) (rest : List ℕ) :
    W (k :: k' :: rest) = if k' + 2 = k then 1 + W rest else 1 + W (k' :: rest) := rfl

lemma greatestFib_eq {k n : ℕ} (h1 : fib k ≤ n) (h2 : n < fib (k + 1)) : greatestFib n = k :=
  le_antisymm (Nat.lt_succ_iff.1 (greatestFib_lt.2 h2)) (le_greatestFib.2 h1)

lemma two_le_greatestFib {n : ℕ} (hn : 0 < n) : 2 ≤ greatestFib n :=
  le_greatestFib.2 (by rw [fib_two]; omega)

theorem a214973_eq_W (n : ℕ) : a214973 n = W (zeckendorf n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [a214973_zero, zeckendorf_zero, W_nil]
  have hz := zeckendorf_of_pos hn
  have hF := fib_greatestFib_le n
  have hF' := lt_fib_greatestFib_add_one n
  have hK2 := two_le_greatestFib hn
  generalize greatestFib n = K at hz hF hF' hK2
  rw [hz]
  rcases Nat.lt_or_ge K 4 with hK4 | hK4
  · have h4 : fib 4 = 3 := rfl
    have hmono : fib (K + 1) ≤ fib 4 := fib_mono (by omega)
    have h0 : n - fib K = 0 := by
      interval_cases K
      · have : fib 2 = 1 := rfl
        have : fib (2 + 1) = 2 := rfl
        omega
      · have : fib 3 = 2 := rfl
        have : fib (3 + 1) = 3 := rfl
        omega
    rw [h0, zeckendorf_zero, W_single]
    have : n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl
    · exact a214973_one
    · exact a214973_two
  obtain ⟨q, rfl⟩ : ∃ q, K = q + 4 := ⟨K - 4, by omega⟩
  rw [show q + 4 + 1 = q + 5 by ring] at hF'
  have hL3 := lucas_three q
  have h5 : fib (q + 5) = fib (q + 3) + fib (q + 4) := fib_add_two
  have hpos : 0 < fib (q + 4) := fib_pos.2 (by omega)
  rcases Nat.lt_or_ge n (lucas (q + 3)) with hL | hL
  · rw [a214973_of_lt_lucas hF hL]
    rcases Nat.eq_zero_or_pos (n - fib (q + 4)) with h0 | h0
    · rw [h0, a214973_zero, zeckendorf_zero, W_single]
    · rw [zeckendorf_of_pos h0]
      have hK' : greatestFib (n - fib (q + 4)) < q + 2 := greatestFib_lt.2 (by omega)
      rw [W_cons_cons, ite_eq_right (by omega), ← zeckendorf_of_pos h0, ih _ (by omega)]
  · rw [a214973_of_lucas_le hL hF']
    have hge : fib (q + 2) ≤ n - fib (q + 4) := by omega
    have hlt : n - fib (q + 4) < fib (q + 2 + 1) := by
      rw [show q + 2 + 1 = q + 3 by ring]; omega
    have hg : greatestFib (n - fib (q + 4)) = q + 2 := greatestFib_eq hge hlt
    have h0 : 0 < n - fib (q + 4) := lt_of_lt_of_le (fib_pos.2 (by omega)) hge
    rw [zeckendorf_of_pos h0, hg, W_cons_cons, ite_eq_left (by omega)]
    have : n - lucas (q + 3) = n - fib (q + 4) - fib (q + 2) := by omega
    rw [this, ih _ (by omega)]

/-! ## A329320 -/

/-- The summand of A329320: `hh t = 1 - A035263(1 + t)`, the parity of `v₂(t + 1)`. -/
def hh (t : ℕ) : ℕ := 1 - a035263 (1 + t)

lemma padicValNat_two_mul {x : ℕ} (hx : x ≠ 0) :
    padicValNat 2 (2 * x) = 1 + padicValNat 2 x := by
  rw [padicValNat.mul (by norm_num) hx, padicValNat_self]

lemma hh_even (u : ℕ) : hh (2 * u) = 0 := by
  have h1 : padicValNat 2 (1 + 2 * u) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have h2 : padicValNat 2 (2 * (1 + 2 * u)) = 1 + padicValNat 2 (1 + 2 * u) :=
    padicValNat_two_mul (by omega)
  unfold hh a035263
  omega

lemma hh_odd (u : ℕ) : hh (2 * u + 1) = 1 - hh u := by
  have h1 : padicValNat 2 (2 * (1 + (2 * u + 1))) = 1 + padicValNat 2 (1 + (2 * u + 1)) :=
    padicValNat_two_mul (by omega)
  have h2 : padicValNat 2 (1 + (2 * u + 1)) = 1 + padicValNat 2 (1 + u) := by
    rw [show 1 + (2 * u + 1) = 2 * (1 + u) by ring]; exact padicValNat_two_mul (by omega)
  have h3 : padicValNat 2 (2 * (1 + u)) = 1 + padicValNat 2 (1 + u) :=
    padicValNat_two_mul (by omega)
  unfold hh a035263
  omega

lemma hh_zero : hh 0 = 0 := hh_even 0

lemma hh_one : hh 1 = 1 := by
  have := hh_odd 0
  rw [hh_zero] at this
  simpa using this

lemma a329320_zero : a329320 0 = 0 := by
  simp only [a329320, Nat.log_zero_right, zero_add, Finset.sum_range_one, Nat.zero_div]
  exact hh_zero

lemma a329320_one : a329320 1 = 1 := by
  simp only [a329320, Nat.log_one_right, zero_add, Finset.sum_range_one, pow_zero, Nat.div_one]
  exact hh_one

/-- `A329320(y) = A329320(⌊y/2⌋) + hh y`. -/
lemma a329320_eq (y : ℕ) : a329320 y = a329320 (y / 2) + hh y := by
  rcases Nat.lt_or_ge y 2 with hy | hy
  · interval_cases y
    · simp [hh_zero]
    · simp [a329320_one, a329320_zero, hh_one]
  have hlog : Nat.log 2 y = Nat.log 2 (y / 2) + 1 := by
    rw [Nat.log_div_base]
    have := Nat.log_pos (by norm_num) hy
    omega
  unfold a329320
  rw [hlog, Finset.sum_range_succ' _ (Nat.log 2 (y / 2) + 1)]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
  · rw [pow_zero, Nat.div_one]
    rfl

/-- The top bit of a block: for `z < 2^Q`, `hh` does not see the bits `Q + 1` and `Q`. -/
lemma hh_top (Q : ℕ) :
    ∀ z < 2 ^ Q, hh (2 ^ (Q + 1) + z) = hh z ∧ hh (2 ^ (Q + 1) + 2 ^ Q + z) = hh z := by
  induction Q with
  | zero =>
    intro z hz
    obtain rfl : z = 0 := by simpa using hz
    refine ⟨?_, ?_⟩
    · show hh (2 * 1) = hh 0
      rw [hh_even, hh_zero]
    · show hh (2 * 1 + 1) = hh 0
      rw [hh_odd, hh_one, hh_zero]
  | succ Q ih =>
    intro z hz
    obtain ⟨u, rfl | rfl⟩ : ∃ u, z = 2 * u ∨ z = 2 * u + 1 := ⟨z / 2, by omega⟩
    · have e1 : 2 ^ (Q + 1 + 1) + 2 * u = 2 * (2 ^ (Q + 1) + u) := by ring
      have e2 : 2 ^ (Q + 1 + 1) + 2 ^ (Q + 1) + 2 * u = 2 * (2 ^ (Q + 1) + 2 ^ Q + u) := by ring
      rw [e1, e2]
      simp only [hh_even, and_self]
    · have hu : u < 2 ^ Q := by rw [pow_succ] at hz; omega
      have e1 : 2 ^ (Q + 1 + 1) + (2 * u + 1) = 2 * (2 ^ (Q + 1) + u) + 1 := by ring
      have e2 : 2 ^ (Q + 1 + 1) + 2 ^ (Q + 1) + (2 * u + 1) =
          2 * (2 ^ (Q + 1) + 2 ^ Q + u) + 1 := by ring
      rw [e1, e2]
      simp only [hh_odd, (ih u hu).1, (ih u hu).2, and_self]

/-- The OEIS recursion `a(2^m + k) = a(k mod 2^(m-1)) + 1`, split into its two halves. -/
lemma a329320_top (Q : ℕ) : ∀ z < 2 ^ Q,
    a329320 (2 ^ (Q + 1) + z) = 1 + a329320 z ∧
      a329320 (2 ^ (Q + 1) + 2 ^ Q + z) = 1 + a329320 z := by
  induction Q with
  | zero =>
    intro z hz
    obtain rfl : z = 0 := by simpa using hz
    have h2 : a329320 2 = 1 := by
      rw [a329320_eq]; norm_num [a329320_one, show hh 2 = 0 from hh_even 1]
    have h3 : a329320 3 = 1 := by
      rw [a329320_eq]
      norm_num [a329320_one, show hh 3 = 0 by simpa [hh_one] using hh_odd 1]
    exact ⟨by simpa [a329320_zero] using h2, by simpa [a329320_zero] using h3⟩
  | succ Q ih =>
    intro z hz
    have hz2 : z / 2 < 2 ^ Q := by rw [pow_succ] at hz; omega
    have e1 : (2 ^ (Q + 1 + 1) + z) / 2 = 2 ^ (Q + 1) + z / 2 := by
      rw [show 2 ^ (Q + 1 + 1) = 2 * 2 ^ (Q + 1) by ring]; omega
    have e2 : (2 ^ (Q + 1 + 1) + 2 ^ (Q + 1) + z) / 2 = 2 ^ (Q + 1) + 2 ^ Q + z / 2 := by
      rw [show 2 ^ (Q + 1 + 1) = 2 * 2 ^ (Q + 1) by ring, show 2 ^ (Q + 1) = 2 * 2 ^ Q by ring]
      omega
    obtain ⟨h1, h2⟩ := hh_top (Q + 1) z hz
    rw [a329320_eq (2 ^ (Q + 1 + 1) + z), a329320_eq (2 ^ (Q + 1 + 1) + 2 ^ (Q + 1) + z), e1, e2,
      (ih _ hz2).1, (ih _ hz2).2, h1, h2, a329320_eq z]
    constructor <;> ring

lemma a329320_two_pow (P : ℕ) : a329320 (2 ^ P) = 1 := by
  rcases P with _ | Q
  · exact a329320_one
  · simpa [a329320_zero] using (a329320_top Q 0 (by positivity)).1

/-! ## Compression -/

/-- The compression `0 → 0`, `01 → 1` of the binary expansion of `m`. -/
def CV (m : ℕ) : ℕ := Nat.ofDigits 2 (compress (Nat.digits 2 m))

lemma a048679_eq (n : ℕ) : a048679 n = CV (a003714 n) := rfl

lemma compress_nil : compress [] = [] := by rw [compress]

lemma compress_one (rest : List ℕ) : compress (1 :: rest) = 1 :: compress rest.tail := by
  rw [compress]; simp

lemma compress_zero (rest : List ℕ) : compress (0 :: rest) = 0 :: compress rest := by
  rw [compress]; simp

lemma digits_two_mul {X : ℕ} (hX : 0 < X) : Nat.digits 2 (2 * X) = 0 :: Nat.digits 2 X := by
  rw [Nat.digits_def' (by norm_num) (by omega), show 2 * X % 2 = 0 by omega,
    show 2 * X / 2 = X by omega]

lemma digits_four_mul_add_one (X : ℕ) :
    Nat.digits 2 (4 * X + 1) = 1 :: Nat.digits 2 (2 * X) := by
  rw [Nat.digits_def' (by norm_num) (by omega), show (4 * X + 1) % 2 = 1 by omega,
    show (4 * X + 1) / 2 = 2 * X by omega]

lemma CV_zero : CV 0 = 0 := by simp [CV, compress_nil]

lemma CV_two_mul (X : ℕ) : CV (2 * X) = 2 * CV X := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [CV_zero]
  · unfold CV
    rw [digits_two_mul hX, compress_zero, Nat.ofDigits_cons]
    simp

lemma CV_four_mul_add_one (X : ℕ) : CV (4 * X + 1) = 1 + 2 * CV X := by
  unfold CV
  rw [digits_four_mul_add_one, compress_one]
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [compress_nil, Nat.ofDigits_cons]
  · rw [digits_two_mul hX, List.tail_cons, Nat.ofDigits_cons]

lemma CV_one : CV 1 = 1 := by simpa [CV_zero] using CV_four_mul_add_one 0

lemma CV_two_pow : ∀ k, CV (2 ^ k) = 2 ^ k
  | 0 => CV_one
  | k + 1 => by rw [pow_succ', CV_two_mul, CV_two_pow k]

/-! ## Binary weight -/

/-- The number of ones in the binary expansion of `n`. -/
def pc (n : ℕ) : ℕ := if h : n = 0 then 0 else n % 2 + pc (n / 2)
termination_by n
decreasing_by omega

lemma pc_zero : pc 0 = 0 := by rw [pc]; simp

lemma pc_pos {n : ℕ} (hn : n ≠ 0) : pc n = n % 2 + pc (n / 2) := by rw [pc]; simp [hn]

lemma pc_two_mul (X : ℕ) : pc (2 * X) = pc X := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  · rw [pc_pos (n := 2 * X) (by omega), show 2 * X % 2 = 0 by omega,
      show 2 * X / 2 = X by omega, zero_add]

lemma pc_four_mul_add_one (Y : ℕ) : pc (4 * Y + 1) = pc Y + 1 := by
  rw [pc_pos (n := 4 * Y + 1) (by omega), show (4 * Y + 1) % 2 = 1 by omega,
    show (4 * Y + 1) / 2 = 2 * Y by omega, pc_two_mul]
  ring

lemma pc_le : ∀ P m, m < 2 ^ P → pc m ≤ P := by
  intro P
  induction P with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := by simpa using hm
    simp [pc_zero]
  | succ P ih =>
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [pc_zero]
    · rw [pc_pos (by omega)]
      have := ih (m / 2) (by rw [pow_succ] at hm; omega)
      omega

lemma pc_two_pow_add : ∀ P m, m < 2 ^ P → pc (2 ^ P + m) = pc m + 1 := by
  intro P
  induction P with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := by simpa using hm
    rw [pc_pos (by norm_num)]
    simp [pc_zero]
  | succ P ih =>
    intro m hm
    have hT : 2 ^ (P + 1) = 2 * 2 ^ P := by ring
    rw [hT] at hm
    have hm2 : m / 2 < 2 ^ P := by omega
    rw [pc_pos (n := 2 ^ (P + 1) + m) (by positivity), hT,
      show (2 * 2 ^ P + m) % 2 = m % 2 by omega,
      show (2 * 2 ^ P + m) / 2 = 2 ^ P + m / 2 by omega, ih _ hm2]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [pc_zero]
    · rw [pc_pos (n := m) (by omega)]
      ring

/-! ## Fibbinary numbers -/

/-- `m` has no two adjacent ones in binary. -/
def IsFibb (m : ℕ) : Prop := ∀ i, m / 2 ^ i % 4 ≠ 3

lemma fibb_zero : IsFibb 0 := fun i => by simp

lemma fibb_one : IsFibb 1 := fun i => by
  rcases i with _ | i
  · norm_num
  · have : 1 < 2 ^ (i + 1) := by have := Nat.two_pow_pos i; rw [pow_succ]; omega
    rw [Nat.div_eq_of_lt this]
    norm_num

lemma fibb_of_two_mul {X : ℕ} (h : IsFibb (2 * X)) : IsFibb X := fun i => by
  have := h (i + 1)
  rwa [pow_succ', Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)] at this

lemma fibb_odd {X : ℕ} (h : IsFibb (2 * X + 1)) : X % 2 = 0 := by
  have := h 0
  rw [pow_zero, Nat.div_one] at this
  omega

lemma fibb_of_four_mul_add_one {Y : ℕ} (h : IsFibb (4 * Y + 1)) : IsFibb Y := fun i => by
  have := h (i + 2)
  rwa [show 2 ^ (i + 2) = 4 * 2 ^ i by ring, ← Nat.div_div_eq_div_mul,
    show (4 * Y + 1) / 4 = Y by omega] at this

lemma fibb_two_pow_add {m Q : ℕ} (hf : IsFibb m) (hm : m < 2 ^ Q) :
    IsFibb (2 ^ (Q + 1) + m) := by
  intro i
  rcases Nat.lt_trichotomy i Q with hi | rfl | hi
  · obtain ⟨d, rfl⟩ : ∃ d, Q = i + 1 + d := ⟨Q - i - 1, by omega⟩
    have e : 2 ^ (i + 1 + d + 1) + m = 2 ^ i * (4 * 2 ^ d) + m := by ring
    rw [e, Nat.mul_add_div (Nat.two_pow_pos i)]
    have := hf i
    omega
  · have e : 2 ^ (i + 1) + m = 2 ^ i * 2 + m := by ring
    rw [e, Nat.mul_add_div (Nat.two_pow_pos i), Nat.div_eq_of_lt hm]
    norm_num
  · have h1 : 2 ^ (Q + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    have h2 : 2 ^ Q < 2 ^ (Q + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h3 : (2 ^ (Q + 1) + m) / 2 ^ i < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i)]
      omega
    generalize (2 ^ (Q + 1) + m) / 2 ^ i = x at h3 ⊢
    omega

/-- Compression of a fibbinary number with one more top bit: the top bit `2^(P+1)` moves down by
the number of ones below it. -/
theorem CV_top : ∀ m P, IsFibb m → m < 2 ^ P → CV (2 ^ (P + 1) + m) = 2 ^ (P + 1 - pc m) + CV m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P hf hm
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [add_zero, CV_two_pow, pc_zero, CV_zero]
    simp
  obtain ⟨X, rfl | rfl⟩ : ∃ X, m = 2 * X ∨ m = 2 * X + 1 := ⟨m / 2, by omega⟩
  · have hX : 0 < X := by omega
    rcases P with _ | P'
    · rw [pow_zero] at hm; omega
    have hXP : X < 2 ^ P' := by rw [pow_succ] at hm; omega
    have hpc : pc X ≤ P' := pc_le P' X hXP
    have e : 2 ^ (P' + 1 + 1) + 2 * X = 2 * (2 ^ (P' + 1) + X) := by ring
    rw [e, CV_two_mul, ih X (by omega) P' (fibb_of_two_mul hf) hXP, pc_two_mul, CV_two_mul,
      show P' + 1 + 1 - pc X = (P' + 1 - pc X) + 1 by omega, pow_succ]
    ring
  · have hX2 := fibb_odd hf
    obtain ⟨Y, rfl⟩ : ∃ Y, X = 2 * Y := ⟨X / 2, by omega⟩
    rw [show 2 * (2 * Y) + 1 = 4 * Y + 1 by ring] at hf hm ih ⊢
    have hf' : IsFibb Y := fibb_of_four_mul_add_one hf
    rcases P with _ | _ | P''
    · rw [pow_zero] at hm; omega
    · have hY : Y = 0 := by norm_num at hm; omega
      subst hY
      have c5 : CV 5 = 3 := by
        have := CV_four_mul_add_one 1
        rw [CV_one] at this
        simpa using this
      have p1 : pc 1 = 1 := by simpa [pc_zero] using pc_four_mul_add_one 0
      norm_num [c5, p1, CV_one]
    · have hYP : Y < 2 ^ P'' := by rw [pow_succ, pow_succ] at hm; omega
      have hpc : pc Y ≤ P'' := pc_le P'' Y hYP
      have e : 2 ^ (P'' + 1 + 1 + 1) + (4 * Y + 1) = 4 * (2 ^ (P'' + 1) + Y) + 1 := by ring
      rw [e, CV_four_mul_add_one, ih Y (by omega) P'' hf' hYP, pc_four_mul_add_one,
        CV_four_mul_add_one, show P'' + 1 + 1 + 1 - (pc Y + 1) = (P'' + 1 - pc Y) + 1 by omega,
        pow_succ]
      ring

/-! ## The Zeckendorf representation -/

/-- The compressed value of a Zeckendorf list: the summand `F k` with `l` below it becomes the bit
`k - 2 - |l|`. -/
def cvZ : List ℕ → ℕ
  | [] => 0
  | k :: l => 2 ^ (k - 2 - l.length) + cvZ l

lemma cvZ_nil : cvZ [] = 0 := rfl

lemma cvZ_cons (k : ℕ) (l : List ℕ) : cvZ (k :: l) = 2 ^ (k - 2 - l.length) + cvZ l := rfl

lemma a003714_zero : a003714 0 = 0 := by simp [a003714]

lemma a003714_of_pos {n : ℕ} (hn : 0 < n) :
    a003714 n = 2 ^ (greatestFib n - 2) + a003714 (n - fib (greatestFib n)) := by
  unfold a003714
  rw [zeckendorf_of_pos hn, List.map_cons, List.sum_cons]

/-- One step of the Zeckendorf algorithm. -/
lemma zeck_decomp {n : ℕ} (hn : 0 < n) :
    ∃ K n', greatestFib n = K ∧ 2 ≤ K ∧ zeckendorf n = K :: zeckendorf n' ∧
      a003714 n = 2 ^ (K - 2) + a003714 n' ∧ n' < n ∧
      (n' = 0 ∨ (0 < n' ∧ greatestFib n' + 2 ≤ K)) := by
  refine ⟨greatestFib n, n - fib (greatestFib n), rfl, two_le_greatestFib hn, zeckendorf_of_pos hn,
    a003714_of_pos hn, Nat.sub_lt hn (fib_pos.2 (by have := two_le_greatestFib hn; omega)), ?_⟩
  rcases Nat.eq_zero_or_pos (n - fib (greatestFib n)) with h0 | h0
  · exact Or.inl h0
  · refine Or.inr ⟨h0, ?_⟩
    have h1 := greatestFib_sub_fib_greatestFib_le_greatestFib (n := n) (by omega)
    have h2 := two_le_greatestFib h0
    omega

theorem two_mul_length_le : ∀ n, 0 < n → 2 * (zeckendorf n).length ≤ greatestFib n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨K, n', hK, hK2, hz, -, hlt, hcase⟩ := zeck_decomp hn
  rw [hK, hz, List.length_cons]
  rcases hcase with rfl | ⟨h0, hK'⟩
  · rw [zeckendorf_zero, List.length_nil]; omega
  · have := ih n' hlt h0; omega

theorem a003714_lt : ∀ n, 0 < n → a003714 n < 2 ^ (greatestFib n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨K, n', hK, hK2, -, ha, hlt, hcase⟩ := zeck_decomp hn
  rw [hK, ha]
  rcases hcase with rfl | ⟨h0, hK'⟩
  · rw [a003714_zero, add_zero]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · have h1 := ih n' hlt h0
    have h2 : 2 ≤ greatestFib n' := two_le_greatestFib h0
    obtain ⟨j, rfl⟩ : ∃ j, K = j + 4 := ⟨K - 4, by omega⟩
    have h3 : 2 ^ (greatestFib n' - 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show j + 4 - 2 = j + 2 by omega, show j + 4 - 1 = j + 3 by omega]
    have e : 2 ^ (j + 3) = 2 ^ (j + 2) + 2 ^ (j + 2) := by ring
    have e' : 2 ^ (j + 2) = 2 ^ (j + 1) + 2 ^ (j + 1) := by ring
    omega

lemma a003714_rest_lt {K n' : ℕ} (hK2 : 2 ≤ K)
    (hcase : n' = 0 ∨ (0 < n' ∧ greatestFib n' + 2 ≤ K)) : a003714 n' < 2 ^ (K - 3) := by
  rcases hcase with rfl | ⟨h0, hK'⟩
  · rw [a003714_zero]; positivity
  · have h1 := a003714_lt n' h0
    have h2 : 2 ^ (greatestFib n' - 1) ≤ 2 ^ (K - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem fibb_a003714 : ∀ n, IsFibb (a003714 n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [a003714_zero]; exact fibb_zero
  obtain ⟨K, n', -, hK2, -, ha, hlt, hcase⟩ := zeck_decomp hn
  have hr := a003714_rest_lt hK2 hcase
  rw [ha]
  rcases Nat.lt_or_ge K 3 with hK3 | hK3
  · rw [show K - 3 = 0 by omega, pow_zero] at hr
    rw [show a003714 n' = 0 by omega, add_zero, show K - 2 = 0 by omega, pow_zero]
    exact fibb_one
  · rw [show K - 2 = (K - 3) + 1 by omega]
    exact fibb_two_pow_add (ih n' hlt) hr

theorem pc_a003714 : ∀ n, pc (a003714 n) = (zeckendorf n).length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [a003714_zero, pc_zero, zeckendorf_zero, List.length_nil]
  obtain ⟨K, n', -, hK2, hz, ha, hlt, hcase⟩ := zeck_decomp hn
  have hr := a003714_rest_lt hK2 hcase
  rw [ha, hz, List.length_cons, ← ih n' hlt]
  exact pc_two_pow_add (K - 2) _ (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- A048679 in Zeckendorf terms. -/
theorem CV_a003714 : ∀ n, CV (a003714 n) = cvZ (zeckendorf n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [a003714_zero, zeckendorf_zero, CV_zero, cvZ_nil]
  obtain ⟨K, n', -, hK2, hz, ha, hlt, hcase⟩ := zeck_decomp hn
  have hr := a003714_rest_lt hK2 hcase
  rw [ha, hz, cvZ_cons, ← ih n' hlt, ← pc_a003714 n']
  rcases Nat.lt_or_ge K 3 with hK3 | hK3
  · rw [show K - 3 = 0 by omega, pow_zero] at hr
    rw [show a003714 n' = 0 by omega, show K - 2 = 0 by omega, pc_zero, CV_zero]
    simp [CV_one]
  · rw [show K - 2 = (K - 3) + 1 by omega]
    exact CV_top _ _ (fibb_a003714 n') hr

theorem cvZ_lt : ∀ n, 0 < n → cvZ (zeckendorf n) < 2 ^ (greatestFib n - (zeckendorf n).length) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨K, n', hK, hK2, hz, -, hlt, hcase⟩ := zeck_decomp hn
  rw [hK, hz, cvZ_cons, List.length_cons]
  rcases hcase with rfl | ⟨h0, hK'⟩
  · rw [zeckendorf_zero, cvZ_nil, List.length_nil, add_zero]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · have h1 := ih n' hlt h0
    have h2 := two_mul_length_le n' h0
    have h3 : 2 ^ (greatestFib n' - (zeckendorf n').length) ≤
        2 ^ (K - 2 - (zeckendorf n').length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show K - ((zeckendorf n').length + 1) = (K - 2 - (zeckendorf n').length) + 1 by omega,
      pow_succ]
    omega

/-- A329320 of the compressed value is the greedy count. -/
theorem a329320_cvZ : ∀ n, a329320 (cvZ (zeckendorf n)) = W (zeckendorf n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zeckendorf_zero, cvZ_nil, a329320_zero, W_nil]
  obtain ⟨K, n', -, hK2, hz, -, hlt, hcase⟩ := zeck_decomp hn
  rw [hz, cvZ_cons]
  rcases hcase with rfl | ⟨h0, hK'⟩
  · rw [zeckendorf_zero, cvZ_nil, add_zero, a329320_two_pow, W_single]
  obtain ⟨K', n'', hK'', hK'2, hz', -, hlt', hcase'⟩ := zeck_decomp h0
  have hlen := two_mul_length_le n' h0
  rw [hK''] at hK' hlen
  have hL : (zeckendorf n').length = (zeckendorf n'').length + 1 := by
    rw [hz', List.length_cons]
  have hQ : K - 2 - (zeckendorf n').length = (K - 3 - (zeckendorf n').length) + 1 := by omega
  rw [hQ]
  rcases Nat.lt_or_ge (K' + 2) K with hlt2 | hge2
  · have hc : cvZ (zeckendorf n') < 2 ^ (K - 3 - (zeckendorf n').length) := by
      have h1 := cvZ_lt n' h0
      rw [hK''] at h1
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [(a329320_top _ _ hc).1, ih n' hlt, hz', W_cons_cons, ite_eq_right (by omega)]
  · have hKK : K' + 2 = K := by omega
    have hc'' : cvZ (zeckendorf n'') < 2 ^ (K' - 2 - (zeckendorf n'').length) := by
      rcases hcase' with rfl | ⟨h0', hK'''⟩
      · rw [zeckendorf_zero, cvZ_nil]; positivity
      · have h1 := cvZ_lt n'' h0'
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hQ' : K' - 2 - (zeckendorf n'').length = K - 3 - (zeckendorf n').length := by
      rw [hL]; omega
    have hcv : cvZ (zeckendorf n') =
        2 ^ (K - 3 - (zeckendorf n').length) + cvZ (zeckendorf n'') := by
      rw [← hQ', hz', cvZ_cons]
    rw [hQ'] at hc''
    rw [hcv, ← add_assoc, (a329320_top _ _ hc'').2, ih n'' (by omega), hz', W_cons_cons,
      ite_eq_left hKK]

/-- Kurkov's formula, for every `n ≥ 0`. -/
theorem kurkov_formula (n : ℕ) : a214973 n = a329320 (a048679 n) := by
  rw [a214973_eq_W, a048679_eq, CV_a003714, a329320_cvZ]

/-- **Kurkov's conjecture (A214973, 2021).** `a(n) = A329320(A048679(n))` for `n > 0`. -/
theorem kurkov_conjecture (n : ℕ) (_hn : 0 < n) : a214973 n = a329320 (a048679 n) :=
  kurkov_formula n

end FibLucas
