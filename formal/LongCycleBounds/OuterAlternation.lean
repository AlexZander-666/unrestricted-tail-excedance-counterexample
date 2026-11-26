import LongCycleBounds.OuterMode

/-! A variation proof of the sharp alternating-sum bound at the actual mode. -/

noncomputable section
namespace LongCycleBounds.Outer

open Finset Filter
open scoped Topology

private theorem signed_telescope (f : ℕ → ℝ) (l : ℕ) :
    2 * (∑ j ∈ range l, (-1 : ℝ)^j * f j) =
      f 0 - (-1 : ℝ)^l * f l + ∑ j ∈ range l, (-1 : ℝ)^j * (f j - f (j+1)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [sum_range_succ, mul_add, pow_succ, ih]
    ring

private theorem variation (f : ℕ → ℝ) (m l : ℕ) (hml : m ≤ l)
    (up : ∀ j < m, f j ≤ f (j+1)) (down : ∀ j ≥ m, f (j+1) ≤ f j) :
    ∑ j ∈ range l, |f (j+1)-f j| = 2*f m - f l - f 0 := by
  let V (j : ℕ) := if j ≤ m then f j else 2*f m - f j
  have he (j : ℕ) : |f (j+1)-f j| = V (j+1)-V j := by
    by_cases hj : j < m
    · simp [V, Nat.succ_le_iff.mpr hj, hj.le, abs_of_nonneg (sub_nonneg.mpr (up _ hj))]
    · have h := abs_of_nonpos (sub_nonpos.mpr (down _ (by omega : m ≤ j)))
      rcases eq_or_lt_of_le (by omega : m ≤ j) with he | hlt
      · subst j
        simp [V, h]
        ring
      · simp [V, h, not_le.mpr hlt, show ¬ j+1 ≤ m by omega]
  simp_rw [he]
  rw [Finset.sum_range_sub]
  by_cases hl : l = m
  · simp [V, hl]
    ring
  · simp [V, show ¬l ≤ m by omega]

/-- For an absolutely convergent alternating weighting of a nonnegative unimodal sequence
the absolute sum is bounded by the actual mode, with constant one. -/
theorem alternating_tsum_le_mode (f : ℕ → ℝ) (m : ℕ) (hf : ∀ n, 0 ≤ f n)
    (up : ∀ j < m, f j ≤ f (j+1)) (down : ∀ j ≥ m, f (j+1) ≤ f j)
    (hs : Summable (fun n ↦ (-1 : ℝ)^n * f n)) :
    |∑' n : ℕ, (-1 : ℝ)^n * f n| ≤ f m := by
  apply le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hs.hasSum.tendsto_sum_nat)
  filter_upwards [eventually_ge_atTop m] with l hl
  change |∑ j ∈ range l, (-1 : ℝ)^j*f j| ≤ f m
  have hv := variation f m l hl up down
  have ht := signed_telescope f l
  have htri := abs_add_le (f 0-(-1 : ℝ)^l*f l)
    (∑ j ∈ range l, (-1 : ℝ)^j * (f j-f (j+1)))
  rw [← ht, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at htri
  have h₁ := abs_sub (f 0) ((-1 : ℝ)^l * f l)
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (hf 0),
    abs_of_nonneg (hf l)] at h₁
  have h₂ := Finset.abs_sum_le_sum_abs (fun j : ℕ ↦ (-1 : ℝ)^j*(f j-f (j+1))) (range l)
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h₂
  simp_rw [abs_sub_comm (f _) (f (_+1))] at h₂
  linarith

theorem summable_weight (N : ℕ) (x : ℝ) (hx : 0 < x) : Summable (weight N x) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one N (r := Real.exp (-x)) (by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith)
  apply ((summable_nat_add_iff (f := fun j : ℕ ↦ (j : ℝ)^N * Real.exp (-x)^j) 1).mpr h).congr
  intro j
  simp [weight]

theorem summable_signed_weight (N : ℕ) (x : ℝ) (hx : 0 < x) :
    Summable fun j : ℕ ↦ (-1 : ℝ)^j * weight N x j := by
  apply (summable_weight N x hx).of_norm_bounded
  intro j
  simp [Real.norm_eq_abs, abs_of_pos (weight_pos ..)]

theorem signed_weight_bound (N : ℕ) (x : ℝ) (hx : 0 < x) :
    |∑' j : ℕ, (-1 : ℝ)^j * weight N x j| ≤ weight N x (mode N x hx) := by
  apply alternating_tsum_le_mode
  · exact fun j ↦ (weight_pos ..).le
  · exact fun j hj ↦ weight_inc_before N x hx hj
  · exact fun j hj ↦ weight_dec_after N x hx hj
  · exact summable_signed_weight N x hx

/-- Doubling the positive label produces exactly the square needed at the first split. -/
theorem doubled_weight (b : ℕ) (x : ℝ) (j : ℕ) :
    (2 : ℝ)^(2*b) * weight b x j ^ 2 = weight (2*b) x (2*j+1) := by
  unfold weight
  push_cast
  rw [show (2:ℝ)*j+1+1 = 2*(j+1) by ring, show 2*b = b*2 by omega,
    mul_pow 2 ((j : ℝ)+1) (b*2), pow_mul ((j : ℝ)+1) b 2,
    show 2*j+1+1 = (j+1)*2 by omega, pow_mul (Real.exp (-x)) (j+1) 2]
  ring

theorem first_split_numerator (b : ℕ) (x : ℝ) (hx : 0 < x) :
    (2 : ℝ)^(2*b) * (∑' j : ℕ, (-1 : ℝ)^j * weight b x j)^2 ≤
      weight (2*b) x (mode (2*b) x hx) := by
  have h := signed_weight_bound b x hx
  have hs : (∑' j : ℕ, (-1 : ℝ)^j * weight b x j)^2 ≤ weight b x (mode b x hx)^2 :=
    sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans
    ((doubled_weight b x (mode b x hx)).le.trans (weight_le_mode ..))

/-- Literal square-root form of the numerator. Array index 2j+1 is positive label 2(j+1). -/
theorem alternating_sqrt_even_bound (b : ℕ) (x : ℝ) (hx : 0 < x) :
    (∑' j : ℕ, (-1 : ℝ)^j * Real.sqrt (weight (2*b) x (2*j+1)))^2 ≤
      weight (2*b) x (mode (2*b) x hx) := by
  have he (j : ℕ) : Real.sqrt (weight (2*b) x (2*j+1)) = 2^b * weight b x j := by
    rw [← doubled_weight, show 2*b = b*2 by omega, pow_mul, ← mul_pow, Real.sqrt_sq]
    exact mul_nonneg (by positivity) (weight_pos ..).le
  simp_rw [he, show ∀ j : ℕ, (-1 : ℝ)^j*(2^b*weight b x j) =
      2^b*((-1 : ℝ)^j*weight b x j) from fun j ↦ by ring]
  rw [tsum_mul_left, mul_pow, ← pow_mul, Nat.mul_comm b 2]
  exact first_split_numerator b x hx

#print axioms alternating_sqrt_even_bound
end LongCycleBounds.Outer
