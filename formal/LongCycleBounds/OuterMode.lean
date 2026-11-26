import LongCycleBounds.EulerianSeries
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Positive-label moments, their mode, and quantitative ratio decay in the outer region.
The array index j represents the positive label j+1. -/

noncomputable section

namespace LongCycleBounds.Outer

def weight (N : ℕ) (x : ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ)+1)^N * Real.exp (-x)^(j+1)

def ratio (N : ℕ) (x : ℝ) (j : ℕ) : ℝ :=
  (1 + 1 / ((j : ℝ)+1))^N * Real.exp (-x)

theorem weight_pos (N : ℕ) (x : ℝ) (j : ℕ) : 0 < weight N x j := by
  unfold weight
  positivity

theorem ratio_pos (N : ℕ) (x : ℝ) (j : ℕ) : 0 < ratio N x j := by
  unfold ratio
  positivity

theorem weight_succ (N : ℕ) (x : ℝ) (j : ℕ) :
    weight N x (j+1) = ratio N x j * weight N x j := by
  unfold weight ratio
  push_cast
  have hz : (j : ℝ)+1 ≠ 0 := by positivity
  have h : (1 + 1/((j : ℝ)+1)) * (j+1) = j+1+1 := by field_simp
  rw [show (Real.exp (-x))^(j+1+1) = Real.exp (-x)^(j+1)*Real.exp (-x) by rw [pow_succ _ (j+1)]]
  rw [← h, mul_pow]
  ring

theorem ratio_antitone (N : ℕ) (x : ℝ) : Antitone (ratio N x) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  have hab' : (a : ℝ)+1 ≤ (b : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hab 1
  exact add_le_add_right (one_div_le_one_div_of_le (by positivity) hab') 1

theorem ratio_le_exp (N : ℕ) (x : ℝ) (j : ℕ) :
    ratio N x j ≤ Real.exp ((N : ℝ)/((j : ℝ)+1) - x) := by
  rw [sub_eq_add_neg, Real.exp_add, div_eq_mul_one_div, Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  linarith [Real.add_one_le_exp (1/((j : ℝ)+1))]

private theorem exists_cross (N : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ j : ℕ, ratio N x j ≤ 1 := by
  obtain ⟨j, hj⟩ := exists_nat_gt ((N : ℝ)/x)
  refine ⟨j, (ratio_le_exp ..).trans (Real.exp_le_one_iff.mpr ?_)⟩
  apply sub_nonpos.mpr
  apply (div_le_iff₀ (by positivity : 0 < (j : ℝ)+1)).mpr
  have := (div_lt_iff₀ hx).mp hj
  nlinarith

/-- The selected mode is the first place where the adjacent ratio drops to one or below. -/
def mode (N : ℕ) (x : ℝ) (hx : 0 < x) : ℕ := Nat.find (exists_cross N x hx)

theorem ratio_mode_le (N : ℕ) (x : ℝ) (hx : 0 < x) : ratio N x (mode N x hx) ≤ 1 :=
  Nat.find_spec (exists_cross N x hx)

theorem one_lt_ratio_before (N : ℕ) (x : ℝ) (hx : 0 < x) {j : ℕ} (hj : j < mode N x hx) :
    1 < ratio N x j := lt_of_not_ge (Nat.find_min (exists_cross N x hx) hj)

theorem mode_index_mul_le (N : ℕ) (x : ℝ) (hx : 0 < x) :
    (mode N x hx : ℝ)*x ≤ N := by
  generalize he : mode N x hx = m
  cases m with
  | zero => simp
  | succ i =>
    have h := one_lt_ratio_before N x hx (j := i) (by omega)
    have hg := (Real.one_lt_exp_iff.mp (h.trans_le (ratio_le_exp ..)))
    have hh := (lt_div_iff₀ (by positivity : 0 < (i : ℝ)+1)).mp (sub_pos.mp hg)
    push_cast
    linarith

theorem weight_inc_before (N : ℕ) (x : ℝ) (hx : 0 < x) {j : ℕ}
    (hj : j < mode N x hx) : weight N x j ≤ weight N x (j+1) := by
  rw [weight_succ]
  exact le_mul_of_one_le_left (weight_pos ..).le (one_lt_ratio_before N x hx hj).le

theorem weight_dec_after (N : ℕ) (x : ℝ) (hx : 0 < x) {j : ℕ}
    (hj : mode N x hx ≤ j) : weight N x (j+1) ≤ weight N x j := by
  rw [weight_succ]
  exact mul_le_of_le_one_left (weight_pos ..).le ((ratio_antitone N x hj).trans (ratio_mode_le ..))

theorem weight_le_mode (N : ℕ) (x : ℝ) (hx : 0 < x) (j : ℕ) :
    weight N x j ≤ weight N x (mode N x hx) := by
  rcases le_total j (mode N x hx) with h | h
  · have aux (l : ℕ) (hjl : j ≤ l) (hl : l ≤ mode N x hx) :
        weight N x j ≤ weight N x l := by
      induction l with
      | zero =>
        obtain rfl : j = 0 := by omega
        exact le_rfl
      | succ l ih =>
        rcases Nat.eq_or_lt_of_le hjl with he | hh
        · rw [he]
        · exact (ih (by omega) (by omega)).trans (weight_inc_before N x hx (by omega))
    exact aux _ h le_rfl
  · exact (monotoneOn_nat_Ici_of_le_succ (α := OrderDual ℝ)
      (f := weight N x) (fun _ hi ↦ weight_dec_after N x hx hi)) (show mode N x hx ≤ _ from le_rfl)
      h h

/-- The peak and its next ratio index are within half a square root. -/
theorem mode_add_two_le_half_sqrt (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) : (mode N x hx : ℝ)+2 ≤ Real.sqrt N/2 := by
  have hroot : 20 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hN
  have hsq := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  have hi := mode_index_mul_le N x hx
  have hbound := mul_le_mul_of_nonneg_left hregion (Nat.cast_nonneg (mode N x hx))
  by_contra! bad
  nlinarith [mul_nonneg (sub_nonneg.mpr bad.le) (show 0 ≤ Real.sqrt (N : ℝ) by positivity)]

theorem ratio_succ_eq (N : ℕ) (x : ℝ) (j : ℕ) :
    ratio N x (j+1) = (1 - 1/((j : ℝ)+2)^2)^N * ratio N x j := by
  unfold ratio
  push_cast
  rw [← mul_assoc, ← mul_pow]
  congr 2
  field_simp
  ring

private theorem exp_neg_four_lt : Real.exp (-4) < 1/50 := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  have hh : (27/10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ hh (by norm_num : (0:ℝ) ≤ 27/10) (by decide : 4 ≠ 0)
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

/-- A quantitative bound on the factor between adjacent ratios before and at the mode. -/
theorem ratio_contracts (N : ℕ) (x : ℝ) (j : ℕ)
    (hj : (j : ℝ)+2 ≤ Real.sqrt N/2) :
    ratio N x (j+1) ≤ (1/50 : ℝ) * ratio N x j := by
  rw [ratio_succ_eq]
  apply mul_le_mul_of_nonneg_right _ (ratio_pos ..).le
  let a := 1 / ((j : ℝ)+2)^2
  have ha : 0 ≤ 1-a := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity : 0 < ((j : ℝ)+2)^2)).mpr (by nlinarith [sq_nonneg (j : ℝ)])
  have he : 1-a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  apply (pow_le_pow_left₀ ha he N).trans
  rw [← Real.exp_nat_mul]
  apply le_trans _ exp_neg_four_lt.le
  apply Real.exp_le_exp.mpr
  have hs := sq_le_sq' (by linarith [Real.sqrt_nonneg (N : ℝ)] :
      -(Real.sqrt N/2) ≤ (j : ℝ)+2) hj
  have hN := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  have h : 4 ≤ (N : ℝ) / ((j : ℝ)+2)^2 := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  dsimp [a]
  linarith [show (N : ℝ)*(1 / ((j : ℝ)+2)^2) = N/((j : ℝ)+2)^2 by ring]

end LongCycleBounds.Outer
