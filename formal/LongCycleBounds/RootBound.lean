import LongCycleBounds.Reciprocity
import LongCycleBounds.EulerianBulk
import LongCycleBounds.OuterLow

namespace LongCycleBounds
open LongCycles Polynomial
noncomputable section

private theorem firstSplitUnitBound (k : ℕ) (hk : 55 ≤ k) (t : ℝ) (hlo : -1 ≤ t) (ht : t < 0)
    (hz : (eulerian (2*k-2)).eval t = 0) :
    ((2*k).choose k : ℝ)/2 * |t| * ((eulerian (k-1)).eval t)^2 < |(eulerian (2*k-1)).eval t| := by
  let x := -Real.log (-t)
  have hp : 0 < -t := by linarith
  have hx : 0 ≤ x := neg_nonneg.mpr (Real.log_nonpos hp.le (by linarith))
  have he : Real.exp (-x) = -t := by simpa [x] using Real.exp_log hp
  have he' : -Real.exp (-x) = t := by rw [he, neg_neg]
  have hzt : (eulerian (2*k-2)).eval (-Real.exp (-x)) = 0 := he' ▸ hz
  have ans := (le_total x (5/2 * Real.sqrt (2*k-2 : ℕ))).elim
    (fun h ↦ firstSplitBulkBound55 k hk x hx h hzt) (fun h ↦ firstSplitOuterBound51 k (by omega) x h hzt)
  rwa [he', he, ← abs_of_neg ht] at ans

private theorem reciprocal_shift (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : t ≠ 0) :
    t^(m-1) * (eulerian m).eval t⁻¹ = (eulerian m).eval t := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact eulerian_reciprocity n ht

/-- Strict dominance of the adjacent Eulerian row at every negative root of the lower row. -/
theorem firstSplitRootBound55 (k : ℕ) (hk : 55 ≤ k) {t : ℝ} (ht : t < 0)
    (hz : (eulerian (2*k-2)).eval t = 0) :
    ((2*k).choose k : ℝ)/2 * |t| * ((eulerian (k-1)).eval t)^2 < |(eulerian (2*k-1)).eval t| := by
  by_cases hlo : -1 ≤ t
  · exact firstSplitUnitBound k hk t hlo ht hz
  have hi : t⁻¹ < 0 := inv_lt_zero.mpr ht
  have hil : -1 ≤ t⁻¹ := by
    rw [inv_eq_one_div, le_div_iff_of_neg ht]
    linarith
  have ht0 := ht.ne
  have z := reciprocal_shift (2*k-2) (by omega) ht0
  rw [hz] at z
  have zi := (mul_eq_zero.mp z).resolve_left (pow_ne_zero _ ht0)
  have h := firstSplitUnitBound k hk _ hil hi zi
  let a := (eulerian (k-1)).eval t⁻¹
  have ka : k-1-1=k-2 := by omega
  have kb : 2*k-1-1=2*k-2 := by omega
  have ar := congrArg abs (reciprocal_shift (k-1) (by omega) ht0)
  have br := congrArg abs (reciprocal_shift (2*k-1) (by omega) ht0)
  rw [abs_mul,abs_pow,ka] at ar
  rw [abs_mul,abs_pow,kb] at br
  have sq : ((eulerian (k-1)).eval t)^2 = |t|^((k-2)*2) * a^2 := by
    rw [← sq_abs, ← ar, mul_pow, sq_abs, pow_mul]
  rw [sq, ← br]
  have pos := pow_pos (abs_pos.mpr ht0) (2*k-2)
  have scale := mul_lt_mul_of_pos_left h pos
  rw [abs_inv] at scale
  refine lt_of_eq_of_lt ?_ scale
  have ex : 2*k-2=(k-2)*2+2 := by omega
  rw [ex,pow_add]
  dsimp [a]
  field_simp [abs_ne_zero.mpr ht0]

theorem firstSplitRootBound (k : ℕ) (hk : 201 ≤ k) {t : ℝ} (ht : t < 0)
    (hz : (eulerian (2*k-2)).eval t = 0) :
    ((2*k).choose k : ℝ)/2 * |t| * ((eulerian (k-1)).eval t)^2 < |(eulerian (2*k-1)).eval t| := by
  exact firstSplitRootBound55 k (by omega) ht hz

/-- The corrected row and the adjacent Eulerian row have identical signs at all lower roots. -/
theorem firstSplit_sameSign55 (k : ℕ) (hk : 55 ≤ k) {t : ℝ} (ht : t < 0)
    (hz : (eulerian (2*k-2)).eval t = 0) :
    0 < (eulerian (2*k-1)).eval t *
      ((eulerian (2*k-1)).eval t + ((2*k).choose k:ℝ)/2*t*((eulerian (k-1)).eval t)^2) := by
  have bound := firstSplitRootBound55 k hk ht hz
  rw [abs_of_neg ht] at bound
  rcases le_or_gt 0 ((eulerian (2*k-1)).eval t) with hb|hb
  · rw [abs_of_nonneg hb] at bound
    have corr : 0 ≤ ((2*k).choose k:ℝ)/2*(-t)*((eulerian (k-1)).eval t)^2 := mul_nonneg (mul_nonneg (by positivity) (neg_nonneg.mpr ht.le)) (sq_nonneg _)
    exact mul_pos (corr.trans_lt bound) (by linarith)
  · apply mul_pos_of_neg_of_neg hb
    have corr : ((2*k).choose k:ℝ)/2*t*((eulerian (k-1)).eval t)^2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht.le) (sq_nonneg _)
    linarith

theorem firstSplit_sameSign (k : ℕ) (hk : 201 ≤ k) {t : ℝ} (ht : t < 0)
    (hz : (eulerian (2*k-2)).eval t = 0) :
    0 < (eulerian (2*k-1)).eval t *
      ((eulerian (2*k-1)).eval t + ((2*k).choose k:ℝ)/2*t*((eulerian (k-1)).eval t)^2) := by
  exact firstSplit_sameSign55 k (by omega) ht hz

#print axioms firstSplitRootBound
#print axioms firstSplit_sameSign
end
end LongCycleBounds
