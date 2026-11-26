import LongCycleBounds.RootBound
import LongCycleFinite.CoefficientRows

namespace LongCycleBounds
open LongCycles LongCycleFinite Polynomial
noncomputable section

/-- The unordered supports coefficient of the original permutation count. -/
theorem chooseHalf_cast (k : ℕ) (hk : 0 < k) :
    (((2*k).choose k / 2 : ℕ) : ℝ) = ((2*k).choose k : ℝ)/2 := by
  have hd : 2 ∣ (2*k).choose k := Nat.two_dvd_centralBinom_of_one_le hk
  apply (eq_div_iff (by norm_num : (2:ℝ) ≠ 0)).mpr
  exact_mod_cast Nat.div_mul_cancel hd

theorem firstQ_sameSign55 (k : ℕ) (hk : 55 ≤ k) {t : ℝ} (ht : t < 0)
    (hz : (firstP k).eval t = 0) :
    0 < (eulerian (2*k-1)).eval t * (firstQ k).eval t := by
  simpa only [firstQ, eval_add,eval_mul,eval_C,eval_X,eval_pow,chooseHalf_cast k (by omega)]
    using firstSplit_sameSign55 k hk ht hz

theorem firstQ_sameSign (k : ℕ) (hk : 201 ≤ k) {t : ℝ} (ht : t < 0)
    (hz : (firstP k).eval t = 0) :
    0 < (eulerian (2*k-1)).eval t * (firstQ k).eval t := by
  exact firstQ_sameSign55 k (by omega) ht hz

private theorem eulerian_eval_pos (m : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (eulerian m).eval t := by
  classical
  simp only [eulerian,eval_finsetSum,eval_pow,eval_X]
  exact Finset.sum_pos (fun _ _ ↦ pow_pos ht _) Finset.univ_nonempty

/-- The two original enumerators have precisely one common real root for every k ≥ 201. -/
theorem common_real_root_iff (k : ℕ) (hk : 201 ≤ k) (t : ℝ) :
    (enumerator (2*k-1) k).eval t = 0 ∧ (enumerator (2*k) k).eval t = 0 ↔ t = 0 := by
  obtain ⟨hl,hu⟩ := firstSplit_quotients k (by omega)
  rw [hl,hu,eval_mul,eval_mul,eval_X]
  constructor
  · intro ⟨hp,hq⟩
    by_contra hn
    have pz := (mul_eq_zero.mp hp).resolve_left hn
    have qz := (mul_eq_zero.mp hq).resolve_left hn
    rcases lt_or_gt_of_ne hn with ht|ht
    · have h := firstQ_sameSign k hk ht pz
      simp [qz] at h
    · exact (eulerian_eval_pos (2*k-2) ht).ne' pz
  · rintro rfl
    simp

#print axioms chooseHalf_cast
#print axioms firstQ_sameSign
#print axioms common_real_root_iff
end
end LongCycleBounds
