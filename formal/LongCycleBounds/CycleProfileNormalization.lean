import LongCycleBounds.CycleProfile
import LongCycleBounds.MarkedInsertion

/-! Analytic coordinates for the true cycle-profile rows. -/

noncomputable section

namespace LongCycleBounds.CycleProfile

open Polynomial

/-- The weighted permutation row at \(t=-e^{-x}\), divided by \((1-t)^j\). -/
def normalizedRow (w : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (row j w).eval (MarkedTwo.time x) / (1 - MarkedTwo.time x) ^ j

theorem normalizedRow_zero {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    normalizedRow (profile k 0) j = Band.normalizedEnumerator j k := by
  funext x
  simp only [normalizedRow, row_zero j hk, MarkedTwo.time, Band.normalizedEnumerator]

theorem normalizedRow_one (k j : ℕ) :
    normalizedRow (profile k 1) j = Band.normalizedEnumerator j 2 := by
  funext x
  simp only [normalizedRow, row_one, MarkedTwo.time, Band.normalizedEnumerator]

/-- At a zero of the numerator, the normalization denominator makes no derivative term. -/
theorem normalized_deriv_at_zero {p : ℕ} (w : ℕ → ℝ) (x : ℝ)
    (hz : (row p w).eval (MarkedTwo.time x) = 0) :
    deriv (normalizedRow w p) x =
      -MarkedTwo.time x * (row p w).derivative.eval (MarkedTwo.time x) /
        (1 - MarkedTwo.time x) ^ p := by
  let t := MarkedTwo.time x
  have dt : HasDerivAt MarkedTwo.time (-t) x :=
    (((hasDerivAt_id x).neg.exp).neg).congr_deriv (by simp [t, MarkedTwo.time])
  have den : (1 - t) ^ p ≠ 0 := by
    simp only [t, MarkedTwo.time, sub_neg_eq_add]
    positivity
  have h := (((row p w).hasDerivAt t).comp x dt).div
    (((hasDerivAt_const x (1 : ℝ)).sub dt).pow p) den
  apply HasDerivAt.deriv
  apply h.congr_deriv
  change (_ * (-t) * (1 - t) ^ p - (row p w).eval t * _) / ((1 - t) ^ p) ^ 2 =
    (-t) * (row p w).derivative.eval t / (1 - t) ^ p
  rw [show (row p w).eval t = 0 from hz, zero_mul, sub_zero]
  field_simp

#print axioms normalizedRow_zero
#print axioms normalizedRow_one
#print axioms normalized_deriv_at_zero

end LongCycleBounds.CycleProfile
