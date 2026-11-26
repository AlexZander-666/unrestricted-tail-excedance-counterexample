import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Fourier expansion of the odd pole lattice in the Eulerian normalization. -/

noncomputable section

namespace LongCycleBounds

open Complex
open scoped Real

/-- The real-axis evaluation of the odd complex pole lattice. -/
def oddPoleSum (p : ℕ) (x : ℝ) : ℂ :=
  ∑' l : ℤ, 1 / ((x : ℂ) + (2 * (l : ℂ) + 1) * π * I) ^ p

private def shiftedPoint (x : ℝ) (hx : 0 < x) : UpperHalfPlane :=
  ⟨-(1 / 2 : ℂ) + ((x / (2 * π) : ℝ) : ℂ) * I, by
    rw [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re]
    norm_num
    positivity⟩

private theorem shiftedPoint_exp (x : ℝ) (hx : 0 < x) :
    Complex.exp (2 * π * I * (shiftedPoint x hx : ℂ)) = -((Real.exp (-x) : ℝ) : ℂ) := by
  have h : 2 * (π : ℂ) * I * (shiftedPoint x hx : ℂ) = -(π * I) + ↑(-x : ℝ) := by
    change _ * (-(1 / 2 : ℂ) + _ * I) = _
    push_cast
    have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    linear_combination (x : ℂ) * (Complex.I_mul_I)
  rw [h, Complex.exp_add, Complex.exp_neg_pi_mul_I, Complex.ofReal_exp]
  ring

/-- For positive x the Fourier series of the negative geometric parameter equals the pole sum
with precisely the factorial in the Eulerian partial fraction formula. -/
theorem oddPoleSum_eq_powerSeries_of_pos (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 < x) :
    (m.factorial : ℂ) * oddPoleSum (m+1) x =
      ∑' h : ℕ, (h : ℂ)^m * (-((Real.exp (-x) : ℝ) : ℂ))^h := by
  let z := shiftedPoint x hx
  let a : ℂ := -2 * π * I
  have ha : a ≠ 0 := by simp [a, Real.pi_ne_zero, Complex.I_ne_zero]
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hv (l : ℤ) : a * ((z : ℂ) + (-l : ℤ)) =
      (x : ℂ) + (2 * (l : ℂ) + 1) * π * I := by
    change (-2 * (π : ℂ) * I) * (-(1 / 2 : ℂ) + _ * I + _) = _
    push_cast
    field_simp
    linear_combination -(x : ℂ) * Complex.I_mul_I
  have hs : oddPoleSum (m+1) x =
      (a^(m+1))⁻¹ * ∑' l : ℤ, 1 / ((z : ℂ) + l) ^ (m+1) := by
    rw [oddPoleSum, ← tsum_mul_left, ← tsum_comp_neg (fun l : ℤ ↦
      (a^(m+1))⁻¹ * (1 / ((z : ℂ) + l) ^ (m+1)))]
    apply tsum_congr
    intro l
    rw [← hv, mul_pow]
    simp [div_eq_mul_inv, mul_comm]
  rw [hs, EisensteinSeries.qExpansion_identity hm z, show
      Complex.exp (2 * π * I * (z : ℂ)) = _ from shiftedPoint_exp x hx]
  change _ * (_ * (a^(m+1) / _ * _)) = _
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp

/-- A uniform majorant also controls the boundary point x = 0. -/
theorem continuous_oddPoleSum (p : ℕ) (hp : 2 ≤ p) : Continuous (oddPoleSum p) := by
  have hden (l : ℤ) : (l : ℝ) + 1/2 ≠ 0 := by
    have ho : (2*l+1 : ℤ) ≠ 0 := by omega
    have ho' : (2*(l : ℝ)+1) ≠ 0 := by exact_mod_cast ho
    contrapose! ho'
    linarith
  have hnorm (l : ℤ) (x : ℝ) :
      |(l : ℝ) + 1/2| ≤ ‖(x : ℂ) + (2 * (l : ℂ) + 1) * π * I‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_I_im]
    have hh : (2 * (l : ℂ) + 1) * (π : ℂ) = (((2 * (l : ℝ) + 1) * π : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hh, Complex.ofReal_re, show (2*(l : ℝ)+1)*π = ((l : ℝ)+1/2)*(2*π) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < 2*π)]
    exact le_mul_of_one_le_right (abs_nonneg _) (by linarith [Real.pi_gt_three])
  have hs : Summable (fun l : ℤ ↦ 1 / |(l : ℝ) + 1/2| ^ p) := by
    simpa using (Real.summable_one_div_int_add_rpow (1/2) (p : ℝ)).mpr (by exact_mod_cast
      (show 1 < p by omega))
  apply continuous_tsum (u := fun l : ℤ ↦ 1 / |(l : ℝ)+1/2|^p) _ hs
  · intro l x
    simp only [norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le (pow_pos (abs_pos.mpr (hden l)) _) <|
      pow_le_pow_left₀ (abs_nonneg _) (hnorm l x) p
  · intro l
    have hz (x : ℝ) : (x : ℂ) + (2 * (l : ℂ) + 1) * π * I ≠ 0 := by
      exact norm_pos_iff.mp (lt_of_lt_of_le (abs_pos.mpr (hden l)) (hnorm l x))
    exact continuous_const.div ((Complex.continuous_ofReal.add continuous_const).pow p)
      (fun x ↦ pow_ne_zero _ (hz x))

#print axioms continuous_oddPoleSum
#print axioms oddPoleSum_eq_powerSeries_of_pos

end LongCycleBounds
