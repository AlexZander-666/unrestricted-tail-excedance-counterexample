import LongCycleBounds.CycleProfileHomotopy
import LongCycleBounds.CycleProfileNormalization
import LongCycleBounds.LinearRootCoordinates

/-! Transfer of the half-axis sign criterion to the original adjacent permutation rows. -/

noncomputable section

namespace LongCycleBounds.CycleProfile

open Polynomial LongCycles LongCycleFinite Band Finset Real
open MarkedTwo (time)
open scoped Classical

/-- Reciprocity holds for arbitrary real cycle weights. Each one-cycle factor in the
anchored recurrence contributes its reciprocal identity at its own order. -/
theorem row_reciprocal (n : ℕ) (w : ℕ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    t ^ n * (row n w).eval t⁻¹ = (row n w).eval t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases z : n = 0
    · subst n
      simp only [pow_zero, one_mul]
      unfold row
      rw [Fintype.sum_unique]
      have e : (default : Equiv.Perm (Fin 0)) = 1 := Subsingleton.elim _ _
      simp [e, term, cycleWeight, excedances, Allowed]
    have formula := row_anchored (n := n) ⟨0, by omega⟩ w
    rw [formula]
    simp only [eval_finsetSum, mul_sum]
    apply sum_congr rfl
    intro a ha
    obtain ⟨lo, hi⟩ := mem_Icc.mp ha
    have er : t ^ (a - 2) * (eulerian (a - 1)).eval t⁻¹ = (eulerian (a - 1)).eval t := by
      simpa only [show a - 2 + 1 = a - 1 by omega] using eulerian_reciprocity (a - 2) ht
    have shorter := ih (n - a) (by omega)
    simp only [eval_mul, eval_C, eval_X]
    conv_lhs => arg 1; rw [show n = (a - 2) + 2 + (n - a) by omega, pow_add, pow_add]
    rw [← er, ← shorter]
    field_simp

theorem quotient_reciprocal {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {t : ℝ} (ht : t ≠ 0) :
    t ^ (n - 2) * (quotient n k u).eval t⁻¹ = (quotient n k u).eval t := by
  have h := row_reciprocal n (profile k u) ht
  rw [(quotient_shape hk hn hu).2.2.2] at h
  simp only [eval_mul, eval_X] at h
  conv_lhs at h => arg 1; rw [show n = n - 2 + 2 by omega, pow_add]
  have e : t ^ 2 * t⁻¹ = t := by field_simp
  apply mul_left_cancel₀ ht
  calc
    _ = (t ^ (n - 2) * t ^ 2) * (t⁻¹ * (quotient n k u).eval t⁻¹) := by
      linear_combination -(t ^ (n - 2) * (quotient n k u).eval t⁻¹) * e
    _ = _ := h

/-- Odd-sized rows have the center zero \(x=0\), corresponding to \(t=-1\). -/
theorem normalizedRow_center_zero {j : ℕ} (odd : Odd j) (w : ℕ → ℝ) :
    normalizedRow w j 0 = 0 := by
  have h := row_reciprocal j w (t := -1) (by norm_num)
  rw [odd.neg_one_pow, show (-1 : ℝ)⁻¹ = -1 by norm_num, neg_one_mul] at h
  have z : (row j w).eval (-1) = 0 := by linarith
  simp [normalizedRow, time, z]

/-- Reciprocity and differentiation at the true root transfer the half-axis sign
to every negative root of the predecessor quotient. -/
theorem quotient_root_sign {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1)
    (sign : ∀ x : ℝ, 0 ≤ x → normalizedRow (profile k u) (n - 1) x = 0 →
      0 < normalizedRow (profile k u) n x * (-deriv (normalizedRow (profile k u) (n - 1)) x))
    {t : ℝ} (ht : t < 0) (rt : (quotient (n - 1) k u).eval t = 0) :
    (quotient n k u).eval t * (quotient (n - 1) k u).derivative.eval t < 0 := by
  have hk2 : 2 ≤ k := by omega
  let P := quotient (n - 1) k u
  let Q := quotient n k u
  let D := n - 1 - 2
  have pR {v : ℝ} (hv : v ≠ 0) := quotient_reciprocal (n := n - 1) hk2 (by omega) hu hv
  have qR {v : ℝ} (hv : v ≠ 0) := quotient_reciprocal (n := n) hk2 hkn.le hu hv
  have unit (v : ℝ) (hv : v < 0) (left : -1 ≤ v) (z : P.eval v = 0) :
      Q.eval v * P.derivative.eval v < 0 := by
    let x := -log (-v)
    have hx : 0 ≤ x := neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))
    have coord : time x = v := by
      simp only [time, x, neg_neg, exp_log (show 0 < -v by linarith)]
    have hP : row (n - 1) (profile k u) = X * P := (quotient_shape hk2 (by omega) hu).2.2.2
    have hQ : row n (profile k u) = X * Q := (quotient_shape hk2 hkn.le hu).2.2.2
    have root : (row (n - 1) (profile k u)).eval (time x) = 0 := by
      rw [coord, hP, eval_mul, z, mul_zero]
    have out := sign x hx (by simp [normalizedRow, root])
    rw [normalized_deriv_at_zero (profile k u) x root] at out
    unfold normalizedRow at out
    rw [coord, hQ, hP, derivative_mul, derivative_X, one_mul] at out
    simp only [eval_add, eval_mul, eval_X, z, zero_add] at out
    have vp : 0 < 1 - v := by linarith
    by_contra! bad
    have scale : v ^ 3 / ((1 - v) ^ n * (1 - v) ^ (n - 1)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hv.le (sq_nonneg v)]
    have nonpos := mul_nonpos_of_nonpos_of_nonneg scale bad
    apply (not_lt_of_ge nonpos)
    exact out.trans_eq (by field_simp)
  by_cases l : -1 ≤ t
  · exact unit t ht l rt
  have qr : t ^ (D + 1) * Q.eval t⁻¹ = Q.eval t := by
    rw [show D + 1 = n - 2 by dsimp [D]; omega]
    exact qR ht.ne
  have ri : P.eval t⁻¹ = 0 :=
    (mul_eq_zero.mp ((pR ht.ne).trans rt)).resolve_left (pow_ne_zero _ ht.ne)
  have inside := unit t⁻¹ (inv_lt_zero.mpr ht)
    (by rw [inv_eq_one_div, le_div_iff_of_neg ht]; linarith) ri
  have pd := reciprocal_derivative_at_root P D (fun _ hv ↦ pR hv) ht.ne rt
  have e : t ^ 2 * (Q.eval t * P.derivative.eval t) =
      ((-t) * (t ^ D) ^ 2) * (Q.eval t⁻¹ * P.derivative.eval t⁻¹) := by
    rw [← qr, pow_succ]
    linear_combination (t ^ D * t * Q.eval t⁻¹) * pd
  exact neg_of_mul_neg_right (e.trans_lt (mul_neg_of_pos_of_neg
    (mul_pos (neg_pos.mpr ht) (sq_pos_of_ne_zero (pow_ne_zero _ ht.ne))) inside)) (sq_nonneg t)

/-- At any fixed pair, the half-axis estimate along the deformation proves interlacing
for every short-cycle weight in the interval. -/
theorem interlacing_of_normalized_sign {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n)
    (sign : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, 0 ≤ x →
      normalizedRow (profile k u) (n - 1) x = 0 →
      0 < normalizedRow (profile k u) n x * (-deriv (normalizedRow (profile k u) (n - 1)) x)) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      StrictNegativeInterlacing (quotient (n - 1) k u) (quotient n k u) (n - 3) ∧
        WeakRealInterlacing (row (n - 1) (profile k u)) (row n (profile k u)) :=
  interlacing_of_sign hk hkn fun u hu _ ht hz ↦ quotient_root_sign hk hkn hu (sign u hu) ht hz

/-- A single pairwise half-axis sign estimate along \(u\in[0,1]\) implies the
strict quotient and weak original interlacing results at the cutoff \(k\). -/
theorem original_of_normalized_sign {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n)
    (sign : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, 0 ≤ x →
      normalizedRow (profile k u) (n - 1) x = 0 →
      0 < normalizedRow (profile k u) n x * (-deriv (normalizedRow (profile k u) (n - 1)) x)) :
    StrictNegativeInterlacing (generalCycleQuotient (n - 1) k) (generalCycleQuotient n k) (n - 3) ∧
      WeakRealInterlacing (enumerator (n - 1) k) (enumerator n k) := by
  have hk2 : 2 ≤ k := by omega
  simpa only [(quotient_endpoints hk2 (by omega : 0 < n - 1)).1,
    (quotient_endpoints hk2 (by omega : 0 < n)).1, row_zero _ hk2] using
    interlacing_of_normalized_sign hk hkn sign 0 (by norm_num)

#print axioms row_reciprocal
#print axioms quotient_reciprocal
#print axioms normalizedRow_center_zero
#print axioms quotient_root_sign
#print axioms interlacing_of_normalized_sign
#print axioms original_of_normalized_sign

end LongCycleBounds.CycleProfile
