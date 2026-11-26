import LongCycleBounds.PartialFractions
import LongCycleBounds.DescentRows
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecificLimits.Normed

/-! Ordinary power series for Eulerian rows under the maximum-insertion recurrence. -/

noncomputable section
namespace LongCycleBounds

open Polynomial Set Filter
open scoped Topology

private theorem summable_shifted (m : ℕ) {r : ℝ} (hr : ‖r‖ < 1) (hr0 : r ≠ 0) :
    Summable fun n : ℕ ↦ ((n : ℝ)+1)^m * r^n := by
  have h := (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ)^m * r^n) 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one m hr)
  apply (h.mul_right r⁻¹).congr
  intro n
  push_cast
  rw [pow_succ]
  field_simp

def shiftedMoment (m : ℕ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ)+1)^m * y^n

private theorem hasDerivAt_shiftedMoment (m : ℕ) (t : ℝ) (ht : ‖t‖ < 1) :
    HasDerivAt (fun y ↦ y * shiftedMoment m y) (shiftedMoment (m+1) t) t := by
  obtain ⟨r, htr, hr⟩ := exists_between ht
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg t) htr
  have hs := summable_shifted (m+1) (r := r) (by simpa [Real.norm_eq_abs, abs_of_pos hr0])
    hr0.ne'
  let g (n : ℕ) (y : ℝ) := ((n : ℝ)+1)^m * y^(n+1)
  let g' (n : ℕ) (y : ℝ) := ((n : ℝ)+1)^(m+1) * y^n
  have hterm (n : ℕ) (y : ℝ) : HasDerivAt (g n) (g' n y) y := by
    convert! (hasDerivAt_pow (n+1) y).const_mul (((n : ℝ)+1)^m) using 1
    dsimp [g, g']
    simp only [Nat.cast_add, Nat.cast_one, pow_succ ((n : ℝ)+1)]
    ring
  have hz : (0 : ℝ) ∈ Metric.ball 0 r := by simpa using hr0
  have h0 : Summable (fun n ↦ g n 0) := by simp [g]
  have ht' : t ∈ Metric.ball (0 : ℝ) r := by simpa [Metric.mem_ball, dist_zero_right] using htr
  have hd := hasDerivAt_tsum_of_isPreconnected hs Metric.isOpen_ball
    (convex_ball (0 : ℝ) r).isPreconnected (fun n y _ ↦ hterm n y) (fun n y hy ↦ by
      have hnorm : ‖y‖ ≤ r := (by simpa [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < r).le
      simp only [g', norm_mul, norm_pow]
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ)+1)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (by positivity))
    hz h0 ht'
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro y
  change y * (∑' n : ℕ, ((n : ℝ)+1)^m * y^n) = ∑' n : ℕ, g n y
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [g, pow_succ]
  ring

/-- Evaluation identity for any real polynomial family with the Eulerian insertion recurrence. -/
theorem shiftedMoment_eq_eulerian (A : ℕ → ℝ[X]) (hzero : A 0 = 1)
    (hstep : ∀ m, A (m+1) = (1 + C (m : ℝ)*X) * A m + X*(1-X)*derivative (A m)) :
    ∀ m t, ‖t‖ < 1 → shiftedMoment m t = (A m).eval t / (1-t)^(m+1) := by
  intro m
  induction m with
  | zero =>
    intro t ht
    simp [shiftedMoment, hzero, tsum_geometric_of_norm_lt_one ht, one_div]
  | succ m ih =>
    intro t ht
    have hne : 1 - t ≠ 0 := sub_ne_zero.mpr (lt_of_le_of_lt (le_abs_self t) ht).ne'
    have hden : (1-t)^(m+1) ≠ 0 := pow_ne_zero _ hne
    have did : HasDerivAt (fun y : ℝ ↦ y) 1 t := hasDerivAt_id t
    have hbase : HasDerivAt (fun y : ℝ ↦ 1-y) (0-1) t := (hasDerivAt_const t 1).sub did
    have hrat := did.mul (((A m).hasDerivAt t).div (hbase.pow (m+1)) hden)
    have heq : (fun y ↦ y * shiftedMoment m y) =ᶠ[𝓝 t]
        (fun y ↦ y * ((A m).eval y / (1-y)^(m+1))) := by
      filter_upwards [continuous_norm.continuousAt.eventually_lt_const ht] with y hy
      rw [ih y hy]
    have hh := (hasDerivAt_shiftedMoment m t ht).congr_of_eventuallyEq heq.symm
    have hh' := hh.unique hrat
    rw [hh', hstep]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one, Nat.succ_sub_one,
      Nat.cast_add, Nat.cast_one, Pi.div_apply, Pi.pow_apply]
    rw [pow_succ (1-t) (m+1), pow_succ (1-t) m]
    field_simp
    ring

/-- The ordinary Eulerian rational function equals its power sum inside the unit disk
on the real axis. The polynomial is the descent enumerator of actual permutations. -/
theorem eulerian_eq_powerSeries (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : ‖t‖ < 1) :
    t * (LongCycles.eulerian m).eval t / (1-t)^(m+1) = ∑' n : ℕ, (n : ℝ)^m * t^n := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one m ht
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_pow (by omega : m ≠ 0), zero_mul, zero_add, Nat.cast_succ]
  rw [mul_div_assoc, ← shiftedMoment_eq_eulerian _ longEulerian_zero longEulerian_succ m t ht]
  change t * (∑' n : ℕ, ((n : ℝ)+1)^m * t^n) = _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pow_succ]
  ring

/-- The alternating real moment used in the discrete-maximum estimate. -/
theorem eulerian_eq_alternatingMoment (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 < x) :
    (-Real.exp (-x)) * (LongCycles.eulerian m).eval (-Real.exp (-x)) /
      (1 + Real.exp (-x))^(m+1) =
        ∑' h : ℕ, (-1 : ℝ)^h * h^m * Real.exp (-(x*(h : ℝ))) := by
  have ht : ‖-Real.exp (-x)‖ < 1 := by
    rw [norm_neg, Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have h := eulerian_eq_powerSeries m hm _ ht
  rw [sub_neg_eq_add] at h
  rw [h]
  apply tsum_congr
  intro h
  rw [show -(x*(h : ℝ)) = h * (-x) by ring, Real.exp_nat_mul,
    show -Real.exp (-x) = (-1) * Real.exp (-x) by ring, mul_pow]
  ring

/-- Odd-pole expansion, with the original Eulerian polynomial, at every positive parameter. -/
theorem eulerian_eq_oddPoleSum_of_pos (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 < x) :
    (((-Real.exp (-x)) * (LongCycles.eulerian m).eval (-Real.exp (-x)) /
      (1 + Real.exp (-x))^(m+1) : ℝ) : ℂ) = m.factorial * oddPoleSum (m+1) x := by
  have hn : ‖-Real.exp (-x)‖ < 1 := by
    rw [norm_neg, Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  rw [oddPoleSum_eq_powerSeries_of_pos m hm x hx]
  have h := congrArg (fun y : ℝ ↦ (y : ℂ)) (eulerian_eq_powerSeries m hm _ hn)
  simpa only [sub_neg_eq_add, Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_natCast] using h

/-- The complex odd-pole representation in the manuscript, including the central point t = -1. -/
theorem eulerian_eq_oddPoleSum (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 ≤ x) :
    (((-Real.exp (-x)) * (LongCycles.eulerian m).eval (-Real.exp (-x)) /
      (1 + Real.exp (-x))^(m+1) : ℝ) : ℂ) = m.factorial * oddPoleSum (m+1) x := by
  let f (y : ℝ) : ℂ := (((-Real.exp (-y)) * (LongCycles.eulerian m).eval (-Real.exp (-y)) /
    (1 + Real.exp (-y))^(m+1) : ℝ) : ℂ)
  let g (y : ℝ) : ℂ := m.factorial * oddPoleSum (m+1) y
  have he : EqOn f g (Ioi (0 : ℝ)) := fun y hy ↦ eulerian_eq_oddPoleSum_of_pos m hm y hy
  have hf : Continuous f := by
    dsimp [f]
    have hdn (y : ℝ) : (1 + Real.exp (-y))^(m+1) ≠ 0 := by positivity
    fun_prop (disch := exact hdn)
  have hg : Continuous g := continuous_const.mul (continuous_oddPoleSum _ (by omega))
  exact he.closure hf hg (by simpa [closure_Ioi] using hx)

#print axioms eulerian_eq_oddPoleSum
#print axioms eulerian_eq_alternatingMoment
#print axioms eulerian_eq_powerSeries
#print axioms eulerian_eq_oddPoleSum_of_pos

end LongCycleBounds
