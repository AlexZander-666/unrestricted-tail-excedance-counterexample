import LongCycleBounds.OuterMoments
import LongCycleBounds

/-! Exact comparison of the first two-cycle correction with the single-cycle term
at Eulerian roots in the outer real region. -/
noncomputable section
namespace LongCycleBounds

open Outer

/-- Positive-label normalization, with the sign of the alternating series shifted by one. -/
theorem outerMoment_eq_evaluation (j : ℕ) (x : ℝ) (hx : 0 < x) :
    moment j x = Real.exp (-x) * (LongCycles.eulerian j).eval (-Real.exp (-x)) /
      (1+Real.exp (-x))^(j+1) := by
  let u := Real.exp (-x)
  have ht : ‖-u‖ < 1 := by
    change |-Real.exp (-x)| < 1
    rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have h := shiftedMoment_eq_eulerian _ longEulerian_zero longEulerian_succ j (-u) ht
  rw [sub_neg_eq_add] at h
  change _ = u * _ / _
  rw [mul_div_assoc, ← h]
  unfold moment shiftedMoment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold weight
  change (-1 : ℝ)^n * (((n : ℝ)+1)^j * u^(n+1)) =
    u * (((n : ℝ)+1)^j * (-u)^n)
  rw [show -u = (-1)*u by ring, mul_pow, pow_succ u n]
  ring

private theorem coefficient_lt (k : ℕ) (hk : 5 ≤ k) :
    ((2*k).choose k : ℝ) < (2 : ℝ)^(2*k-2) := by
  have h := tail_normalization k (by omega)
  rw [Nat.centralBinom_eq_two_mul_choose, ← mul_div_assoc, div_lt_one (by positivity)] at h
  have hr : 4*((2*k).choose k : ℝ) < (4:ℝ)^k := by exact_mod_cast h
  have pw : (2 : ℝ)^(2*k-2)*4 = 4^k := by
    calc
      _ = (2:ℝ)^((2*k-2)+2) := by rw [pow_add]; ring
      _ = (2:ℝ)^(2*k) := by congr 1; omega
      _ = 4^k := by rw [pow_mul]; norm_num
  linarith

private theorem unscale {u v c a b : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : c*(u*a/v)^2 < |u*b/v^2|) : c*u*a^2 < |b| := by
  rw [div_pow, ← mul_div_assoc, abs_div, abs_mul, abs_of_pos hu, abs_of_pos (sq_pos_of_pos hv),
    div_lt_div_iff_of_pos_right (sq_pos_of_pos hv)] at h
  exact (mul_lt_mul_iff_right₀ hu).mp (by linarith only [show c*(u*a)^2 = u*(c*u*a^2) by ring, h])

/-- Outer-region counterpart to firstSplitBulkBound, with the same source-polynomial conventions. -/
theorem firstSplitOuter_of_derivative (k : ℕ) (hk : 5 ≤ k) (x : ℝ) (hx' : 0 < x)
    (hder : moment (2*k-2) x = 0 →
      weight (2*k-2) x (mode (2*k-2) x hx')/2 < |moment ((2*k-2)+1) x|)
    (zero : (LongCycles.eulerian (2*k-2)).eval (-Real.exp (-x)) = 0) :
    ((2*k).choose k : ℝ)/2 * Real.exp (-x) *
        ((LongCycles.eulerian (k-1)).eval (-Real.exp (-x)))^2 <
      |(LongCycles.eulerian (2*k-1)).eval (-Real.exp (-x))| := by
  let N := 2*k-2
  let b := k-1
  let c : ℝ := ((2*k).choose k : ℝ)/2
  let u := Real.exp (-x)
  have hu : 0 < u := Real.exp_pos _
  have hzero : moment N x = 0 := by rw [outerMoment_eq_evaluation _ _ hx', zero]; simp
  have den := hder hzero
  have num := first_split_numerator b x hx'
  have hindex : 2*b = N := by dsimp [b,N]; omega
  rw [hindex] at num
  have cn : 2*c ≤ (2 : ℝ)^N := by
    dsimp [c, N]
    linarith [coefficient_lt k hk]
  have cmp : c * (moment b x)^2 < |moment (N+1) x| := by
    change (2:ℝ)^N * (moment b x)^2 ≤ _ at num
    nlinarith only [mul_le_mul_of_nonneg_right cn (sq_nonneg (moment b x)), num, den]
  rw [outerMoment_eq_evaluation b x hx', outerMoment_eq_evaluation (N+1) x hx'] at cmp
  have hb : b+1 = k := by dsimp [b]; omega
  have hnext : N+1 = 2*k-1 := by dsimp [N]; omega
  have hbig : N+1+1 = k*2 := by dsimp [N]; omega
  rw [hb, hbig, pow_mul, hnext] at cmp
  exact unscale hu (pow_pos (by linarith : 0 < 1+u) k) cmp

theorem firstSplitOuterBound (k : ℕ) (hk : 201 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (lower : 5/2*Real.sqrt (2*k-2 : ℕ) ≤ x)
    (zero : (LongCycles.eulerian (2*k-2)).eval (-Real.exp (-x)) = 0) :
    ((2*k).choose k : ℝ)/2 * Real.exp (-x) *
        ((LongCycles.eulerian (k-1)).eval (-Real.exp (-x)))^2 <
      |(LongCycles.eulerian (2*k-1)).eval (-Real.exp (-x))| := by
  let N := 2*k-2
  have hN : 400 ≤ N := by dsimp [N]; omega
  have hregion : 5*Real.sqrt N/2 ≤ x := by linarith [lower]
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
  have hx' : 0 < x := lt_of_le_of_ne hx (by linarith)
  exact firstSplitOuter_of_derivative k (by omega) x hx'
    (derivative_moment_bound N hN x hx' hregion) zero

#print axioms firstSplitOuterBound
end LongCycleBounds
