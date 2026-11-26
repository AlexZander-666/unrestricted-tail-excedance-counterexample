import LongCycleBounds.OuterAlternation
import LongCycleBounds.OuterDecay

/-! A two-sided discrete moment estimate around the actual largest positive-label term. -/

noncomputable section
namespace LongCycleBounds.Outer

open Finset

private theorem sum_left (f : ℕ → ℝ) (m : ℕ) :
    ∑' j : ℕ, leftAt f m (j+1) = ∑ j ∈ range m, f j := by
  rw [tsum_eq_sum (s := range m) (fun j hj ↦ by
    have h : ¬ j+1 ≤ m := by simpa [Finset.mem_range] using hj
    simp [leftAt, h])]
  rw [← sum_range_reflect f m]
  apply sum_congr rfl
  intro j hj
  simp only [mem_range] at hj
  simp [leftAt, show j+1 ≤ m by omega, show m-(j+1) = m-1-j by omega]

private theorem central_error (f : ℕ → ℝ) (m : ℕ) (hs : Summable f)
    {u : ℕ → ℝ} {b : ℝ} (hu : HasSum u b)
    (hl : ∀ j, |leftAt f m (j+2)| ≤ u j)
    (hr : ∀ j, |f (m+(j+2))| ≤ u j) :
    |(∑' j, f j) - (f m + leftAt f m 1 + f (m+1))| ≤ 2*b := by
  have hls : Summable (fun j : ℕ ↦ leftAt f m (j+1)) := by
    apply summable_of_ne_finset_zero (s := range m)
    intro j hj
    simp [leftAt, show ¬j+1 ≤ m by simpa [Finset.mem_range] using hj]
  have hrs : Summable (fun j : ℕ ↦ f (j+(m+1))) := (summable_nat_add_iff (m+1)).mpr hs
  have hl' := hls.tsum_eq_zero_add
  have hr' := hrs.tsum_eq_zero_add
  rw [sum_left] at hl'
  have hd := hs.sum_add_tsum_nat_add (m+1)
  rw [sum_range_succ] at hd
  have ht : (∑' j, f j) - (f m + leftAt f m 1 + f (m+1)) =
      (∑' j : ℕ, leftAt f m (j+2)) + (∑' j : ℕ, f (m+(j+2))) := by
    simp only [zero_add] at hl' hr'
    simp_rw [show ∀ j : ℕ, j+1+(m+1) = m+(j+2) from fun j ↦ by omega] at hr'
    linarith
  rw [ht]
  have bound (v : ℕ → ℝ) (hv : ∀ j, |v j| ≤ u j) : |∑' j, v j| ≤ b := by
    have hh : ∀ j, ‖v j‖ ≤ u j := by simpa [Real.norm_eq_abs] using hv
    rw [← hu.tsum_eq, ← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm (hu.summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) hh)).trans
      ((hu.summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) hh).tsum_le_tsum hh hu.summable)
  exact (abs_add_le ..).trans (by linarith [bound _ hl, bound _ hr])

private abbrev delta : ℝ := 1/50

private theorem tail_plain (M : ℝ) :
    HasSum (fun j : ℕ ↦ delta^(j+1)*M) (delta/(1-delta)*M) := by
  have h := ((hasSum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖delta‖ < 1)).mul_left
    delta).mul_right M
  have he (j : ℕ) : delta^(j+1)*M = delta * delta^j * M := by rw [pow_succ']
  simp_rw [he]
  exact h

private theorem tail_linear (M : ℝ) :
    HasSum (fun j : ℕ ↦ ((j : ℝ)+2)*delta^(j+1)*M) (((1-delta)⁻¹^2-1)*M) := by
  have hd : ‖delta‖ < 1 := by norm_num [Real.norm_eq_abs]
  have h := (((hasSum_coe_mul_geometric_of_norm_lt_one hd).add
    ((hasSum_geometric_of_norm_lt_one hd).mul_left 2)).mul_right delta).mul_right M
  have hval : ((1-delta)⁻¹^2-1)*M =
      (delta/(1-delta)^2 + 2*(1-delta)⁻¹)*delta*M := by norm_num [delta]
  have hf : (fun j : ℕ ↦ ((j : ℝ)+2)*delta^(j+1)*M) =
      fun j : ℕ ↦ (j*delta^j+2*delta^j)*delta*M := by
    funext j
    rw [pow_succ]
    ring
  rw [hval, hf]
  exact h

private def sig (j : ℕ) : ℝ := (-1)^j

private theorem abs_sig (j : ℕ) : |sig j| = 1 := by simp [sig]

private theorem sig_succ (j : ℕ) : sig (j+1) = - sig j := by simp [sig, pow_succ]

private theorem left_abs (f : ℕ → ℝ) (m d : ℕ) :
    |leftAt f m d| = leftAt (fun j ↦ |f j|) m d := by
  unfold leftAt
  split <;> simp

private theorem abs_left_signed (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (m d : ℕ) :
    |leftAt (fun j ↦ sig j * w j) m d| = leftAt w m d := by
  rw [left_abs]
  simp [abs_mul, abs_sig, abs_of_nonneg (hw _)]

private theorem left_centered (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (m d : ℕ) :
    |leftAt (fun j ↦ ((j : ℝ)-m)*(sig j*w j)) m d| = (d : ℝ)*leftAt w m d := by
  unfold leftAt
  split
  · rename_i h
    simp [abs_mul, abs_sig, abs_of_nonneg (hw _), Nat.cast_sub h, sub_sub_cancel_left]
  · simp

private theorem left_first (w : ℕ → ℝ) (m : ℕ) :
    leftAt (fun j ↦ sig j*w j) m 1 = -sig m*leftAt w m 1 := by
  cases m with
  | zero => simp [leftAt]
  | succ m => simp [leftAt, sig_succ]

private theorem centered_left_first (w : ℕ → ℝ) (m : ℕ) :
    leftAt (fun j ↦ ((j : ℝ)-m)*(sig j*w j)) m 1 = sig m*leftAt w m 1 := by
  cases m with
  | zero => simp [leftAt]
  | succ m => simp [leftAt, sig_succ]

/-- The alternating moment indexed from label one, with an overall minus sign relative
to the standard Eulerian power sum. -/
def moment (N : ℕ) (x : ℝ) : ℝ := ∑' j : ℕ, (-1 : ℝ)^j*weight N x j

private theorem next_weight (N : ℕ) (x : ℝ) (j : ℕ) :
    weight (N+1) x j = ((j : ℝ)+1)*weight N x j := by
  simp only [weight, pow_succ ((j : ℝ)+1)]
  ring

/-- The derivative moment stays large even when the preceding signed moment only nearly
vanishes. The coefficient uses the zero-based peak index; its positive label is mode+1. -/
theorem robust_derivative_of_tails (N : ℕ) (x : ℝ) (hx : 0 < x)
    (hn : min (leftAt (weight N x) (mode N x hx) 1) (weight N x (mode N x hx+1)) ≤
      weight N x (mode N x hx)/7)
    (hgrow : ∀ l : ℕ, leftAt (weight N x) (mode N x hx) (l+1) ≤
        (1/50 : ℝ)^l*weight N x (mode N x hx) ∧
      weight N x (mode N x hx+(l+1)) ≤ (1/50 : ℝ)^l*weight N x (mode N x hx)) :
    weight N x (mode N x hx)/2 <
      |moment (N+1) x| + ((mode N x hx : ℝ)+2)*|moment N x| := by
  let w := weight N x
  let m := mode N x hx
  let M := w m
  let L := leftAt w m 1
  let R := w (m+1)
  let f (j : ℕ) := sig j * w j
  let g (j : ℕ) := ((j : ℝ)-m)*f j
  have hM : 0 < M := weight_pos ..
  have hw (j : ℕ) : 0 ≤ w j := (weight_pos ..).le
  have hL : 0 ≤ L := leftAt_nonneg hw m 1
  have hR : 0 ≤ R := hw _
  change min L R ≤ M/7 at hn
  have hgeom (j : ℕ) := hgrow (j+1)
  have hs : Summable f := summable_signed_weight N x hx
  have hf0 : ∑' j, f j = moment N x := rfl
  have hg (j : ℕ) : g j = sig j * weight (N+1) x j - ((m : ℝ)+1)*f j := by
    rw [next_weight]
    dsimp [g, f, w]
    ring
  have hsg : Summable g := ((summable_signed_weight (N+1) x hx).sub
    (hs.mul_left ((m : ℝ)+1))).congr (fun j ↦ (hg j).symm)
  let y := moment (N+1) x - ((m : ℝ)+1)*moment N x
  have hg0 : ∑' j, g j = y := by
    simp_rw [hg]
    have ha : Summable (fun j ↦ sig j * weight (N+1) x j) := summable_signed_weight _ _ hx
    rw [ha.tsum_sub (hs.mul_left ((m : ℝ)+1)), tsum_mul_left, hf0]
    rfl
  have h1 := central_error f m hs (tail_plain M)
    (fun j ↦ (abs_left_signed w hw m (j+2)).le.trans (hgeom j).1) (fun j ↦ by
      simp only [f, abs_mul, abs_sig, abs_of_nonneg (hw _), one_mul]
      exact (hgeom j).2)
  have h2 := central_error g m hsg (tail_linear M)
    (fun j ↦ by
      rw [show |leftAt g m (j+2)| = ((j+2 : ℕ) : ℝ)*leftAt w m (j+2) from
        left_centered w hw m (j+2)]
      push_cast
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hgeom j).1 (by positivity)) (fun j ↦ by
      have he : ((m+(j+2) : ℕ) : ℝ) - (m : ℝ) = (j : ℝ)+2 := by push_cast; ring
      simp only [g, f, abs_mul, abs_sig, one_mul, abs_of_nonneg (hw _), he,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (j : ℝ)+2)]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hgeom j).2 (by positivity))
  have hv1 : f m + leftAt f m 1 + f (m+1) = sig m*(M-L-R) := by
    change sig m*M + leftAt (fun j ↦ sig j*w j) m 1 + sig (m+1)*R = _
    rw [left_first, sig_succ]
    dsimp only [L]
    ring
  have hv2 : g m + leftAt g m 1 + g (m+1) = sig m*(L-R) := by
    rw [show leftAt g m 1 = sig m*L from centered_left_first w m]
    dsimp only [g, f, R]
    push_cast
    rw [sig_succ]
    ring
  rw [hf0, hv1] at h1
  rw [hg0, hv2] at h2
  have tri (a b : ℝ) : |a| ≤ |b|+|b-sig m*a| := by
    have hh := abs_sub b (b-sig m*a)
    rwa [sub_sub_cancel, abs_mul, abs_sig, one_mul] at hh
  have h3 := tri (L-R) y
  have h4 := (le_abs_self (M-L-R)).trans (tri (M-L-R) (moment N x))
  have hy : |y| ≤ |moment (N+1) x|+((m : ℝ)+1)*|moment N x| := by
    apply (abs_sub _ _).trans_eq
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)+1)]
  have h5 : L+R-2*min L R ≤ |L-R| := by
    rcases le_total L R with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      linarith
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      linarith
  change M/2 < |moment (N+1) x|+((m : ℝ)+2)*|moment N x|
  norm_num [delta] at h1 h2
  linarith

theorem robust_derivative_moment (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) :
    weight N x (mode N x hx)/2 <
      |moment (N+1) x| + ((mode N x hx : ℝ)+2)*|moment N x| := by
  exact robust_derivative_of_tails N x hx (neighbors_min_le N hN x hx hregion)
    (both_geometric N hN x hx hregion)

/-- Perturbation margin in the scale of the positive label of the mode. -/
theorem derivative_margin (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) (ε : ℝ)
    (hsmall : ((mode N x hx : ℝ)+1)*|moment N x| ≤ ε*weight N x (mode N x hx)) :
    (1/2-2*ε)*weight N x (mode N x hx) < |moment (N+1) x| := by
  have h := robust_derivative_moment N hN x hx hregion
  nlinarith only [h, hsmall, mul_nonneg (Nat.cast_nonneg (mode N x hx) : (0:ℝ) ≤ _)
    (abs_nonneg (moment N x))]

/-- Specialization at an actual zero of the lower signed moment. -/
theorem derivative_moment_bound (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) (hz : moment N x = 0) :
    weight N x (mode N x hx)/2 < |moment (N+1) x| := by
  simpa [hz] using robust_derivative_moment N hN x hx hregion

#print axioms derivative_margin
#print axioms robust_derivative_moment
#print axioms derivative_moment_bound

end LongCycleBounds.Outer
