import LongCycleBounds.Outer

/-! The steep tail comparison uses only N ≥ 100. If the first right ratio lies outside
the half-square-root zone, the exponential envelope already supplies its decay. -/
noncomputable section
namespace LongCycleBounds.Outer.Low
open Real

theorem mode_one_bound (N : ℕ) (hN : 100 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) : (mode N x hx : ℝ)+1 ≤ Real.sqrt N/2 := by
  have hroot : 10 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hN
  have hsq := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  have hi := mode_index_mul_le N x hx
  have hbound := mul_le_mul_of_nonneg_left hregion (Nat.cast_nonneg (mode N x hx))
  by_contra! bad
  nlinarith [mul_nonneg (sub_nonneg.mpr bad.le) (show 0 ≤ Real.sqrt (N : ℝ) by positivity)]

private theorem exp_small : exp (-4) < 1/50 := by
  rw [exp_neg,inv_lt_comm₀ (exp_pos _) (by norm_num)]
  have hh : (27/10 : ℝ)<exp 1 := by linarith [exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ hh (by norm_num : (0:ℝ) ≤ 27/10) (by decide : 4 ≠ 0)
  rw [← exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

theorem right_succ_decay (N : ℕ) (hN : 100≤N) (x : ℝ) (hx : 0<x)
    (hregion : 5*sqrt N/2≤x) {j : ℕ} (hj : mode N x hx<j) :
    weight N x (j+1) ≤ (1/50 : ℝ)*weight N x j := by
  let m := mode N x hx
  have hb : ratio N x (m+1) ≤ (1/50:ℝ) := by
    by_cases hh : (m:ℝ)+2 ≤ sqrt N/2
    · have hr := ratio_contracts N x m hh
      exact hr.trans (by linarith [ratio_mode_le N x hx])
    · have hs : 10 ≤ sqrt (N:ℝ) := by
        rw [le_sqrt (by norm_num) (by positivity)];exact_mod_cast hN
      have hsq := sq_sqrt (show 0≤(N:ℝ) by positivity)
      have hdiv : (N:ℝ)/((m:ℝ)+2) ≤ 2*sqrt N := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [mul_nonneg (show 0≤(m:ℝ)+2-sqrt N/2 by linarith) (sqrt_nonneg (N:ℝ))]
      have he := ratio_le_exp N x (m+1)
      push_cast at he
      have hindex : (m:ℝ)+1+1=m+2 := by ring
      rw [hindex] at he
      exact he.trans ((exp_le_exp.mpr (show (N:ℝ)/((m:ℝ)+2)-x≤ -4 by linarith)).trans exp_small.le)
  rw [weight_succ]
  exact mul_le_mul_of_nonneg_right ((ratio_antitone N x (show m+1≤j from hj)).trans hb) (weight_pos ..).le

theorem left_succ_decay (N : ℕ) (hN : 100 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) (d : ℕ) (hd : 1 ≤ d) :
    leftAt (weight N x) (mode N x hx) (d+1) ≤ (1/50 : ℝ)*leftAt (weight N x) (mode N x hx) d := by
  let m := mode N x hx
  by_cases he : d+1 ≤ m
  · let j := m-(d+1)
    have hj : j+1 = m-d := by dsimp [j]; omega
    have hbf : j+1 < mode N x hx := by change j+1 < m; omega
    have hcast : (j : ℝ)+1 ≤ (mode N x hx : ℝ) := by exact_mod_cast (show j+1 ≤ mode N x hx by omega)
    have he' := ratio_contracts N x j (by linarith [mode_one_bound N hN x hx hregion])
    have hr := (one_lt_ratio_before N x hx hbf).le.trans he'
    change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_pos he, leftAt, if_pos (by omega : d ≤ m), ← hj]
    change weight N x j ≤ _ * weight N x (j+1)
    rw [weight_succ, ← mul_assoc]
    exact le_mul_of_one_le_left (weight_pos ..).le hr
  · change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_neg he]
    exact mul_nonneg (by norm_num) (leftAt_nonneg (fun _ ↦ (weight_pos ..).le) ..)

theorem neighbors_product (N : ℕ) (hN : 100 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) :
    let m := mode N x hx
    leftAt (weight N x) m 1 * weight N x (m+1) ≤ (1/50 : ℝ)*weight N x m ^ 2 := by
  dsimp only
  generalize hm : mode N x hx = m
  cases m with
  | zero => simp [leftAt]; positivity
  | succ j =>
    have h := mode_one_bound N hN x hx hregion
    rw [hm] at h
    push_cast at h
    have hr := ratio_contracts N x j (by linarith)
    simp only [leftAt, if_pos (show 1 ≤ j+1 by omega), Nat.add_one_sub_one]
    rw [weight_succ N x (j+1), weight_succ N x j]
    nlinarith [mul_le_mul_of_nonneg_right hr
      (mul_nonneg (ratio_pos N x j).le (sq_nonneg (weight N x j)))]

theorem neighbors_min_le (N : ℕ) (hN : 100 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) :
    let m := mode N x hx
    min (leftAt (weight N x) m 1) (weight N x (m+1)) ≤ weight N x m/7 := by
  dsimp only
  have hp := neighbors_product N hN x hx hregion
  dsimp only at hp
  by_contra! bad
  rw [lt_min_iff] at bad
  have hh := mul_lt_mul_of_pos_left bad.2 (weight_pos N x (mode N x hx))
  have hmp := mul_lt_mul_of_pos_right bad.1 (weight_pos N x (mode N x hx+1))
  nlinarith [sq_pos_of_pos (weight_pos N x (mode N x hx))]

theorem both_geometric (N : ℕ) (hN : 100 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) (l : ℕ) :
    let m := mode N x hx
    leftAt (weight N x) m (l+1) ≤ (1/50 : ℝ)^l*weight N x m ∧
      weight N x (m+(l+1)) ≤ (1/50 : ℝ)^l*weight N x m := by
  let m := mode N x hx
  change leftAt (weight N x) m (l+1) ≤ _ ∧ weight N x (m+(l+1)) ≤ _
  induction l with
  | zero =>
    simp only [zero_add, pow_zero, one_mul]
    constructor
    · unfold leftAt
      split
      · exact weight_le_mode ..
      · exact (weight_pos ..).le
    · exact weight_le_mode ..
  | succ l ih =>
    have hl := left_succ_decay N hN x hx hregion (l+1) (by omega)
    have hr := right_succ_decay N hN x hx hregion (j := m+(l+1)) (by change m < _; omega)
    constructor
    · exact hl.trans (by rw [pow_succ']; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ih.1 (by norm_num))
    · exact hr.trans (by rw [pow_succ']; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ih.2 (by norm_num))


theorem derivative_at_root (N : ℕ) (hN : 100≤N) (x : ℝ) (hx : 0<x)
    (hregion : 5*sqrt N/2≤x) (hz : moment N x=0) :
    weight N x (mode N x hx)/2 < |moment (N+1) x| := by
  simpa [hz] using robust_derivative_of_tails N x hx (neighbors_min_le N hN x hx hregion)
    (both_geometric N hN x hx hregion)

end LongCycleBounds.Outer.Low
namespace LongCycleBounds

theorem firstSplitOuterBound51 (k : ℕ) (hk : 51≤k) (x : ℝ)
    (lower : 5/2*Real.sqrt (2*k-2 : ℕ) ≤ x)
    (zero : (LongCycles.eulerian (2*k-2)).eval (-Real.exp (-x))=0) :
    ((2*k).choose k : ℝ)/2 * Real.exp (-x) * ((LongCycles.eulerian (k-1)).eval (-Real.exp (-x)))^2 <
      |(LongCycles.eulerian (2*k-1)).eval (-Real.exp (-x))| := by
  have hN : 100 ≤ 2*k-2 := by omega
  have hs : 0 < Real.sqrt ((2*k-2:ℕ):ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0<2*k-2 by omega))
  have hx : 0<x := by linarith only [hs,lower]
  apply firstSplitOuter_of_derivative k (by omega) x hx _ zero
  exact Outer.Low.derivative_at_root (2*k-2) hN x hx (by linarith only [lower])

#print axioms firstSplitOuterBound51
end LongCycleBounds
