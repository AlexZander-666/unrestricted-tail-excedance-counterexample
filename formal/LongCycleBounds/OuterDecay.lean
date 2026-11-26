import LongCycleBounds.OuterMode

/-! Two-sided pointwise decay from the actual mode, with a zero extension at the left boundary. -/
noncomputable section
namespace LongCycleBounds.Outer

def leftAt (f : ℕ → ℝ) (m d : ℕ) := if d ≤ m then f (m-d) else 0

theorem leftAt_nonneg {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (m d : ℕ) : 0 ≤ leftAt f m d := by
  unfold leftAt
  split
  · apply hf
  · rfl

theorem right_succ_decay (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) {j : ℕ} (hj : mode N x hx < j) :
    weight N x (j+1) ≤ (1/50 : ℝ) * weight N x j := by
  have he := ratio_contracts N x (mode N x hx) (mode_add_two_le_half_sqrt N hN x hx hregion)
  have h := (ratio_antitone N x (show mode N x hx+1 ≤ j by omega)).trans he
  rw [weight_succ]
  apply mul_le_mul_of_nonneg_right _ (weight_pos ..).le
  simpa using h.trans (mul_le_mul_of_nonneg_left (ratio_mode_le N x hx) (by norm_num : (0:ℝ) ≤ 1/50))

theorem left_succ_decay (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) (d : ℕ) (hd : 1 ≤ d) :
    leftAt (weight N x) (mode N x hx) (d+1) ≤ (1/50 : ℝ)*leftAt (weight N x) (mode N x hx) d := by
  let m := mode N x hx
  by_cases he : d+1 ≤ m
  · let j := m-(d+1)
    have hj : j+1 = m-d := by dsimp [j]; omega
    have hbf : j+1 < mode N x hx := by change j+1 < m; omega
    have hcast : (j : ℝ) ≤ (mode N x hx : ℝ) := by exact_mod_cast (show j ≤ mode N x hx by omega)
    have he' := ratio_contracts N x j (le_trans (add_le_add_left hcast 2)
      (mode_add_two_le_half_sqrt N hN x hx hregion))
    have hr := (one_lt_ratio_before N x hx hbf).le.trans he'
    change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_pos he, leftAt, if_pos (by omega : d ≤ m), ← hj]
    change weight N x j ≤ _ * weight N x (j+1)
    rw [weight_succ, ← mul_assoc]
    exact le_mul_of_one_le_left (weight_pos ..).le hr
  · change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_neg he]
    exact mul_nonneg (by norm_num) (leftAt_nonneg (fun _ ↦ (weight_pos ..).le) ..)

theorem neighbors_product (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) :
    let m := mode N x hx
    leftAt (weight N x) m 1 * weight N x (m+1) ≤ (1/50 : ℝ)*weight N x m ^ 2 := by
  dsimp only
  generalize hm : mode N x hx = m
  cases m with
  | zero => simp [leftAt]; positivity
  | succ j =>
    have h := mode_add_two_le_half_sqrt N hN x hx hregion
    rw [hm] at h
    push_cast at h
    have hr := ratio_contracts N x j (by linarith)
    simp only [leftAt, if_pos (show 1 ≤ j+1 by omega), Nat.add_one_sub_one]
    rw [weight_succ N x (j+1), weight_succ N x j]
    nlinarith [mul_le_mul_of_nonneg_right hr
      (mul_nonneg (ratio_pos N x j).le (sq_nonneg (weight N x j)))]

theorem neighbors_min_le (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
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

theorem both_geometric (N : ℕ) (hN : 400 ≤ N) (x : ℝ) (hx : 0 < x)
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

end LongCycleBounds.Outer
