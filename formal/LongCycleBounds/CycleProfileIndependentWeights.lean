import LongCycleBounds.CycleProfileReadout

/-! Independently weighted short cycles and the line to ordinary derangements. -/

noncomputable section

namespace LongCycleBounds.CycleProfile

open Finset Polynomial Insertion LongCycles Band
open scoped Classical

/-- Remove the common zero factor from the row with possibly independent cycle weights. -/
def weightedQuotient (n : ℕ) (w : ℕ → ℝ) : ℝ[X] := (row n w).divX

private theorem coeff_row_weights (n m : ℕ) (w : ℕ → ℝ) :
    (row n w).coeff m =
      ∑ σ : Admissible n 2, cycleWeight w σ.val * (X ^ (excedances σ.val) : ℝ[X]).coeff m := by
  simp only [row_admissible, finsetSum_coeff, term, coeff_C_mul]

private theorem coeff_power_nonneg (a m : ℕ) : 0 ≤ (X ^ a : ℝ[X]).coeff m := by
  simp only [coeff_X_pow]
  split <;> norm_num

private theorem weight_coeff_mono (n m : ℕ) {w v : ℕ → ℝ} (w0 : ∀ a, 0 ≤ w a)
    (h : ∀ a, w a ≤ v a) : (row n w).coeff m ≤ (row n v).coeff m := by
  rw [coeff_row_weights, coeff_row_weights]
  apply sum_le_sum
  intro σ _
  apply mul_le_mul_of_nonneg_right _ (coeff_power_nonneg _ _)
  exact Multiset.prod_map_le_prod_map₀ w v (fun a _ ↦ w0 a) (fun a _ ↦ h a)

theorem weightedQuotient_endpoints {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    weightedQuotient n (profile k 0) = generalCycleQuotient n k ∧
      weightedQuotient n (profile k 1) = generalCycleQuotient n 2 :=
  quotient_endpoints hk hn

/-- The two original rows at cutoffs \(k\) and \(2\) bound every coefficient of the weighted row. -/
theorem weightedQuotient_shape {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) {w : ℕ → ℝ}
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) (tail : ∀ a ≥ k, w a = 1) :
    (weightedQuotient n w).natDegree = n - 2 ∧ (weightedQuotient n w).Monic ∧
      (weightedQuotient n w).eval 0 = 1 ∧ row n w = X * weightedQuotient n w := by
  have w0 (a : ℕ) : 0 ≤ w a := (unit a).1
  have bot0 (a : ℕ) : 0 ≤ profile k 0 a := by
    unfold profile
    split <;> norm_num
  have bot_le (a : ℕ) : profile k 0 a ≤ w a := by
    by_cases ha : a < k
    · simpa [profile, ha] using w0 a
    · simp [profile, ha, tail a (by omega)]
  have top_le (a : ℕ) : w a ≤ profile k 1 a := by simpa [profile] using (unit a).2
  have ends := weightedQuotient_endpoints hk (by omega : 0 < n)
  have between (i : ℕ) :
      (generalCycleQuotient n k).coeff i ≤ (weightedQuotient n w).coeff i ∧
        (weightedQuotient n w).coeff i ≤ (generalCycleQuotient n 2).coeff i := by
    rw [← ends.1, ← ends.2]
    simp only [weightedQuotient, coeff_divX]
    exact ⟨weight_coeff_mono n (i + 1) bot0 bot_le, weight_coeff_mono n (i + 1) w0 top_le⟩
  have sk := generalCycleQuotient_shape hk hn
  have s2 := generalCycleQuotient_shape (n := n) (k := 2) (by decide) (by omega)
  have top := between (n - 2)
  have lead : (weightedQuotient n w).coeff (n - 2) = 1 := by
    rw [← sk.1, sk.2.1.coeff_natDegree, sk.1, ← s2.1, s2.2.1.coeff_natDegree, s2.1] at top
    exact le_antisymm top.2 top.1
  have deg : (weightedQuotient n w).natDegree ≤ n - 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have b := between i
    rw [coeff_eq_zero_of_natDegree_lt (sk.1.trans_lt hi),
      coeff_eq_zero_of_natDegree_lt (s2.1.trans_lt hi)] at b
    exact le_antisymm b.2 b.1
  have z := between 0
  simp only [coeff_zero_eq_eval_zero, s2.2.2, sk.2.2] at z
  have bot : (row n w).coeff 0 = 0 := by
    have lo := weight_coeff_mono n 0 bot0 bot_le
    have hi := weight_coeff_mono n 0 w0 top_le
    rw [row_zero n hk, actual_general_cycle_row hk (by omega : 0 < n), coeff_X_mul_zero] at lo
    rw [row_one, actual_general_cycle_row (by decide : 2 ≤ 2) (by omega : 0 < n),
      coeff_X_mul_zero] at hi
    exact le_antisymm hi lo
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero deg (by simp [lead]),
    monic_of_natDegree_le_of_coeff_eq_one _ deg lead, le_antisymm z.2 z.1,
    by simpa [weightedQuotient, bot] using (X_mul_divX_add (row n w)).symm⟩

private theorem weightedQuotient_coeff_nonneg (n m : ℕ) {w : ℕ → ℝ} (w0 : ∀ a, 0 ≤ w a) :
    0 ≤ (weightedQuotient n w).coeff m := by
  rw [weightedQuotient, coeff_divX, coeff_row_weights]
  apply sum_nonneg
  intro σ _
  apply mul_nonneg _ (coeff_power_nonneg _ _)
  apply Multiset.prod_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hx
  exact w0 a

theorem weightedQuotient_neg_roots {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) {w : ℕ → ℝ}
    (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) (tail : ∀ a ≥ k, w a = 1)
    {t : ℝ} (root : (weightedQuotient n w).IsRoot t) : t < 0 := by
  by_contra! pos
  let p := weightedQuotient n w
  have z : p.coeff 0 = 1 := (coeff_zero_eq_eval_zero _).trans
    (weightedQuotient_shape hk hn unit tail).2.2.1
  have one := single_le_sum (s := range (p.natDegree + 1)) (f := fun i ↦ p.coeff i * t ^ i)
    (fun i _ ↦ mul_nonneg (weightedQuotient_coeff_nonneg n i (fun a ↦ (unit a).1))
      (pow_nonneg pos _)) (a := 0) (by simp)
  rw [← eval_eq_sum_range, z, pow_zero, mul_one] at one
  exact (not_lt_of_ge one) (by rw [show p.eval t = 0 from root]; norm_num)

/-- Affine interpolation from \(w\) to ordinary derangements, with singleton weight zero. -/
def anchorLine (w : ℕ → ℝ) (u : ℝ) (a : ℕ) : ℝ :=
  (1 - u) * w a + u * (if a = 1 then 0 else 1)

@[simp] theorem anchorLine_zero (w : ℕ → ℝ) : anchorLine w 0 = w := by
  funext a
  simp [anchorLine]

theorem anchorLine_singleton {w : ℕ → ℝ} (w1 : w 1 = 0) (u : ℝ) : anchorLine w u 1 = 0 := by
  simp [anchorLine, w1]

theorem anchorLine_unit {w : ℕ → ℝ} (unit : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (a : ℕ) : anchorLine w u a ∈ Set.Icc (0 : ℝ) 1 := by
  have e : (0 : ℝ) ≤ 1 - u := sub_nonneg.mpr hu.2
  have below := mul_le_mul_of_nonneg_left (unit a).2 e
  have above := mul_nonneg e (unit a).1
  unfold anchorLine
  by_cases h : a = 1
  · simpa [h] using And.intro above (below.trans (by linarith [hu.1]))
  · simp only [h, if_false, mul_one]
    exact ⟨add_nonneg above hu.1, by linarith only [below]⟩

theorem anchorLine_tail {k : ℕ} (hk : 2 ≤ k) {w : ℕ → ℝ} (tail : ∀ a ≥ k, w a = 1)
    (u : ℝ) {a : ℕ} (ha : k ≤ a) : anchorLine w u a = 1 := by
  simp [anchorLine, tail a ha, show a ≠ 1 by omega]

theorem row_anchorLine_one (n : ℕ) (w : ℕ → ℝ) : row n (anchorLine w 1) = enumerator n 2 := by
  rw [← row_one n 2, row_admissible, row_admissible]
  apply sum_congr rfl
  intro σ _
  simp only [term, cycleWeight]
  have same : σ.val.cycleType.map (anchorLine w 1) = σ.val.cycleType.map (profile 2 1) := by
    apply Multiset.map_congr rfl
    intro a ha
    have two : 2 ≤ a := le_of_mem_cycleType σ.property ha
    simp [anchorLine, profile, show a ≠ 1 by omega]
  rw [same]

private theorem continuous_line_weight (w : ℕ → ℝ) (m : Multiset ℕ) :
    Continuous fun u ↦ (m.map (anchorLine w u)).prod := by
  induction m using Multiset.induction_on with
  | empty => simpa using (continuous_const : Continuous fun _ : ℝ ↦ (1 : ℝ))
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (show Continuous fun u ↦ anchorLine w u a from by unfold anchorLine; fun_prop).mul ih

theorem continuous_line_quotient_coeff (n m : ℕ) (w : ℕ → ℝ) :
    Continuous fun u ↦ (weightedQuotient n (anchorLine w u)).coeff m := by
  simp only [weightedQuotient, coeff_divX, coeff_row_weights, cycleWeight]
  exact continuous_finsetSum _ fun σ _ ↦ (continuous_line_weight w σ.val.cycleType).mul
    continuous_const

#print axioms weightedQuotient_shape
#print axioms weightedQuotient_neg_roots
#print axioms row_anchorLine_one
#print axioms continuous_line_quotient_coeff

end LongCycleBounds.CycleProfile
