import LongCycleBounds.GeneralCycleSupports
import LongCycleBounds.ThreeCycleQuotient

/-! Quotients, degree and reciprocity of all nonempty actual rows. -/

noncomputable section
namespace LongCycleBounds.Band
open CycleCount Finset Polynomial LongCycles LongCycleFinite

/-- The ordered support sum with one factor of X removed from each cycle. -/
def orderedCycleFactor (n k : ℕ) : ℕ → ℝ[X]
  | 0 => if n = 0 then 1 else 0
  | h+1 => ∑ a ∈ Icc k n, C (n.choose a:ℝ)*eulerian (a-1)*orderedCycleFactor (n-a) k h
termination_by h => h

theorem orderedCycleRow_factor (n k h : ℕ) :
    orderedCycleRow n k h = X^h*orderedCycleFactor n k h := by
  induction h generalizing n with
  | zero => simp [orderedCycleRow, orderedCycleFactor]
  | succ h ih =>
    rw [orderedCycleRow, orderedCycleFactor, mul_sum]
    apply sum_congr rfl
    intro a _
    rw [ih, pow_succ]
    ring

private theorem orderedCycleFactor_zero {n k h : ℕ} (hk : 2 ≤ k) (small : n < 2*h) :
    orderedCycleFactor n k h = 0 := by
  induction h generalizing n with
  | zero => omega
  | succ h ih =>
    rw [orderedCycleFactor]
    apply sum_eq_zero
    intro a ha
    obtain ⟨lower, upper⟩ := mem_Icc.mp ha
    rw [ih (by omega : n-a < 2*h), mul_zero]

private theorem cycle_factor_degree {a : ℕ} (ha : 2 ≤ a) :
    (eulerian (a-1)).natDegree = a-2 := by
  simpa only [show a-2+1 = a-1 by omega] using (eulerian_degree_monic (a-2)).1

theorem orderedCycleFactor_degree {n k h : ℕ} (hk : 2 ≤ k) :
    (orderedCycleFactor n k h).natDegree ≤ n-2*h := by
  induction h generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [orderedCycleFactor, hn]
  | succ h ih =>
    rw [orderedCycleFactor]
    apply natDegree_sum_le_of_forall_le
    intro a ha
    obtain ⟨lower, upper⟩ := mem_Icc.mp ha
    by_cases room : 2*h ≤ n-a
    · apply (natDegree_mul_le ..).trans
      have dA := natDegree_C_mul_le (n.choose a : ℝ) (eulerian (a-1))
      have dB := @ih (n-a)
      rw [cycle_factor_degree (by omega : 2 ≤ a)] at dA
      omega
    · simp [orderedCycleFactor_zero hk (by omega : n-a < 2*h)]

private theorem cycle_factor_reciprocity {a : ℕ} (ha : 2 ≤ a) {t : ℝ} (ht : t ≠ 0) :
    t^(a-2)*(eulerian (a-1)).eval t⁻¹ = (eulerian (a-1)).eval t := by
  simpa only [show a-2+1 = a-1 by omega] using eulerian_reciprocity (a-2) ht

/-- After removing X from each cycle the ordered support row is reciprocal
at order n - 2h, including the zero row when the support window is empty. -/
theorem orderedCycleFactor_reciprocity {n k h : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ≠ 0) :
    t^(n-2*h)*(orderedCycleFactor n k h).eval t⁻¹ = (orderedCycleFactor n k h).eval t := by
  induction h generalizing n with
  | zero =>
    by_cases hn : n=0
    · simp [orderedCycleFactor, hn]
    · simp [orderedCycleFactor, hn]
  | succ h ih =>
    simp only [orderedCycleFactor, eval_finsetSum, mul_sum]
    apply sum_congr rfl
    intro a ha
    obtain ⟨lower, upper⟩ := mem_Icc.mp ha
    by_cases room : 2*h ≤ n-a
    · have deg : n-2*(h+1) = (a-2)+(n-a-2*h) := by omega
      simp only [eval_mul, eval_C]
      rw [deg, pow_add, ← cycle_factor_reciprocity (by omega : 2 ≤ a) ht, ← ih (n := n-a)]
      ring
    · simp [orderedCycleFactor_zero hk (by omega : n-a < 2*h)]

private theorem orderedCycleFactor_one {n k : ℕ} (lo : k ≤ n) :
    orderedCycleFactor n k 1 = eulerian (n-1) := by
  rw [orderedCycleFactor, sum_eq_single_of_mem n (mem_Icc.mpr ⟨lo, le_rfl⟩)]
  · simp [orderedCycleFactor]
  · intro a ha hne
    have upper := (mem_Icc.mp ha).2
    have h : n-a ≠ 0 := by omega
    simp [orderedCycleFactor, h]

/-- The actual quotient of the nonempty original permutation row by X. -/
def generalCycleQuotient (n k : ℕ) : ℝ[X] :=
  ∑ h ∈ range (n/k), C (1/((h+1).factorial:ℝ))*X^h*orderedCycleFactor n k (h+1)

/-- Factor one X from every permissible nonempty original row. -/
theorem actual_general_cycle_row {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    enumerator n k = X*generalCycleQuotient n k := by
  rw [enumerator_ordered_cycle_rows hk, sum_range_succ']
  simp only [orderedCycleRow.eq_1, if_neg hn.ne', mul_zero, add_zero]
  rw [generalCycleQuotient, mul_sum]
  apply sum_congr rfl
  intro h _
  rw [orderedCycleRow_factor, pow_succ]
  ring

#print axioms orderedCycleRow_factor
#print axioms orderedCycleFactor_degree
#print axioms orderedCycleFactor_reciprocity
#print axioms actual_general_cycle_row

private theorem generalCycleQuotient_split {n k : ℕ} (hk : 2 ≤ k) (lo : k ≤ n) :
    generalCycleQuotient n k = eulerian (n-1) +
      ∑ h ∈ range (n/k-1), C (1/((h+2).factorial:ℝ))*X^(h+1)*orderedCycleFactor n k (h+2) := by
  have pos : 1 ≤ n/k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).2 (by simpa using lo)
  unfold generalCycleQuotient
  conv_lhs => rw [← Nat.sub_add_cancel pos, sum_range_succ']
  simp [orderedCycleFactor_one lo]
  exact add_comm _ _

private theorem room_of_index {n k h : ℕ} (hk : 2 ≤ k) (hi : h < n/k) :
    2*(h+1) ≤ n := calc
  _ = (h+1)*2 := by ring
  _ ≤ (h+1)*k := Nat.mul_le_mul_left _ hk
  _ ≤ (n/k)*k := Nat.mul_le_mul_right _ (by omega)
  _ ≤ n := Nat.div_mul_le_self _ _

/-- The one-cycle row determines the leading and constant coefficients
throughout every allowed cycle count. -/
theorem generalCycleQuotient_shape {n k : ℕ} (hk : 2 ≤ k) (lo : k ≤ n) :
    (generalCycleQuotient n k).natDegree = n-2 ∧ (generalCycleQuotient n k).Monic ∧
      (generalCycleQuotient n k).eval 0 = 1 := by
  have base : (eulerian (n-1)).natDegree = n-2 ∧ (eulerian (n-1)).Monic := by
    simpa only [show n-2+1 = n-1 by omega] using eulerian_degree_monic (n-2)
  by_cases hn : n = 2
  · have hk' : k = 2 := by omega
    have empty : n/k-1 = 0 := by simp [hn, hk']
    rw [generalCycleQuotient_split hk lo, empty, range_zero, sum_empty, add_zero]
    exact ⟨base.1, base.2, eulerian_at_zero _⟩
  let R := ∑ h ∈ range (n/k-1), C (1/((h+2).factorial:ℝ))*X^(h+1)*orderedCycleFactor n k (h+2)
  have small : R.natDegree ≤ n-3 := by
    apply natDegree_sum_le_of_forall_le
    intro h hi
    have room := room_of_index hk (show h+1 < n/k by have := mem_range.mp hi; omega)
    apply natDegree_mul_le.trans
    have monomial : (C (1/((h+2).factorial:ℝ))*X^(h+1)).natDegree ≤ h+1 :=
      (natDegree_C_mul_le ..).trans_eq (natDegree_X_pow _)
    have factor := orderedCycleFactor_degree (n := n) (k := k) (h := h+2) hk
    omega
  have below : R.natDegree < (eulerian (n-1)).natDegree := by rw [base.1]; omega
  rw [generalCycleQuotient_split hk lo]
  change (eulerian (n-1)+R).natDegree = n-2 ∧ (eulerian (n-1)+R).Monic ∧
    (eulerian (n-1)+R).eval 0 = 1
  exact ⟨(natDegree_add_eq_left_of_natDegree_lt below).trans base.1,
    base.2.add_of_left (degree_lt_degree below), by simp [R, eval_finsetSum, eulerian_at_zero]⟩

/-- Reciprocity of the actual quotient at every nonzero real argument. -/
theorem generalCycleQuotient_reciprocity {n k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ≠ 0) :
    t^(n-2)*(generalCycleQuotient n k).eval t⁻¹ = (generalCycleQuotient n k).eval t := by
  simp only [generalCycleQuotient, eval_finsetSum, mul_sum]
  apply sum_congr rfl
  intro h hi
  have room := room_of_index hk (mem_range.mp hi)
  have order : n-2 = h+h+(n-2*(h+1)) := by omega
  have cancel : t^(h+h)*(t⁻¹)^h = t^h := by
    rw [pow_add, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  calc
    _ = (1/((h+1).factorial:ℝ))*(t^(h+h)*(t⁻¹)^h)*
        (t^(n-2*(h+1))*(orderedCycleFactor n k (h+1)).eval t⁻¹) := by
      rw [order, pow_add t (h+h)]
      ring
    _ = _ := by rw [cancel, orderedCycleFactor_reciprocity hk ht]

/-- The general quotient agrees with the established two-cycle quotient. -/
theorem generalCycleQuotient_eq_deformed {n k : ℕ} (hk : 2 ≤ k) (lo : k ≤ n)
    (hi : n < 3*k) : generalCycleQuotient n k = deformedRow n k 1 := by
  apply mul_left_cancel₀ (X_ne_zero : (X:ℝ[X]) ≠ 0)
  rw [← actual_general_cycle_row hk (by omega), ← actual_band_row hk lo hi]

/-- The general quotient agrees with the established three-cycle quotient. -/
theorem generalCycleQuotient_eq_threeCycle {n k : ℕ} (hk : 2 ≤ k) (lo : k ≤ n)
    (hi : n < 4*k) : generalCycleQuotient n k = threeCycleQuotient n k := by
  apply mul_left_cancel₀ (X_ne_zero : (X:ℝ[X]) ≠ 0)
  rw [← actual_general_cycle_row hk (by omega), ← actual_threeCycle_row hk lo hi]

theorem generalCycleQuotient_eq_threshold {k : ℕ} (hk : 2 ≤ k) :
    generalCycleQuotient (3*k) k = thresholdQuotient k :=
  (generalCycleQuotient_eq_threeCycle hk (by omega) (by omega)).trans
    (threeCycleQuotient_eq_threshold hk)

/-- Extend strict interlacing of the original rows by one step, given the
normalized analytic sign at each preceding zero. -/
theorem extend_general_actual_interlacing {n k : ℕ} (hk : 2 ≤ k) (hkn : k < n)
    (hn : 4 ≤ n)
    (prev : StrictNegativeInterlacing (generalCycleQuotient (n-1-1) k)
      (generalCycleQuotient (n-1) k) (n-4))
    (sign : ∀ x : ℝ, 0 ≤ x → normalizedEnumerator (n-1) k x = 0 →
      0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x)) :
    StrictNegativeInterlacing (generalCycleQuotient (n-1) k) (generalCycleQuotient n k) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  obtain ⟨_, monP, _⟩ := generalCycleQuotient_shape (n := n-1) hk (by omega)
  obtain ⟨degQ, monQ, zeroQ⟩ := generalCycleQuotient_shape (n := n) hk (by omega)
  exact extend_actual_interlacing hn _ _ _ prev monP monQ degQ (by rw [zeroQ]; norm_num)
    (actual_general_cycle_row hk (by omega)) (actual_general_cycle_row hk (by omega))
    (fun _ ht ↦ generalCycleQuotient_reciprocity hk ht)
    (fun _ ht ↦ generalCycleQuotient_reciprocity hk ht) sign

#print axioms generalCycleQuotient_shape
#print axioms generalCycleQuotient_reciprocity
#print axioms generalCycleQuotient_eq_deformed
#print axioms generalCycleQuotient_eq_threeCycle
#print axioms generalCycleQuotient_eq_threshold
#print axioms extend_general_actual_interlacing

end LongCycleBounds.Band
