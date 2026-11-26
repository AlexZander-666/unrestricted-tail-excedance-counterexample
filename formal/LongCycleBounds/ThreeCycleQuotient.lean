import LongCycleBounds.ThreeCycleRows
import LongCycleBounds.TripleThresholdRow
import LongCycleBounds.AdjacentRootStep

/-! Degree, endpoint, and reciprocity of the true quotient below the four-cycle threshold. -/

noncomputable section

namespace LongCycleBounds.Band

open Finset Polynomial LongCycles LongCycleFinite

private def quotientTripleTerm (j a b : ℕ) : ℝ[X] :=
  C ((j.choose a:ℝ)*((j-a).choose b:ℝ)) * X^2 *
    eulerian (a-1) * eulerian (b-1) * eulerian (j-a-b-1)

/-- The original row has one common factor X. The third-cycle term retains X²
in the quotient and is counted on the entire ordered support window. -/
def threeCycleQuotient (j k : ℕ) : ℝ[X] :=
  deformedRow j k 1 + C (1/6:ℝ) *
    ∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k), quotientTripleTerm j a b

theorem actual_threeCycle_row {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (hhi : j < 4*k) :
    enumerator j k = X*threeCycleQuotient j k := by
  rw [enumerator_threeCycle hk hj hhi, threeCycleQuotient, mul_add]
  congr 1
  rw [mul_left_comm X]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  unfold quotientTripleTerm
  ring

theorem threeCycleQuotient_eq_deformed {j k : ℕ} (h : j < 3*k) :
    threeCycleQuotient j k = deformedRow j k 1 := by
  have empty : Icc k (j-2*k) = ∅ := Icc_eq_empty_of_lt (by omega)
  simp [threeCycleQuotient, empty]

theorem threeCycleQuotient_eq_threshold {k : ℕ} (hk : 2 ≤ k) :
    threeCycleQuotient (3*k) k = thresholdQuotient k := by
  apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0)
  rw [←actual_threeCycle_row hk (by omega) (by omega), ←actual_threshold_row hk]

private theorem cycle_degree {a : ℕ} (ha : 2 ≤ a) : (eulerian (a-1)).natDegree = a-2 := by
  simpa only [show a-2+1=a-1 by omega] using (eulerian_degree_monic (a-2)).1

private theorem quotientTripleTerm_degree {j a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ j-a-b) :
    (quotientTripleTerm j a b).natDegree ≤ j-4 := by
  let D := C ((j.choose a:ℝ)*((j-a).choose b:ℝ)) * (X^2 : ℝ[X])
  let A := eulerian (a-1)
  let B := eulerian (b-1)
  let E := eulerian (j-a-b-1)
  have dD : D.natDegree ≤ 2 := by
    apply (natDegree_C_mul_le ..).trans
    rw [natDegree_X_pow]
  have dA : A.natDegree = a-2 := cycle_degree ha
  have dB : B.natDegree = b-2 := cycle_degree hb
  have dE : E.natDegree = j-a-b-2 := cycle_degree hc
  have da : (D*A).natDegree ≤ D.natDegree+A.natDegree := natDegree_mul_le
  have db : (D*A*B).natDegree ≤ (D*A).natDegree+B.natDegree := natDegree_mul_le
  have dc : (D*A*B*E).natDegree ≤ (D*A*B).natDegree+E.natDegree := natDegree_mul_le
  change (D*A*B*E).natDegree ≤ j-4
  omega

theorem threeCycleQuotient_shape {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (hn : 3 ≤ j) :
    (threeCycleQuotient j k).natDegree = j-2 ∧ (threeCycleQuotient j k).Monic ∧
      (threeCycleQuotient j k).eval 0 = 1 := by
  let T : ℝ[X] := C (1/6:ℝ) *
    ∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k), quotientTripleTerm j a b
  have small : T.natDegree ≤ j-4 := by
    apply (natDegree_C_mul_le ..).trans
    apply natDegree_sum_le_of_forall_le
    intro a ha
    apply natDegree_sum_le_of_forall_le
    intro b hb
    obtain ⟨al,au⟩ := mem_Icc.mp ha
    obtain ⟨bl,bu⟩ := mem_Icc.mp hb
    exact quotientTripleTerm_degree (by omega) (by omega) (by omega)
  obtain ⟨deg,mon,at_zero⟩ := deformed_shape hk hj hn 1
  have lt : T.natDegree < (deformedRow j k 1).natDegree := by rw [deg]; omega
  change (deformedRow j k 1+T).natDegree = j-2 ∧
    (deformedRow j k 1+T).Monic ∧ (deformedRow j k 1+T).eval 0 = 1
  exact ⟨(natDegree_add_eq_left_of_natDegree_lt lt).trans deg,
    mon.add_of_left (degree_lt_degree lt), by simp [T,quotientTripleTerm,at_zero,eval_finsetSum]⟩

private theorem cycle_reciprocity {a : ℕ} (ha : 2 ≤ a) {t : ℝ} (ht : t≠0) :
    t^(a-2)*(eulerian (a-1)).eval t⁻¹ = (eulerian (a-1)).eval t := by
  simpa only [show a-2+1=a-1 by omega] using eulerian_reciprocity (a-2) ht

private theorem quotientTripleTerm_reciprocity {j a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ j-a-b) {t : ℝ} (ht : t≠0) :
    t^(j-2)*(quotientTripleTerm j a b).eval t⁻¹ = (quotientTripleTerm j a b).eval t := by
  let e := j-a-b
  have order : j-2=(a-2)+(b-2)+(e-2)+4 := by dsimp [e]; omega
  simp only [quotientTripleTerm,eval_mul,eval_C,eval_pow,eval_X]
  change t^(j-2)*(_*t⁻¹^2*(eulerian (a-1)).eval t⁻¹*(eulerian (b-1)).eval t⁻¹*
    (eulerian (e-1)).eval t⁻¹) = _*_*(eulerian (a-1)).eval t*(eulerian (b-1)).eval t*
      (eulerian (e-1)).eval t
  rw [order, pow_add, pow_add, pow_add, ←cycle_reciprocity ha ht, ←cycle_reciprocity hb ht,
    ←cycle_reciprocity (a := e) hc ht]
  field_simp

/-- Evaluation at reciprocal nonzero real inputs agrees at the full quotient degree. -/
theorem threeCycleQuotient_reciprocity {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) {t : ℝ}
    (ht : t≠0) :
    t^(j-2)*(threeCycleQuotient j k).eval t⁻¹ = (threeCycleQuotient j k).eval t := by
  simp only [threeCycleQuotient, eval_add, eval_mul, eval_C, eval_finsetSum, mul_add,
    deformed_reciprocity hk hj 1 ht]
  congr 1
  rw [mul_left_comm (t^_), mul_sum]
  congr 1
  apply sum_congr rfl
  intro a ha
  rw [mul_sum]
  apply sum_congr rfl
  intro b hb
  obtain ⟨al,au⟩ := mem_Icc.mp ha
  obtain ⟨bl,bu⟩ := mem_Icc.mp hb
  exact quotientTripleTerm_reciprocity (by omega) (by omega) (by omega) ht

/-- The shape hypotheses of the generic adjacent-root step for the original
three-cycle quotient. The sign premise is solely an analytic comparison. -/
theorem extend_threeCycle_actual_interlacing {n k : ℕ} (hk : 2 ≤ k) (hkn : k < n)
    (hn : 4 ≤ n) (hhi : n < 4*k)
    (prev : StrictNegativeInterlacing (threeCycleQuotient (n-1-1) k) (threeCycleQuotient (n-1) k) (n-4))
    (sign : ∀ x : ℝ, 0 ≤ x → normalizedEnumerator (n-1) k x = 0 →
      0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x)) :
    StrictNegativeInterlacing (threeCycleQuotient (n-1) k) (threeCycleQuotient n k) (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  obtain ⟨_,monP,_⟩ := threeCycleQuotient_shape (j := n-1) hk (by omega) (by omega)
  obtain ⟨degQ,monQ,zeroQ⟩ := threeCycleQuotient_shape (j := n) hk (by omega) (by omega)
  exact extend_actual_interlacing hn _ _ _ prev monP monQ degQ (by rw [zeroQ]; norm_num)
    (actual_threeCycle_row hk (by omega) (by omega)) (actual_threeCycle_row hk (by omega) hhi)
    (fun _ hu ↦ threeCycleQuotient_reciprocity hk (by omega) hu)
    (fun _ hu ↦ threeCycleQuotient_reciprocity hk (by omega) hu) sign

#print axioms actual_threeCycle_row
#print axioms threeCycleQuotient_eq_deformed
#print axioms threeCycleQuotient_eq_threshold
#print axioms threeCycleQuotient_shape
#print axioms threeCycleQuotient_reciprocity
#print axioms extend_threeCycle_actual_interlacing

end LongCycleBounds.Band
