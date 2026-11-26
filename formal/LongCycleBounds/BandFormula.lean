import LongCycleBounds.BandRows

/-! Folding the ordered support sum about its midpoint gives twice the unordered sum. -/
noncomputable section
namespace LongCycleBounds.Band
open Finset LongCycles Polynomial
open scoped Classical

private theorem reflect_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n k : ℕ) (hk : k≤n) :
    ∑ a ∈ Icc k (n-k), f (n-a) = ∑ a ∈ Icc k (n-k), f a := by
  apply sum_bij' (fun a _ ↦ n-a) (fun a _ ↦ n-a)
  all_goals intros a ha; obtain ⟨ha₁,ha₂⟩ := mem_Icc.mp ha
  all_goals first | exact mem_Icc.mpr ⟨by omega,by omega⟩ | congr 1 <;> omega

/-- Oriented contribution of one specified first support size, before dividing by two. -/
def orderedTerm (n a : ℕ) : ℝ[X] :=
  C (n.choose a : ℝ) * ((X*eulerian (a-1))*(X*eulerian (n-a-1)))

private theorem ordered_symmetric {n a : ℕ} (ha : a≤n) :
    orderedTerm n (n-a) = orderedTerm n a := by
  rw [orderedTerm,orderedTerm,Nat.choose_symm ha,show n-(n-a)=a by omega,mul_comm (X*_)]
  
private theorem twice_diagonal (a : ℕ) (ha : 1≤a) :
    (2 : ℝ) * (((2*a).choose a / 2 : ℕ) : ℝ) = ((2*a).choose a : ℝ) := by
  exact_mod_cast Nat.mul_div_cancel' (Nat.two_dvd_centralBinom_of_one_le ha)

theorem twice_contributions (n k : ℕ) (hk : 2≤k) (hkn : k≤n) :
    2 * ∑ a ∈ Icc k (n/2), cycleContribution n a = ∑ a ∈ Icc k (n-k), orderedTerm n a := by
  let lo (a : ℕ) : ℝ[X] := if a ≤ n-a then orderedTerm n a else 0
  let hi (a : ℕ) : ℝ[X] := if a < n-a then orderedTerm n a else 0
  have fold : (∑ a ∈ Icc k (n-k), orderedTerm n a) =
      ∑ a ∈ Icc k (n-k), (lo a + hi a) := by
    have hx (a : ℕ) (ha : a∈Icc k (n-k)) : orderedTerm n a = lo a + hi (n-a) := by
      obtain ⟨_,ha₂⟩ := mem_Icc.mp ha
      have ha' : a≤n := by omega
      simp only [lo,hi,show n-(n-a)=a by omega,ordered_symmetric ha']
      by_cases h : a≤n-a <;> simp [h,show n-a<a ↔ ¬a≤n-a by omega]
    rw [sum_congr rfl hx,sum_add_distrib,reflect_sum hi n k hkn,← sum_add_distrib]
  rw [fold,← sum_filter_add_sum_filter_not (Icc k (n-k)) (fun a ↦ a≤n/2)]
  have hzero : (∑ a ∈ (Icc k (n-k)).filter (fun a ↦ ¬a≤n/2), (lo a+hi a)) = 0 := by
    apply sum_eq_zero
    intro a ha
    obtain ⟨ha,hgt⟩ := mem_filter.mp ha
    have := (mem_Icc.mp ha).2
    simp [lo,hi,show ¬a≤n-a by omega,show ¬a<n-a by omega]
  rw [hzero,add_zero]
  have hfilter : (Icc k (n-k)).filter (fun a ↦ a≤n/2) = Icc k (n/2) := by
    ext a
    simp only [mem_filter,mem_Icc]
    omega
  rw [hfilter,mul_sum]
  apply sum_congr rfl
  intro a ha
  obtain ⟨hal,har⟩ := mem_Icc.mp ha
  have hlow : a≤n-a := by omega
  by_cases he : a=n-a
  · have hn : n=2*a := by omega
    subst n
    have he' : 2*a-a=a := by omega
    simp only [lo,hi,orderedTerm,cycleContribution,supportMultiplicity,he',le_refl,if_true,
      lt_self_iff_false,if_false,add_zero]
    have hc := congrArg (C : ℝ →+* ℝ[X]) (twice_diagonal a (by omega))
    rw [map_mul,map_ofNat] at hc
    rw [← mul_assoc,hc]
  · simp [lo,hi,cycleContribution,supportMultiplicity,orderedTerm,he,hlow,lt_of_le_of_ne hlow he,two_mul]

/-- The quotient used in the two-row homotopy with its two-cycle part multiplied by τ. -/
def deformedRow (n k : ℕ) (τ : ℝ) : ℝ[X] :=
  eulerian (n-1) + C (τ/2) * ∑ a ∈ Icc k (n-k),
    C (n.choose a : ℝ) * X * eulerian (a-1) * eulerian (n-a-1)

@[simp] theorem deformedRow_zero (n k : ℕ) : deformedRow n k 0 = eulerian (n-1) := by
  simp [deformedRow]

/-- The common homotopy endpoint τ=1 equals the true permutation row with its factor X restored. -/
theorem actual_band_row {n k : ℕ} (hk : 2≤k) (hkn : k≤n) (hn : n<3*k) :
    enumerator n k = X*deformedRow n k 1 := by
  rw [enumerator_band hk hkn hn,deformedRow,mul_add]
  congr 1
  let E := (∑ a ∈ Icc k (n/2), cycleContribution n a)
  have ht := twice_contributions n k hk hkn
  have h : (∑ a ∈ Icc k (n-k), orderedTerm n a) =
      X*(∑ a ∈ Icc k (n-k), C (n.choose a : ℝ)*X*eulerian (a-1)*eulerian (n-a-1)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    unfold orderedTerm
    ring
  rw [h] at ht
  change E = _
  calc
    E = C (1/2 : ℝ) * (2*E) := by
      rw [← mul_assoc,← map_ofNat (f := C) (n := 2),← map_mul]
      norm_num
    _ = _ := by rw [show 2*E = _ from ht]; ring

#print axioms twice_contributions
#print axioms actual_band_row
end LongCycleBounds.Band
