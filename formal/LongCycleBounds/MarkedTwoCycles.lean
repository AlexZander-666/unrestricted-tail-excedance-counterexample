import LongCycleBounds.GeneralCycleSupports
import LongCycles.PermCycleBridge

/-! Derangements marked by their exact number of two-cycles. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open LongCycles Equiv Finset Polynomial Insertion
open scoped Classical

/-- The multiplicity of the part two in the actual permutation cycle type. -/
def twos {n : ℕ} (σ : Perm (Fin n)) : ℕ := σ.cycleType.count 2

def term {n : ℕ} (u : ℝ) (σ : Perm (Fin n)) : ℝ[X] :=
  C (u ^ twos σ) * X ^ excedances σ

/-- A sum over derangements with independently real-valued two-cycle weight. -/
def row (n : ℕ) (u : ℝ) : ℝ[X] :=
  ∑ σ : Perm (Fin n), if Allowed 2 σ then term u σ else 0

theorem row_one (n : ℕ) : row n 1 = enumerator n 2 := by
  simp [row,term,enumerator]

theorem three_iff {n : ℕ} (σ : Perm (Fin n)) :
    Allowed 3 σ ↔ Allowed 2 σ ∧ twos σ = 0 := by
  constructor
  · intro h
    refine ⟨fun i b hb hu ↦ h i b hb (by omega),?_⟩
    apply Multiset.count_eq_zero.mpr
    intro hm
    have := le_of_mem_cycleType h hm
    omega
  · rintro ⟨h,z⟩
    apply allowed_of_cycleType_lower (support_univ_of_allowed h (by decide))
    intro b hb
    have lower := le_of_mem_cycleType h hb
    have neq : b ≠ 2 := by
      rintro rfl
      exact (Multiset.count_eq_zero.mp z) hb
    omega

theorem row_zero (n : ℕ) : row n 0 = enumerator n 3 := by
  classical
  unfold row enumerator
  apply sum_congr rfl
  intro σ _
  rw [three_iff]
  by_cases h : Allowed 2 σ
  · by_cases z : twos σ = 0 <;> simp [h,z,term]
  · simp [h]

theorem row_admissible (n : ℕ) (u : ℝ) :
    row n u = ∑ σ : Admissible n 2, term u σ.val := by
  classical
  unfold row
  rw [←sum_filter]
  apply sum_subtype
  simp

private theorem anchor_data {n a : ℕ} {x : Fin n} (s : ↥(anchoredSupports x a)) :
    s.val.card = a ∧ x ∈ s.val := by
  obtain ⟨h,g⟩ := mem_filter.mp s.property
  exact ⟨(mem_powersetCard.mp h).2,g (mem_singleton_self _)⟩

private theorem compl_card {n a : ℕ} {x : Fin n} (s : ↥(anchoredSupports x a)) :
    s.valᶜ.card=n-a := by simp [card_compl,Fintype.card_fin,(anchor_data s).1]

private theorem disjoint_place {n a : ℕ} {x : Fin n} {s : ↥(anchoredSupports x a)}
    (c : CyclesOn s.val) (f : Perm (Fin (n-a))) :
    c.val.Disjoint (placeEquiv s.valᶜ (compl_card s) f).val := by
  intro y
  by_cases h : y ∈ s.val
  · exact Or.inr ((placeEquiv _ _ _).property y (by simpa))
  · exact Or.inl (Perm.notMem_support.mp (c.property.2.symm ▸ h))

theorem joined_twos {n a : ℕ} {x : Fin n} (ha : 2 ≤ a) (s : ↥(anchoredSupports x a))
    (c : CyclesOn s.val) (f : Admissible (n-a) 2) :
    twos (Anchored.branchEquiv x (by decide : 2 ≤ 2) ha ⟨s,c,f⟩).val =
      (if a = 2 then 1 else 0) + twos f.val := by
  change (c.val*(placeEquiv s.valᶜ (compl_card s) f.val).val).cycleType.count 2 = _
  rw [(disjoint_place c f.val).cycleType_mul, Multiset.count_add, c.property.1.cycleType,
    c.property.2, (anchor_data s).1, CycleCount.cycleType_place]
  by_cases eq : a=2 <;> simp [eq,eq_comm,twos]

private theorem joined_term {n a : ℕ} {x : Fin n} (ha : 2 ≤ a) (s : ↥(anchoredSupports x a))
    (c : CyclesOn s.val) (f : Admissible (n-a) 2) (u : ℝ) :
    term u (Anchored.branchEquiv x (by decide : 2 ≤ 2) ha ⟨s,c,f⟩).val =
      C (if a=2 then u else 1) * X^excedances c.val * term u f.val := by
  unfold term
  rw [joined_twos ha s c f,pow_add,map_mul]
  change _ * X^excedances (c.val*(placeEquiv s.valᶜ (compl_card s) f.val).val) = _
  rw [excedances_disjoint_mul (disjoint_place c f.val),excedances_place,pow_add]
  by_cases eq : a=2 <;> simp [eq] <;> ring

theorem branch_weight {n a : ℕ} (x : Fin n) (ha : 2 ≤ a) (u : ℝ) :
    (∑ τ : Anchored.Branch x a 2, term u τ.val) =
      C (((n-1).choose (a-1)):ℝ) * (C (if a=2 then u else 1)*(X*eulerian (a-1))) *
        row (n-a) u := by
  rw [← (Anchored.branchEquiv x (by decide : 2≤2) ha).sum_comp (fun τ ↦ term u τ.val)]
  rw [Fintype.sum_sigma]
  have per (s : ↥(anchoredSupports x a)) :
      (∑ v : CyclesOn s.val × Admissible (n-a) 2,
        term u (Anchored.branchEquiv x (by decide : 2≤2) ha ⟨s,v⟩).val) =
        (C (if a=2 then u else 1)*(X*eulerian (a-1)))*row (n-a) u := by
    rw [Fintype.sum_prod_type,row_admissible]
    simp_rw [joined_term ha s _ _ u,←mul_sum,←sum_mul,←mul_sum]
    rw [singleCycleWeight s.val ((anchor_data s).1.trans (by omega : a=a-1+1)) (by omega)]
  simp_rw [per]
  rw [sum_const,card_univ,Fintype.card_coe,anchoredSupports,card_filter_powersetCard_subset _ _ _
    (singleton_subset_iff.mpr (mem_univ x)) (by simpa using (show 1≤a by omega))]
  simp [nsmul_eq_mul,mul_assoc]

/-- Coefficient recurrence from removing the entire cycle through a specified label.
It determines every coefficient of the exponential generating function. -/
theorem row_anchored {n : ℕ} (x : Fin n) (u : ℝ) :
    row n u = ∑ a ∈ Icc 2 n,
      C (((n-1).choose (a-1)):ℝ) * (C (if a=2 then u else 1)*(X*eulerian (a-1))) *
        row (n-a) u := by
  let wt (σ : Perm (Fin n)) (a : ℕ) : ℝ[X] :=
    if Allowed 2 σ ∧ lengthAt σ x=a then term u σ else 0
  have split (σ : Perm (Fin n)) :
      (if Allowed 2 σ then term u σ else 0) = ∑ a ∈ Icc 2 n, wt σ a := by
    by_cases h : Allowed 2 σ
    · have lo := (allowed_iff_lengthAt σ).mp h x
      have hi : lengthAt σ x ≤ n := by
        simpa [lengthAt] using (Function.minimalPeriod_le_card (f := σ) (x := x))
      rw [sum_eq_single_of_mem (lengthAt σ x) (mem_Icc.mpr ⟨lo,hi⟩)]
      · simp [wt,h]
      · intro a _ ha
        simp [wt,ha.symm]
    · simp [wt,h]
  change (∑ σ, if Allowed 2 σ then term u σ else 0) = _
  simp_rw [split]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [←branch_weight x (mem_Icc.mp ha).1]
  unfold wt
  rw [←sum_filter]
  apply sum_subtype
  simp

#print axioms row_zero
#print axioms row_one
#print axioms row_anchored
end LongCycleBounds.MarkedTwo
