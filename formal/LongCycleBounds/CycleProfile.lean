import LongCycleBounds.GeneralCycleSupports
import LongCycles.PermCycleBridge

/-! Excedance rows for derangements weighted multiplicatively by their nontrivial cycle lengths. -/
noncomputable section
namespace LongCycleBounds.CycleProfile
open LongCycles Equiv Finset Polynomial Insertion
open scoped Classical

def cycleWeight {n : ℕ} (w : ℕ → ℝ) (σ : Perm (Fin n)) : ℝ :=
  (σ.cycleType.map w).prod

def term {n : ℕ} (w : ℕ → ℝ) (σ : Perm (Fin n)) : ℝ[X] :=
  C (cycleWeight w σ) * X^excedances σ

def row (n : ℕ) (w : ℕ → ℝ) : ℝ[X] :=
  ∑ σ : Perm (Fin n), if Allowed 2 σ then term w σ else 0

def profile (k : ℕ) (u : ℝ) (a : ℕ) : ℝ := if a < k then u else 1

theorem row_one (n k : ℕ) : row n (profile k 1) = enumerator n 2 := by
  have mark : profile k 1 = fun _ ↦ 1 := by funext a; simp [profile]
  simp only [mark,row,term,cycleWeight,Multiset.prod_map_one,map_one,one_mul,enumerator]

private theorem zero_profile_product (m : Multiset ℕ) (k : ℕ) :
    (m.map (profile k 0)).prod = if ∀ a∈m, k≤a then 1 else 0 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases h : a<k <;> by_cases rest : ∀ b∈m,k≤b <;>
      simp [profile,h,ih,rest,show (k≤a) ↔ ¬a<k by omega,Multiset.mem_cons]

theorem row_zero (n : ℕ) {k : ℕ} (hk : 2≤k) : row n (profile k 0) = enumerator n k := by
  unfold row enumerator
  apply sum_congr rfl
  intro σ _
  by_cases h : Allowed k σ
  · have h2 : Allowed 2 σ := fun i j pos lt ↦ h i j pos (by omega)
    have all : ∀ a∈σ.cycleType, k≤a := fun _ ha ↦ le_of_mem_cycleType h ha
    rw [if_pos h2,if_pos h]
    unfold term cycleWeight
    rw [zero_profile_product, if_pos all]
    simp
  · by_cases h2 : Allowed 2 σ
    · have no : ¬∀ a∈σ.cycleType,k≤a := fun all ↦ h
          (allowed_of_cycleType_lower (support_univ_of_allowed h2 (by decide)) all)
      simp [h,h2,term,cycleWeight,zero_profile_product,no]
    · simp [h,h2]

theorem row_admissible (n : ℕ) (w : ℕ → ℝ) :
    row n w = ∑ σ : Admissible n 2, term w σ.val := by
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

private theorem joined_weight {n a : ℕ} {x : Fin n} (ha : 2 ≤ a) (s : ↥(anchoredSupports x a))
    (c : CyclesOn s.val) (f : Admissible (n-a) 2) (w : ℕ → ℝ) :
    cycleWeight w (Anchored.branchEquiv x (by decide : 2 ≤ 2) ha ⟨s,c,f⟩).val =
      w a * cycleWeight w f.val := by
  change (((c.val*(placeEquiv s.valᶜ (compl_card s) f.val).val).cycleType).map w).prod = _
  rw [(disjoint_place c f.val).cycleType_mul, Multiset.map_add, Multiset.prod_add,
    c.property.1.cycleType, c.property.2, (anchor_data s).1, CycleCount.cycleType_place]
  simp [cycleWeight]

private theorem joined_term {n a : ℕ} {x : Fin n} (ha : 2 ≤ a) (s : ↥(anchoredSupports x a))
    (c : CyclesOn s.val) (f : Admissible (n-a) 2) (w : ℕ → ℝ) :
    term w (Anchored.branchEquiv x (by decide : 2 ≤ 2) ha ⟨s,c,f⟩).val =
      C (w a) * X^excedances c.val * term w f.val := by
  unfold term
  rw [joined_weight ha s c f,map_mul]
  change _ * X^excedances (c.val*(placeEquiv s.valᶜ (compl_card s) f.val).val) = _
  rw [excedances_disjoint_mul (disjoint_place c f.val),excedances_place,pow_add]
  ring

theorem branch_weight {n a : ℕ} (x : Fin n) (ha : 2 ≤ a) (w : ℕ → ℝ) :
    (∑ τ : Anchored.Branch x a 2, term w τ.val) =
      C (((n-1).choose (a-1)):ℝ) * (C (w a)*(X*eulerian (a-1))) *
        row (n-a) w := by
  rw [← (Anchored.branchEquiv x (by decide : 2≤2) ha).sum_comp (fun τ ↦ term w τ.val)]
  rw [Fintype.sum_sigma]
  have per (s : ↥(anchoredSupports x a)) :
      (∑ v : CyclesOn s.val × Admissible (n-a) 2,
        term w (Anchored.branchEquiv x (by decide : 2≤2) ha ⟨s,v⟩).val) =
        (C (w a)*(X*eulerian (a-1)))*row (n-a) w := by
    rw [Fintype.sum_prod_type,row_admissible]
    simp_rw [joined_term ha s _ _ w,←mul_sum,←sum_mul,←mul_sum]
    rw [singleCycleWeight s.val ((anchor_data s).1.trans (by omega : a=a-1+1)) (by omega)]
  simp_rw [per]
  rw [sum_const,card_univ,Fintype.card_coe,anchoredSupports,card_filter_powersetCard_subset _ _ _
    (singleton_subset_iff.mpr (mem_univ x)) (by simpa using (show 1≤a by omega))]
  simp [nsmul_eq_mul,mul_assoc]

/-- Coefficient recurrence from removing the entire cycle through a specified label.
It determines every coefficient of the exponential generating function. -/
theorem row_anchored {n : ℕ} (x : Fin n) (w : ℕ → ℝ) :
    row n w = ∑ a ∈ Icc 2 n,
      C (((n-1).choose (a-1)):ℝ) * (C (w a)*(X*eulerian (a-1))) *
        row (n-a) w := by
  let wt (σ : Perm (Fin n)) (a : ℕ) : ℝ[X] :=
    if Allowed 2 σ ∧ lengthAt σ x=a then term w σ else 0
  have split (σ : Perm (Fin n)) :
      (if Allowed 2 σ then term w σ else 0) = ∑ a ∈ Icc 2 n, wt σ a := by
    by_cases h : Allowed 2 σ
    · have lo := (allowed_iff_lengthAt σ).mp h x
      have hi : lengthAt σ x ≤ n := by
        simpa [lengthAt] using (Function.minimalPeriod_le_card (f := σ) (x := x))
      rw [sum_eq_single_of_mem (lengthAt σ x) (mem_Icc.mpr ⟨lo,hi⟩)]
      · simp [wt,h]
      · intro a _ ha
        simp [wt,ha.symm]
    · simp [wt,h]
  change (∑ σ, if Allowed 2 σ then term w σ else 0) = _
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
end LongCycleBounds.CycleProfile
