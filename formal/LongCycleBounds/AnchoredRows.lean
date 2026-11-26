import LongCycleBounds.UniversalShortBranch

/-! The exact contribution of an anchored cycle of prescribed length and an arbitrary admissible complement. -/
noncomputable section
namespace LongCycleBounds.Anchored
open LongCycles Finset Equiv Polynomial Insertion
open scoped Classical

private theorem anchor_data {n k : ℕ} {x : Fin n} (a : ↥(anchoredSupports x k)) :
    a.val.card=k ∧ x∈a.val := by
  obtain ⟨l,r⟩ := mem_filter.mp a.property
  exact ⟨(mem_powersetCard.mp l).2,r (mem_singleton_self _)⟩

private theorem compl_card {n k : ℕ} {x : Fin n} (a : ↥(anchoredSupports x k)) : a.valᶜ.card=n-k := by
  simp [card_compl,Fintype.card_fin,(anchor_data a).1]

abbrev Assignments {n : ℕ} (x : Fin n) (a k : ℕ) :=
  (s : ↥(anchoredSupports x a)) × (CyclesOn s.val × Admissible (n-a) k)

abbrev Branch {n : ℕ} (x : Fin n) (a k : ℕ) :=
  {τ : Perm (Fin n) // Allowed k τ ∧ lengthAt τ x=a}

instance {n : ℕ} (x : Fin n) (a k : ℕ) : Fintype (Branch x a k) := Fintype.ofFinite _

private theorem disj_placed {n k : ℕ} {x : Fin n} {a : ↥(anchoredSupports x k)}
    (c : CyclesOn a.val) (f : Perm (Fin (n-k))) :
    c.val.Disjoint (placeEquiv a.valᶜ (compl_card a) f).val := by
  intro y
  by_cases h : y∈a.val
  · exact Or.inr ((placeEquiv _ _ _).property _ (by simpa))
  · exact Or.inl (Perm.notMem_support.mp (c.property.2.symm ▸ h))

private theorem len_mul_left {n : ℕ} {c d : Perm (Fin n)} (cd : c.Disjoint d)
    (x : Fin n) (hx : d x=x) : lengthAt (c*d) x=lengthAt c x := by
  have same (j : ℕ) : ((c*d)^j) x=(c^j) x := by
    rw [cd.commute.mul_pow,Perm.mul_apply,Perm.pow_apply_eq_self_of_apply_eq_self hx]
  exact le_antisymm (lengthAt_le_return _ _ (lengthAt_pos _ _) ((same _).trans (pow_lengthAt _ _)))
    (lengthAt_le_return _ _ (lengthAt_pos _ _) ((same _).symm.trans (pow_lengthAt _ _)))

private theorem len_cycle {n : ℕ} (c : Perm (Fin n)) (hc : c.IsCycle) {y : Fin n} (hy : y∈c.support) :
    lengthAt c y=c.support.card := by
  have onS : c.IsCycleOn (↑c.support : Set (Fin n)) := by
    have eq : (↑c.support : Set (Fin n)) = {y | c y ≠ y} := by ext y; exact Perm.mem_support
    rw [eq]; exact hc.isCycleOn
  exact le_antisymm (lengthAt_le_return _ _ (card_pos.mpr ⟨_,hy⟩) ((onS.pow_apply_eq hy).mpr dvd_rfl))
    (Nat.le_of_dvd (lengthAt_pos _ _) (onS.pow_apply_eq hy |>.mp (pow_lengthAt _ _)))

private theorem join_length {n k : ℕ} {x : Fin n} {a : ↥(anchoredSupports x k)} (c : CyclesOn a.val)
    (f : Perm (Fin (n-k))) {y : Fin n} (hy : y∈a.val) :
    lengthAt (c.val*(placeEquiv a.valᶜ (compl_card a) f).val) y=k := by
  rw [len_mul_left (disj_placed c f) _ ((placeEquiv _ _ f).property y (by simpa using hy)),
    len_cycle _ c.property.1 (c.property.2.symm ▸ hy),c.property.2,(anchor_data a).1]

private theorem join_iff {n a k : ℕ} (hka : k ≤ a) {x : Fin n} {s : ↥(anchoredSupports x a)} (c : CyclesOn s.val)
    (f : Perm (Fin (n-a))) :
    Allowed k (c.val*(placeEquiv s.valᶜ (compl_card s) f).val) ↔ Allowed k f := by
  let t := s.valᶜ
  let e := t.orderEmbOfFin (compl_card s)
  have rhs (i : Fin (n-a)) : lengthAt (c.val*(placeEquiv t (compl_card s) f).val) (e i) =
      lengthAt f i := by
    have dis := disj_placed c f
    rw [dis.commute.eq,len_mul_left dis.symm _ (Perm.notMem_support.mp (by
      rw [c.property.2]; exact mem_compl.mp (s.valᶜ.orderEmbOfFin_mem (compl_card s) i)))]
    exact lengthAt_place _ _ _ _
  rw [allowed_iff_lengthAt,allowed_iff_lengthAt]
  constructor
  · exact fun h i ↦ (rhs i) ▸ h (e i)
  · intro h y
    by_cases hy : y∈s.val
    · exact hka.trans (join_length c f hy).ge
    · obtain ⟨i,hi⟩ : ∃ i, e i=y := by
        change y ∈ Set.range (t.orderEmbOfFin (compl_card s))
        rw [range_orderEmbOfFin]
        exact mem_compl.mpr hy
      subst y
      exact (rhs i).symm ▸ h i

private def join {n a k : ℕ} (hka : k ≤ a) {x : Fin n}
    (u : Assignments x a k) : Branch x a k :=
  let ⟨s,c,f⟩ := u
  ⟨c.val*(placeEquiv s.valᶜ (compl_card s) f.val).val,
    (join_iff hka c f.val).2 f.property,join_length c f.val (anchor_data s).2⟩

private theorem cycle_join {n k : ℕ} {x : Fin n} {a : ↥(anchoredSupports x k)} (c : CyclesOn a.val)
    (f : Perm (Fin (n-k))) :
    (c.val*(placeEquiv a.valᶜ (compl_card a) f).val).cycleOf x = c.val := by
  have hx := (anchor_data a).2
  have fixed := (placeEquiv a.valᶜ (compl_card a) f).property x (by simpa)
  exact (Perm.cycleOf_mul_of_apply_right_eq_self (disj_placed c f).commute x fixed).trans
    (c.property.1.cycleOf_eq (Perm.mem_support.mp (c.property.2.symm ▸ hx)))

private theorem join_inj {n a k : ℕ} (hka : k ≤ a) {x : Fin n} :
    Function.Injective (@join n a k hka x) := by
  rintro ⟨a,c,f⟩ ⟨b,d,g⟩ eq
  have e := congrArg Subtype.val eq
  change c.val*(placeEquiv _ _ f.val).val=d.val*(placeEquiv _ _ g.val).val at e
  have h := congrArg (fun σ : Perm (Fin n) ↦ σ.cycleOf x) e
  rw [cycle_join,cycle_join] at h
  have ab : a=b := Subtype.ext (c.property.2.symm.trans ((congrArg Perm.support h).trans d.property.2))
  subst b
  have cd : c=d := Subtype.ext h
  subst d
  have fg : f=g := Subtype.ext ((placeEquiv a.valᶜ (compl_card a)).injective (Subtype.ext (mul_left_cancel e)))
  subst g
  rfl

private theorem join_surj {n a k : ℕ} {x : Fin n} (hk : 2 ≤ k) (hka : k ≤ a) : Function.Surjective (@join n a k hka x) := by
  rintro ⟨σ,ok,atx⟩
  let c := σ.cycleOf x
  let d := σ*c⁻¹
  have moved := ne_fixed_of_allowed ok (by omega : 1<k) x
  have hx : x∈c.support := by simpa [c,Perm.mem_support] using moved
  have hc : c.IsCycle := Perm.isCycle_cycleOf _ moved
  have apart : d.Disjoint c := Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset
    (Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr moved))
  have prod : c*d=σ := by rw [←apart.commute.eq]; simp [d]
  have card : c.support.card=a := by
    rw [←len_cycle c hc hx,←atx,←prod,len_mul_left apart.symm x ((apart x).resolve_right (Perm.mem_support.mp hx))]
  let s : ↥(anchoredSupports x a) := ⟨c.support,mem_filter.mpr
    ⟨mem_powersetCard.mpr ⟨subset_univ _,card⟩,singleton_subset_iff.mpr hx⟩⟩
  let cyc : CyclesOn s.val := ⟨c,hc,rfl⟩
  let tail : Supported s.valᶜ := ⟨d,fun y hy ↦ (apart y).resolve_right (Perm.mem_support.mp (by
    change y∈s.val; simpa using hy))⟩
  let f := (placeEquiv s.valᶜ (compl_card s)).symm tail
  have placed : (placeEquiv s.valᶜ (compl_card s) f).val = d :=
    congrArg Subtype.val ((placeEquiv s.valᶜ (compl_card s)).apply_symm_apply tail)
  have assembled : cyc.val*(placeEquiv _ (compl_card s) f).val=σ := by rw [placed]; exact prod
  exact ⟨⟨s,cyc,⟨f,(join_iff hka cyc f).1 (assembled ▸ ok)⟩⟩,Subtype.ext assembled⟩

/-- A cycle through the anchor is recovered together with the independently
ranked admissible permutation of its complement. -/
def branchEquiv {n a k : ℕ} (x : Fin n) (hk : 2 ≤ k) (hka : k ≤ a) :
    Assignments x a k ≃ Branch x a k :=
  Equiv.ofBijective (join hka) ⟨join_inj hka,join_surj hk hka⟩

theorem branch_weight {n a k : ℕ} (x : Fin n) (hk : 2 ≤ k) (hka : k ≤ a) :
    (∑ τ : Branch x a k, (X:Polynomial ℝ)^excedances τ.val) =
    C (((n-1).choose (a-1)):ℝ)*(X*eulerian (a-1))*enumerator (n-a) k := by
  rw [← (branchEquiv x hk hka).sum_comp (fun τ ↦ (X:Polynomial ℝ)^excedances τ.val)]
  change (∑ u : Assignments x a k, (X:Polynomial ℝ)^excedances (join hka u).val) = _
  rw [Fintype.sum_sigma]
  have per (s : ↥(anchoredSupports x a)) :
      (∑ v : CyclesOn s.val × Admissible (n-a) k,
        (X:Polynomial ℝ)^excedances (join hka ⟨s,v⟩).val) =
      (X*eulerian (a-1))*enumerator (n-a) k := by
    rw [Fintype.sum_prod_type,enumerator_eq_admissible_sum]
    change (∑ c : CyclesOn s.val, ∑ f : Admissible (n-a) k,
      (X:Polynomial ℝ)^excedances (c.val*(placeEquiv s.valᶜ (compl_card s) f.val).val))=_
    simp_rw [excedances_disjoint_mul (disj_placed _ _),excedances_place,pow_add,←mul_sum,←sum_mul]
    rw [singleCycleWeight s.val ((anchor_data s).1.trans (by omega : a=a-1+1)) (by omega)]
  simp_rw [per]
  rw [sum_const,card_univ,Fintype.card_coe,anchoredSupports,card_filter_powersetCard_subset _ _ _
    (singleton_subset_iff.mpr (mem_univ x)) (by simpa using (show 1≤a by omega))]
  simp [nsmul_eq_mul,mul_assoc]

/-- Partition the original enumerator according to the length of the cycle
through a given label. The cutoff on the complementary permutation remains k. -/
theorem anchored_row_recurrence {n k : ℕ} (hk : 2 ≤ k) (x : Fin n) :
    enumerator n k = ∑ a ∈ Icc k n,
      C (((n-1).choose (a-1)):ℝ)*(X*eulerian (a-1))*enumerator (n-a) k := by
  let wt (σ : Perm (Fin n)) : ℝ[X] := X ^ excedances σ
  let term (σ : Perm (Fin n)) (a : ℕ) : ℝ[X] :=
    if Allowed k σ ∧ lengthAt σ x = a then wt σ else 0
  have split (σ : Perm (Fin n)) :
      (if Allowed k σ then wt σ else 0) = ∑ a ∈ Icc k n, term σ a := by
    by_cases h : Allowed k σ
    · have hl := (allowed_iff_lengthAt σ).mp h x
      have hu : lengthAt σ x ≤ n := by
        simpa [lengthAt] using (Function.minimalPeriod_le_card (f := σ) (x := x))
      rw [sum_eq_single_of_mem (lengthAt σ x) (mem_Icc.mpr ⟨hl,hu⟩)]
      · simp [term,h]
      · intro a _ ha
        simp [term,ha.symm]
    · simp [term,h]
  change (∑ σ, if Allowed k σ then wt σ else 0) = _
  simp_rw [split]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [← branch_weight x hk (mem_Icc.mp ha).1]
  unfold term
  rw [← sum_filter]
  apply sum_subtype
  simp

#print axioms branchEquiv
#print axioms branch_weight
#print axioms anchored_row_recurrence

end LongCycleBounds.Anchored
