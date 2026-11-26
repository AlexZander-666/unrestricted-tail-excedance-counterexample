import LongCycleBounds.RankedSupport

/-! The exact contribution of an anchored shortest cycle and an arbitrary admissible complement. -/
noncomputable section
namespace LongCycleBounds.Insertion
open LongCycles Finset Equiv Polynomial
open scoped Classical

def anchoredSupports {n : ℕ} (x : Fin n) (k : ℕ) :=
  ((univ : Finset (Fin n)).powersetCard k).filter fun s ↦ ({x} : Finset (Fin n)) ⊆ s

private theorem anchor_data {n k : ℕ} {x : Fin n} (a : ↥(anchoredSupports x k)) :
    a.val.card=k ∧ x∈a.val := by
  obtain ⟨l,r⟩ := mem_filter.mp a.property
  exact ⟨(mem_powersetCard.mp l).2,r (mem_singleton_self _)⟩

private theorem compl_card {n k : ℕ} {x : Fin n} (a : ↥(anchoredSupports x k)) : a.valᶜ.card=n-k := by
  simp [card_compl,Fintype.card_fin,(anchor_data a).1]

abbrev AnchoredAssignments {n : ℕ} (x : Fin n) (k : ℕ) :=
  (a : ↥(anchoredSupports x k)) × (CyclesOn a.val × Admissible (n-k) k)

abbrev ShortBranch {n : ℕ} (x : Fin n) (k : ℕ) :=
  {τ : Perm (Fin n) // Allowed k τ ∧ lengthAt τ x=k}

instance {n : ℕ} (x : Fin n) (k : ℕ) : Fintype (ShortBranch x k) := Fintype.ofFinite _

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

private theorem join_iff {n k : ℕ} {x : Fin n} {a : ↥(anchoredSupports x k)} (c : CyclesOn a.val)
    (f : Perm (Fin (n-k))) :
    Allowed k (c.val*(placeEquiv a.valᶜ (compl_card a) f).val) ↔ Allowed k f := by
  let s := a.valᶜ
  let e := s.orderEmbOfFin (compl_card a)
  have rhs (i : Fin (n-k)) : lengthAt (c.val*(placeEquiv s (compl_card a) f).val) (e i) = lengthAt f i := by
    have dis := disj_placed c f
    rw [dis.commute.eq,len_mul_left dis.symm _ (Perm.notMem_support.mp (by
      rw [c.property.2]; exact mem_compl.mp (a.valᶜ.orderEmbOfFin_mem (compl_card a) i)))]
    exact lengthAt_place _ _ _ _
  rw [allowed_iff_lengthAt,allowed_iff_lengthAt]
  constructor
  · exact fun h i ↦ (rhs i) ▸ h (e i)
  · intro h y
    by_cases hy : y∈a.val
    · exact (join_length c f hy).ge
    · obtain ⟨i,hi⟩ : ∃ i, e i=y := by
        change y ∈ Set.range (s.orderEmbOfFin (compl_card a))
        rw [range_orderEmbOfFin]
        exact mem_compl.mpr hy
      subst y
      exact (rhs i).symm ▸ h i

private def join {n k : ℕ} {x : Fin n} (u : AnchoredAssignments x k) : ShortBranch x k :=
  let ⟨a,c,f⟩ := u
  ⟨c.val*(placeEquiv a.valᶜ (compl_card a) f.val).val,
    (join_iff c f.val).2 f.property,join_length c f.val (anchor_data a).2⟩

private theorem cycle_join {n k : ℕ} {x : Fin n} {a : ↥(anchoredSupports x k)} (c : CyclesOn a.val)
    (f : Perm (Fin (n-k))) :
    (c.val*(placeEquiv a.valᶜ (compl_card a) f).val).cycleOf x = c.val := by
  have hx := (anchor_data a).2
  have fixed := (placeEquiv a.valᶜ (compl_card a) f).property x (by simpa)
  exact (Perm.cycleOf_mul_of_apply_right_eq_self (disj_placed c f).commute x fixed).trans
    (c.property.1.cycleOf_eq (Perm.mem_support.mp (c.property.2.symm ▸ hx)))

private theorem join_inj {n k : ℕ} {x : Fin n} : Function.Injective (@join n k x) := by
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

private theorem join_surj {n k : ℕ} {x : Fin n} (hk : 2 ≤ k) : Function.Surjective (@join n k x) := by
  rintro ⟨σ,ok,atx⟩
  let c := σ.cycleOf x
  let d := σ*c⁻¹
  have moved := ne_fixed_of_allowed ok (by omega : 1<k) x
  have hx : x∈c.support := by simpa [c,Perm.mem_support] using moved
  have hc : c.IsCycle := Perm.isCycle_cycleOf _ moved
  have apart : d.Disjoint c := Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset
    (Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr moved))
  have prod : c*d=σ := by rw [←apart.commute.eq]; simp [d]
  have card : c.support.card=k := by
    rw [←len_cycle c hc hx,←atx,←prod,len_mul_left apart.symm x ((apart x).resolve_right (Perm.mem_support.mp hx))]
  let a : ↥(anchoredSupports x k) := ⟨c.support,mem_filter.mpr
    ⟨mem_powersetCard.mpr ⟨subset_univ _,card⟩,singleton_subset_iff.mpr hx⟩⟩
  let cyc : CyclesOn a.val := ⟨c,hc,rfl⟩
  let tail : Supported a.valᶜ := ⟨d,fun y hy ↦ (apart y).resolve_right (Perm.mem_support.mp (by
    change y∈a.val; simpa using hy))⟩
  let f := (placeEquiv a.valᶜ (compl_card a)).symm tail
  have placed : (placeEquiv a.valᶜ (compl_card a) f).val = d :=
    congrArg Subtype.val ((placeEquiv a.valᶜ (compl_card a)).apply_symm_apply tail)
  have assembled : cyc.val*(placeEquiv _ (compl_card a) f).val=σ := by rw [placed]; exact prod
  exact ⟨⟨a,cyc,⟨f,(join_iff cyc f).1 (assembled ▸ ok)⟩⟩,Subtype.ext assembled⟩

/-- Anchored cycles, with an independently ordered admissible complement, parametrize
the entire shortest-cycle branch for every ambient row. -/
def shortBranchEquiv {n k : ℕ} (x : Fin n) (hk : 2 ≤ k) : AnchoredAssignments x k ≃ ShortBranch x k :=
  Equiv.ofBijective join ⟨join_inj,join_surj hk⟩

theorem shortBranch_weight {n k : ℕ} (x : Fin n) (hk : 2≤k) :
    (∑ τ : ShortBranch x k, (X:Polynomial ℝ)^excedances τ.val) =
    C (((n-1).choose (k-1)):ℝ)*(X*eulerian (k-1))*enumerator (n-k) k := by
  rw [← (shortBranchEquiv x hk).sum_comp (fun τ ↦ (X:Polynomial ℝ)^excedances τ.val)]
  change (∑ u : AnchoredAssignments x k, (X:Polynomial ℝ)^excedances (join u).val) = _
  rw [Fintype.sum_sigma]
  have per (a : ↥(anchoredSupports x k)) :
      (∑ v : CyclesOn a.val × Admissible (n-k) k, (X:Polynomial ℝ)^excedances (join ⟨a,v⟩).val) =
      (X*eulerian (k-1))*enumerator (n-k) k := by
    rw [Fintype.sum_prod_type,enumerator_eq_admissible_sum]
    change (∑ c : CyclesOn a.val, ∑ f : Admissible (n-k) k,
      (X:Polynomial ℝ)^excedances (c.val*(placeEquiv a.valᶜ (compl_card a) f.val).val))=_
    simp_rw [excedances_disjoint_mul (disj_placed _ _),excedances_place,pow_add,←mul_sum,←sum_mul]
    rw [singleCycleWeight a.val ((anchor_data a).1.trans (by omega : k=k-1+1)) (by omega)]
  simp_rw [per]
  rw [sum_const,card_univ,Fintype.card_coe,anchoredSupports,card_filter_powersetCard_subset _ _ _ (singleton_subset_iff.mpr (mem_univ x))
    (by simpa using (show 1≤k by omega))]
  simp [nsmul_eq_mul,mul_assoc]

#print axioms shortBranchEquiv
#print axioms shortBranch_weight
end LongCycleBounds.Insertion
