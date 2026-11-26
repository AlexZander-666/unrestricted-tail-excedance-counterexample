import LongCycleBounds.AnchoredRows
import LongCycleBounds.BandMoments

/-! Distinguishing one actual cycle supplies the divisor for each ordered cycle row. -/

noncomputable section

namespace LongCycleBounds.CycleCount

open LongCycles Finset Equiv Polynomial Insertion
open scoped Classical

/-- Original admissible permutations with a specified number of genuine cycles. -/
abbrev Counted (n k h : ℕ) :=
  {σ : Perm (Fin n) // Allowed k σ ∧ σ.cycleType.card = h}

instance (n k h : ℕ) : Fintype (Counted n k h) := Fintype.ofFinite _

def cycleCountRow (n k h : ℕ) : ℝ[X] :=
  ∑ σ : Counted n k h, X ^ excedances σ.val

private abbrev Supports (n a : ℕ) := ↥((univ : Finset (Fin n)).powersetCard a)

private theorem support_card {n a : ℕ} (s : Supports n a) : s.val.card = a :=
  (mem_powersetCard.mp s.property).2

private theorem compl_card {n a : ℕ} (s : Supports n a) : s.valᶜ.card = n-a := by
  rw [card_compl, Fintype.card_fin, support_card s]

/-- Ranking a subset and extending by the identity preserves cycle type. -/
theorem cycleType_place {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m)
    (f : Perm (Fin m)) :
    (placeEquiv s hs f).val.cycleType = f.cycleType := by
  let e := (s.orderIsoOfFin hs).toEquiv
  have eq : (placeEquiv s hs f).val = f.extendDomain e := by
    apply Perm.ext
    intro y
    by_cases hy : y ∈ s
    · obtain ⟨i,hi⟩ := e.surjective ⟨y,hy⟩
      have hv : (e i : Fin n) = y := congrArg Subtype.val hi
      rw [←hv]
      rw [Perm.extendDomain_apply_image]
      exact place_image s hs f i
    · rw [(placeEquiv s hs f).property y hy, Perm.extendDomain_apply_not_subtype f e hy]
  rw [eq, Perm.cycleType_extendDomain]

private theorem disj_placed {n a : ℕ} {s : Supports n a} (d : CyclesOn s.val)
    (f : Perm (Fin (n-a))) : d.val.Disjoint (placeEquiv s.valᶜ (compl_card s) f).val := by
  intro y
  by_cases hy : y ∈ s.val
  · exact Or.inr ((placeEquiv _ _ _).property y (by simpa))
  · exact Or.inl (Perm.notMem_support.mp (d.property.2.symm ▸ hy))

private theorem allowed_join {n a k : ℕ} (hk : 2 ≤ k) (hka : k ≤ a)
    {s : Supports n a} (d : CyclesOn s.val) (f : Admissible (n-a) k) :
    Allowed k (d.val*(placeEquiv s.valᶜ (compl_card s) f.val).val) := by
  have h : s.val.Nonempty := card_pos.mp (by rw [support_card s]; omega)
  let x := s.val.min' h
  let anchor : ↥(anchoredSupports x a) := ⟨s.val, mem_filter.mpr
    ⟨s.property, singleton_subset_iff.mpr (s.val.min'_mem h)⟩⟩
  have proof := (Anchored.branchEquiv x hk hka ⟨anchor,d,f⟩).property.1
  exact proof

private theorem allowed_complement {n a k : ℕ} {s : Supports n a} {d : CyclesOn s.val}
    {f : Perm (Fin (n-a))}
    (ok : Allowed k (d.val*(placeEquiv s.valᶜ (compl_card s) f).val)) : Allowed k f := by
  intro i b hb bl returns
  let y := s.valᶜ.orderEmbOfFin (compl_card s) i
  have dis := disj_placed d f
  have not_mem : y ∉ d.val.support := by
    rw [d.property.2]
    exact mem_compl.mp (s.valᶜ.orderEmbOfFin_mem (compl_card s) i)
  have fixed : d.val y = y := Perm.notMem_support.mp not_mem
  apply ok y b hb bl
  rw [dis.commute.mul_pow, Perm.mul_apply]
  change (d.val^b) (((placeEquiv s.valᶜ (compl_card s) f).val^b)
    (s.valᶜ.orderEmbOfFin (compl_card s) i)) = y
  rw [place_pow_image, returns]
  exact Perm.pow_apply_eq_self_of_apply_eq_self fixed b

private theorem joined_count {n a : ℕ} {s : Supports n a} (c : CyclesOn s.val)
    (f : Perm (Fin (n-a))) :
    (c.val * (placeEquiv s.valᶜ (compl_card s) f).val).cycleType.card = f.cycleType.card + 1 := by
  rw [(disj_placed c f).cycleType_mul, Multiset.card_add, c.property.1.cycleType,
    Multiset.card_singleton, cycleType_place, Nat.add_comm]

private abbrev Assignments (n k h a : ℕ) :=
  (s : Supports n a) × (CyclesOn s.val × Counted (n-a) k h)

private abbrev Marked (n k h : ℕ) :=
  (σ : Counted n k (h+1)) × ↥σ.val.cycleFactorsFinset

private abbrev MarkedLength (n k h a : ℕ) :=
  {v : Marked n k h // v.2.val.support.card = a}

private instance (n k h a : ℕ) : Fintype (MarkedLength n k h a) := Fintype.ofFinite _

private def join {n k h a : ℕ} (hk : 2 ≤ k) (hka : k ≤ a)
    (u : Assignments n k h a) : MarkedLength n k h a :=
  let ⟨s,d,f⟩ := u
  let g := (placeEquiv s.valᶜ (compl_card s) f.val).val
  let σ : Counted n k (h+1) := ⟨d.val*g, allowed_join hk hka d ⟨f.val,f.property.1⟩,
    (joined_count d f.val).trans (congrArg (·+1) f.property.2)⟩
  ⟨⟨σ, ⟨d.val, by
    change d.val ∈ (d.val*g).cycleFactorsFinset
    rw [(disj_placed d f.val).cycleFactorsFinset_mul_eq_union,
      d.property.1.cycleFactorsFinset_eq_singleton]
    exact mem_union_left _ (mem_singleton_self _)⟩⟩, d.property.2 ▸ support_card s⟩

private theorem join_weight {n k h a : ℕ} (hk : 2 ≤ k) (hka : k ≤ a)
    (s : Supports n a) (d : CyclesOn s.val) (f : Counted (n-a) k h) :
    excedances (join hk hka ⟨s,d,f⟩).val.1.val = excedances d.val + excedances f.val := by
  change excedances (d.val * (placeEquiv s.valᶜ (compl_card s) f.val).val) = _
  rw [excedances_disjoint_mul (disj_placed d f.val), excedances_place]

private theorem join_inj {n a k h : ℕ} (hk : 2 ≤ k) (hka : k ≤ a) :
    Function.Injective (join (n := n) (h := h) hk hka) := by
  rintro ⟨s,d,f⟩ ⟨s',d',f'⟩ eq
  have hd := congrArg (fun v : MarkedLength n k h a ↦ v.val.2.val) eq
  change d.val = d'.val at hd
  have hs : s = s' := Subtype.ext (d.property.2.symm.trans
    ((congrArg Perm.support hd).trans d'.property.2))
  subst s'
  have hd' : d = d' := Subtype.ext hd
  subst d'
  have hf := congrArg (fun v : MarkedLength n k h a ↦ v.val.1.val) eq
  change d.val*(placeEquiv _ _ f.val).val = d.val*(placeEquiv _ _ f'.val).val at hf
  have hf' : f = f' := Subtype.ext ((placeEquiv s.valᶜ (compl_card s)).injective
    (Subtype.ext (mul_left_cancel hf)))
  subst f'
  rfl

private theorem marked_ext {n k h : ℕ} {u v : Marked n k h}
    (perm : u.1.val = v.1.val) (chosen : u.2.val = v.2.val) : u = v := by
  rcases u with ⟨u,c⟩
  rcases v with ⟨v,d⟩
  have uv : u=v := Subtype.ext perm
  subst v
  have cd : c=d := Subtype.ext chosen
  subst d
  rfl

private theorem join_surj {n a k h : ℕ} (hk : 2 ≤ k) (hka : k ≤ a) :
    Function.Surjective (join (n := n) (h := h) hk hka) := by
  rintro ⟨⟨σ,marked⟩,ha⟩
  let c := marked.val
  let g := σ.val*c⁻¹
  have hc : c.IsCycle := (Perm.mem_cycleFactorsFinset_iff.mp marked.property).1
  have dis : g.Disjoint c := Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset marked.property
  have prod : c*g=σ.val := by rw [←dis.commute.eq]; simp [g]
  let s : Supports n a := ⟨c.support,mem_powersetCard.mpr ⟨subset_univ _,ha⟩⟩
  let d : CyclesOn s.val := ⟨c,hc,rfl⟩
  let tail : Supported s.valᶜ := ⟨g,fun y hy ↦ (dis y).resolve_right (Perm.mem_support.mp (by
    change y ∈ s.val; simpa using hy))⟩
  let f := (placeEquiv s.valᶜ (compl_card s)).symm tail
  have placed : (placeEquiv s.valᶜ (compl_card s) f).val = g :=
    congrArg Subtype.val ((placeEquiv s.valᶜ (compl_card s)).apply_symm_apply tail)
  have assembled : d.val*(placeEquiv s.valᶜ (compl_card s) f).val = σ.val := by
    rw [placed]
    exact prod
  have ok : Allowed k f := allowed_complement (assembled ▸ σ.property.1)
  have count := joined_count d f
  rw [assembled,σ.property.2] at count
  let complement : Counted (n-a) k h := ⟨f,ok,by omega⟩
  refine ⟨⟨s,d,complement⟩, Subtype.ext (marked_ext ?_ ?_)⟩
  · exact assembled
  · rfl

private def markedEquiv {n a k h : ℕ} (hk : 2 ≤ k) (hka : k ≤ a) :
    Assignments n k h a ≃ MarkedLength n k h a :=
  Equiv.ofBijective (join hk hka) ⟨join_inj hk hka,join_surj hk hka⟩

private theorem weighted_marked_length {n a k h : ℕ} (hk : 2 ≤ k) (hka : k ≤ a) :
    (∑ v : MarkedLength n k h a, (X:ℝ[X])^excedances v.val.1.val) =
      C (n.choose a:ℝ) * (X*eulerian (a-1)) * cycleCountRow (n-a) k h := by
  rw [← (markedEquiv hk hka).sum_comp
    (fun v : MarkedLength n k h a ↦ (X:ℝ[X])^excedances v.val.1.val), Fintype.sum_sigma]
  have term (s : Supports n a) :
      (∑ u : CyclesOn s.val × Counted (n-a) k h, (X:ℝ[X])^excedances
        ((markedEquiv hk hka) ⟨s,u⟩).val.1.val) =
        (X*eulerian (a-1))*cycleCountRow (n-a) k h := by
    rw [Fintype.sum_prod_type]
    simp_rw [show ∀ (d : CyclesOn s.val) (f : Counted (n-a) k h),
      excedances ((markedEquiv hk hka) ⟨s,d,f⟩).val.1.val = excedances d.val + excedances f.val
      from join_weight hk hka s, pow_add, ←mul_sum, ←sum_mul]
    rw [singleCycleWeight s.val ((support_card s).trans (by omega : a=a-1+1)) (by omega)]
    rfl
  simp_rw [term]
  simp [Supports, card_powersetCard, nsmul_eq_mul, mul_assoc]

private theorem marked_split {n k h : ℕ} :
    (∑ v : Marked n k h, (X:ℝ[X])^excedances v.1.val) =
      ∑ a ∈ Icc k n, ∑ v : MarkedLength n k h a, (X:ℝ[X])^excedances v.val.1.val := by
  let W (v : Marked n k h) : ℝ[X] := X ^ excedances v.1.val
  let len (v : Marked n k h) := v.2.val.support.card
  have range (v : Marked n k h) : len v ∈ Icc k n := by
    have hlen : len v ∈ v.1.val.cycleType := by
      rw [Perm.cycleType,Multiset.mem_map]
      exact ⟨v.2.val,v.2.property,rfl⟩
    exact mem_Icc.mpr ⟨le_of_mem_cycleType v.1.property.1 hlen,
      by simpa [len] using v.2.val.support.card_le_univ⟩
  have per (v : Marked n k h) :
      W v = ∑ a ∈ Icc k n, if len v = a then W v else 0 := by
    rw [sum_eq_single_of_mem (len v) (range v)]
    · simp
    · intro _ _ he
      simp [he.symm]
  change (∑ v, W v) = _
  conv_lhs => arg 2; ext v; rw [per v]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [←sum_filter]
  apply sum_subtype
  simp [len]

private theorem marked_multiply (n k h : ℕ) :
    (∑ v : Marked n k h, (X:ℝ[X])^excedances v.1.val) =
      C ((h+1:ℕ):ℝ) * cycleCountRow n k (h+1) := by
  rw [Fintype.sum_sigma,cycleCountRow,mul_sum]
  apply sum_congr rfl
  intro σ _
  have count : σ.val.cycleFactorsFinset.card = h+1 := by
    change σ.val.cycleFactorsFinset.val.card = h+1
    simpa only [Perm.cycleType,Multiset.card_map] using σ.property.2
  simp only [sum_const,card_univ,Fintype.card_coe,count,nsmul_eq_mul,map_natCast]

/-- Selecting one of the h+1 actual cycles multiplies the row by h+1. Choosing
its support first gives the complete binomial sum with h cycles on the complement. -/
theorem cycleCountRow_succ {n k h : ℕ} (hk : 2 ≤ k) :
    C ((h+1:ℕ):ℝ) * cycleCountRow n k (h+1) =
      ∑ a ∈ Icc k n, C (n.choose a:ℝ)*(X*eulerian (a-1))*cycleCountRow (n-a) k h := by
  rw [←marked_multiply,marked_split]
  apply sum_congr rfl
  intro a ha
  exact weighted_marked_length hk (mem_Icc.mp ha).1

private theorem cycleCountRow_zero {n k : ℕ} (hk : 2 ≤ k) :
    cycleCountRow n k 0 = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n
    let id : Counted 0 k 0 := ⟨1, (fun x ↦ Fin.elim0 x), by simp⟩
    have all (σ : Counted 0 k 0) : σ=id :=
      Subtype.ext (Perm.card_cycleType_eq_zero.mp σ.property.2)
    let _ : Unique (Counted 0 k 0) := ⟨⟨id⟩,all⟩
    have weight (σ : Counted 0 k 0) : excedances σ.val=0 := by simp [excedances]
    simp only [cycleCountRow,weight,pow_zero,sum_const,card_univ,Fintype.card_unique,one_nsmul,
      if_true]
  · have no (σ : Counted n k 0) : False := by
      have h := LongCycles.ne_fixed_of_allowed σ.property.1 hk ⟨0,Nat.pos_of_ne_zero hn⟩
      rw [Perm.card_cycleType_eq_zero.mp σ.property.2, Perm.one_apply] at h
      contradiction
    let _ : IsEmpty (Counted n k 0) := ⟨no⟩
    simp [cycleCountRow,hn]

/-- Choose ordered supports recursively by the next support size, with the
binomial multiplicity computed among the remaining labels. -/
def orderedCycleRow (n k : ℕ) : ℕ → ℝ[X]
  | 0 => if n=0 then 1 else 0
  | h+1 => ∑ a ∈ Icc k n, C (n.choose a:ℝ)*(X*eulerian (a-1))*orderedCycleRow (n-a) k h
termination_by h => h

theorem factorial_mul_cycleCountRow {k : ℕ} (hk : 2 ≤ k) (h n : ℕ) :
    C (h.factorial:ℝ) * cycleCountRow n k h = orderedCycleRow n k h := by
  induction h generalizing n with
  | zero => simp [cycleCountRow_zero hk, orderedCycleRow]
  | succ h ih =>
    calc
      _ = C (h.factorial:ℝ) * (C ((h+1:ℕ):ℝ) * cycleCountRow n k (h+1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul, map_mul]
        ring
      _ = _ := by
        rw [cycleCountRow_succ hk, mul_sum, orderedCycleRow]
        apply sum_congr rfl
        intro a _
        rw [←ih]
        ring

/-- The actual h-cycle row is the ordered support sum divided by h!. -/
theorem cycleCountRow_eq_ordered {k : ℕ} (hk : 2 ≤ k) (n h : ℕ) :
    cycleCountRow n k h = C (1/(h.factorial:ℝ)) * orderedCycleRow n k h := by
  have fac : (h.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero h
  rw [←factorial_mul_cycleCountRow hk h n, ←mul_assoc, ←map_mul, one_div_mul_cancel fac,
    map_one, one_mul]

private theorem card_cutoff {n k : ℕ} (hk : 2 ≤ k) {σ : Perm (Fin n)} (ok : Allowed k σ) :
    σ.cycleType.card ≤ n/k := by
  have bound (s : Multiset ℕ) (lower : ∀ m ∈ s, k ≤ m) : s.card*k ≤ s.sum := by
    induction s using Multiset.induction with
    | empty => simp
    | cons a s ih =>
      have at_a : k ≤ a := lower a (Multiset.mem_cons_self ..)
      have at_tail := ih (fun m hm ↦ lower m (Multiset.mem_cons_of_mem hm))
      rw [Multiset.card_cons, Multiset.sum_cons, Nat.add_mul, one_mul]
      omega
  have sum : σ.cycleType.sum = n := by
    rw [Perm.sum_cycleType,support_univ_of_allowed ok hk,card_univ,Fintype.card_fin]
  apply (Nat.le_div_iff_mul_le (by omega : 0<k)).2
  exact (bound _ (fun _ hm ↦ le_of_mem_cycleType ok hm)).trans_eq sum

/-- All original admissible permutations are included in the cycle-count rows. -/
theorem enumerator_sum_cycleCountRow {n k : ℕ} (hk : 2 ≤ k) :
    enumerator n k = ∑ h ∈ range (n/k+1), cycleCountRow n k h := by
  let W (σ : Perm (Fin n)) : ℝ[X] := X ^ excedances σ
  have per (σ : Perm (Fin n)) :
      (if Allowed k σ then W σ else 0) =
        ∑ h ∈ range (n/k+1), if Allowed k σ ∧ σ.cycleType.card=h then W σ else 0 := by
    by_cases ok : Allowed k σ
    · rw [sum_eq_single_of_mem σ.cycleType.card (mem_range.mpr (Nat.lt_succ_of_le (card_cutoff hk ok)))]
      · simp [ok]
      · intro h _ he
        simp [he.symm]
    · simp [ok]
  change (∑ σ, if Allowed k σ then W σ else 0) = _
  simp_rw [per]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  rw [←sum_filter,cycleCountRow]
  apply sum_subtype
  simp

theorem enumerator_ordered_cycle_rows {n k : ℕ} (hk : 2 ≤ k) :
    enumerator n k = ∑ h ∈ range (n/k+1), C (1/(h.factorial:ℝ))*orderedCycleRow n k h := by
  rw [enumerator_sum_cycleCountRow hk]
  exact sum_congr rfl fun h _ ↦ cycleCountRow_eq_ordered hk n h

/-- The ordered binomial support sum applied to a real sequence of cycle moments. -/
def orderedMomentRow (M : ℕ → ℝ) (n k : ℕ) : ℕ → ℝ
  | 0 => if n=0 then 1 else 0
  | h+1 => ∑ a ∈ Icc k n, (n.choose a:ℝ) * M a * orderedMomentRow M (n-a) k h
termination_by h => h

theorem orderedCycleRow_moment_eval (n k h : ℕ) (t : ℝ) :
    (orderedCycleRow n k h).eval t / (1-t)^n =
      orderedMomentRow (fun a ↦ Band.moment a t) n k h := by
  induction h generalizing n with
  | zero =>
    by_cases hn : n=0 <;> simp [orderedCycleRow, orderedMomentRow, hn]
  | succ h ih =>
    rw [orderedCycleRow, orderedMomentRow, eval_finsetSum, Finset.sum_div]
    apply sum_congr rfl
    intro a ha
    have le := (mem_Icc.mp ha).2
    have power : (1-t)^n = (1-t)^a * (1-t)^(n-a) := by
      rw [←pow_add, Nat.add_sub_of_le le]
    rw [eval_mul, eval_mul, eval_mul, eval_C, eval_X, power, ←ih]
    unfold Band.moment
    ring

/-- The actual insertion-normalized row, expanded over every possible cycle count. -/
theorem normalizedEnumerator_ordered_cycle_rows {n k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    Band.normalizedEnumerator n k x =
      ∑ h ∈ range (n/k+1), (1/(h.factorial:ℝ))*orderedMomentRow (fun a ↦ Band.cycleMoment a x) n k h := by
  dsimp only [Band.normalizedEnumerator, Band.cycleMoment]
  rw [enumerator_ordered_cycle_rows hk, eval_finsetSum, Finset.sum_div]
  simp only [eval_mul,eval_C,mul_div_assoc,orderedCycleRow_moment_eval]

#print axioms cycleType_place
#print axioms cycleCountRow_succ
#print axioms factorial_mul_cycleCountRow
#print axioms cycleCountRow_eq_ordered
#print axioms enumerator_sum_cycleCountRow
#print axioms enumerator_ordered_cycle_rows
#print axioms orderedCycleRow_moment_eval
#print axioms normalizedEnumerator_ordered_cycle_rows

end LongCycleBounds.CycleCount
