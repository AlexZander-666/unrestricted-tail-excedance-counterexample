import LongCycleBounds.BandMoments

/-! At length three times the cutoff, counting three genuine cycles with equal supports. -/

noncomputable section

namespace LongCycleBounds.Band

open Finset LongCycles Polynomial
open scoped Classical

private def anchoredSupports {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (x : Fin n) :=
  (s.powersetCard k).filter fun t ↦ ({x} : Finset (Fin n)) ⊆ t

private theorem anchor_props {n k : ℕ} {s : Finset (Fin n)} {x : Fin n}
    (t : ↥(anchoredSupports s k x)) : t.val ⊆ s ∧ t.val.card = k ∧ x ∈ t.val := by
  have h := mem_filter.mp t.property
  exact ⟨(mem_powersetCard.mp h.1).1, (mem_powersetCard.mp h.1).2,
    h.2 (mem_singleton_self _)⟩

private theorem card_anchor {n k : ℕ} {s : Finset (Fin n)} {x : Fin n} (hx : x ∈ s)
    (hk : 1 ≤ k) : (anchoredSupports s k x).card = (s.card-1).choose (k-1) := by
  rw [anchoredSupports, card_filter_powersetCard_subset _ _ _ (singleton_subset_iff.mpr hx)
    (by simpa using hk)]
  simp

private abbrev FirstSupport (k : ℕ) (x : Fin (3*k)) :=
  ↥(anchoredSupports univ k x)

private theorem first_compl_card {k : ℕ} {x : Fin (3*k)} (a : FirstSupport k x) :
    a.valᶜ.card = 2*k := by
  rw [card_compl, Fintype.card_fin, (anchor_props a).2.1]
  omega

private def secondAnchor {k : ℕ} {x : Fin (3*k)} (hk : 2 ≤ k) (a : FirstSupport k x) :=
  a.valᶜ.min' (card_pos.mp (by rw [first_compl_card]; omega))

private theorem secondAnchor_mem {k : ℕ} {x : Fin (3*k)} (hk : 2 ≤ k) (a : FirstSupport k x) :
    secondAnchor hk a ∈ a.valᶜ := min'_mem _ _

private abbrev SecondSupport {k : ℕ} {x : Fin (3*k)} (hk : 2 ≤ k) (a : FirstSupport k x) :=
  ↥(anchoredSupports a.valᶜ k (secondAnchor hk a))

private theorem third_card {k : ℕ} {x : Fin (3*k)} {hk : 2 ≤ k} (a : FirstSupport k x)
    (b : SecondSupport hk a) : (a.valᶜ \ b.val).card = k := by
  rw [card_sdiff_of_subset (anchor_props b).1, first_compl_card, (anchor_props b).2.1]
  omega

private abbrev Choices {k : ℕ} (hk : 2 ≤ k) (x : Fin (3*k)) :=
  (a : FirstSupport k x) × (b : SecondSupport hk a) ×
    (CyclesOn a.val × CyclesOn b.val × CyclesOn (a.valᶜ \ b.val))

private abbrev Triples (k : ℕ) :=
  {σ : Equiv.Perm (Fin (3*k)) // σ.cycleType = {k,k,k}}

private theorem apart {n : ℕ} {a b : Finset (Fin n)} (c : CyclesOn a) (d : CyclesOn b)
    (h : Disjoint a b) : c.val.Disjoint d.val := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, c.property.2, d.property.2]
  exact h

private theorem disj_first_tail {k : ℕ} {x : Fin (3*k)} {hk : 2 ≤ k} {a : FirstSupport k x}
    {b : SecondSupport hk a} (c : CyclesOn a.val) (d : CyclesOn b.val)
    (e : CyclesOn (a.valᶜ \ b.val)) : c.val.Disjoint (d.val * e.val) := by
  have hd := apart c d (disjoint_of_subset_right (anchor_props b).1 disjoint_compl_right)
  have he := apart c e (disjoint_of_subset_right sdiff_subset disjoint_compl_right)
  exact hd.mul_right he

private theorem disj_second_third {k : ℕ} {x : Fin (3*k)} {hk : 2 ≤ k} {a : FirstSupport k x}
    {b : SecondSupport hk a} (d : CyclesOn b.val) (e : CyclesOn (a.valᶜ \ b.val)) :
    d.val.Disjoint e.val := apart d e disjoint_sdiff_self_right

private def join {k : ℕ} {hk : 2 ≤ k} {x : Fin (3*k)} (u : Choices hk x) : Triples k :=
  let ⟨a, b, c, d, e⟩ := u
  ⟨c.val * (d.val * e.val), by
    rw [(disj_first_tail c d e).cycleType_mul, (disj_second_third d e).cycleType_mul,
      c.property.1.cycleType, d.property.1.cycleType, e.property.1.cycleType,
      c.property.2, d.property.2, e.property.2, (anchor_props a).2.1,
      (anchor_props b).2.1, third_card a b]
    rfl⟩

private theorem cycleOf_left {n : ℕ} {u v : Equiv.Perm (Fin n)} {x : Fin n}
    (hd : u.Disjoint v) (hc : u.IsCycle) (hx : x ∈ u.support) :
    (u*v).cycleOf x = u := by
  have hf : v x = x := (hd x).resolve_left (Equiv.Perm.mem_support.mp hx)
  exact (Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hd.commute x hf).trans
    (hc.cycleOf_eq (Equiv.Perm.mem_support.mp hx))

private theorem join_inj {k : ℕ} {hk : 2 ≤ k} {x : Fin (3*k)} :
    Function.Injective (@join k hk x) := by
  rintro ⟨a,b,c,d,e⟩ ⟨a',b',c',d',e'⟩ eq
  have hprod := congrArg Subtype.val eq
  change c.val * (d.val * e.val) = c'.val * (d'.val * e'.val) at hprod
  have hxc : x ∈ c.val.support := c.property.2.symm ▸ (anchor_props a).2.2
  have hxc' : x ∈ c'.val.support := c'.property.2.symm ▸ (anchor_props a').2.2
  have hc := congrArg (fun u : Equiv.Perm (Fin (3*k)) ↦ u.cycleOf x) hprod
  rw [cycleOf_left (disj_first_tail c d e) c.property.1 hxc,
    cycleOf_left (disj_first_tail c' d' e') c'.property.1 hxc'] at hc
  have ha : a = a' := Subtype.ext (c.property.2.symm.trans
    ((congrArg Equiv.Perm.support hc).trans c'.property.2))
  subst a'
  have hcc : c = c' := Subtype.ext hc
  subst c'
  have htail := mul_left_cancel hprod
  have hxd : secondAnchor hk a ∈ d.val.support := d.property.2.symm ▸ (anchor_props b).2.2
  have hxd' : secondAnchor hk a ∈ d'.val.support := d'.property.2.symm ▸ (anchor_props b').2.2
  have hd := congrArg (fun u : Equiv.Perm (Fin (3*k)) ↦ u.cycleOf (secondAnchor hk a)) htail
  rw [cycleOf_left (disj_second_third d e) d.property.1 hxd,
    cycleOf_left (disj_second_third d' e') d'.property.1 hxd'] at hd
  have hb : b = b' := Subtype.ext (d.property.2.symm.trans
    ((congrArg Equiv.Perm.support hd).trans d'.property.2))
  subst b'
  have hdd : d = d' := Subtype.ext hd
  subst d'
  have he : e = e' := Subtype.ext (mul_left_cancel htail)
  subst e'
  rfl

private theorem splitAt {n k : ℕ} {σ : Equiv.Perm (Fin n)} {x : Fin n}
    (hx : x ∈ σ.support) {lengths : Multiset ℕ} (htype : σ.cycleType = {k} + lengths)
    (hconst : ∀ a ∈ σ.cycleType, a = k) :
    ∃ c d : Equiv.Perm (Fin n), σ = c*d ∧ c.Disjoint d ∧ c.IsCycle ∧
      x ∈ c.support ∧ c.support.card = k ∧ d.cycleType = lengths := by
  let c := σ.cycleOf x
  let d := σ*c⁻¹
  have hc : c.IsCycle := Equiv.Perm.isCycle_cycleOf _ (Equiv.Perm.mem_support.mp hx)
  have hm : c ∈ σ.cycleFactorsFinset := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
  have hd : d.Disjoint c := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hm
  have hcx : x ∈ c.support := by
    simpa [c, Equiv.Perm.mem_support] using hx
  have hck : c.support.card = k := by
    apply hconst
    rw [Equiv.Perm.cycleType, Multiset.mem_map]
    exact ⟨c, hm, rfl⟩
  have hcd : σ = c*d := by
    rw [← hd.commute.eq]
    simp [d]
  have tail : d.cycleType = lengths := by
    have he : ({k} : Multiset ℕ) + d.cycleType = {k} + lengths := by
      rw [← htype, hcd, hd.symm.cycleType_mul, hc.cycleType, hck]
    exact add_left_cancel he
  exact ⟨c,d,hcd,hd.symm,hc,hcx,hck,tail⟩

private theorem support_sdiff {n : ℕ} {c d : Equiv.Perm (Fin n)}
    (hd : c.Disjoint d) : d.support = (c*d).support \ c.support := by
  rw [hd.support_mul]
  ext x
  simp only [mem_sdiff, mem_union]
  have apart : x ∈ c.support → x ∉ d.support := fun h ↦ disjoint_left.mp hd.disjoint_support h
  tauto

private theorem join_surj {k : ℕ} (hk : 2 ≤ k) (x : Fin (3*k)) :
    Function.Surjective (@join k hk x) := by
  intro σ
  have all : σ.val.support = univ := by
    apply eq_univ_of_card
    rw [← Equiv.Perm.sum_cycleType, σ.property, Fintype.card_fin]
    simp
    omega
  have hx : x ∈ σ.val.support := by rw [all]; exact mem_univ _
  obtain ⟨c,tail,hct,hdisj,hc,hcx,hck,htail⟩ := splitAt hx
    (show σ.val.cycleType = {k} + {k,k} from σ.property)
    (by intro a ha; simpa [σ.property] using ha)
  let a : FirstSupport k x := ⟨c.support, by simp [anchoredSupports, hck, hcx]⟩
  have tail_support : tail.support = a.valᶜ := by
    rw [support_sdiff hdisj, ← hct, all]
    simp [a, compl_eq_univ_sdiff]
  have hy : secondAnchor hk a ∈ tail.support := tail_support.symm ▸ secondAnchor_mem hk a
  obtain ⟨d,e,hde,hdisj',hd,hdy,hdk,he⟩ := splitAt hy
    (show tail.cycleType = {k} + {k} from htail)
    (by intro i hi; simpa [htail] using hi)
  have hdc : d.support ⊆ a.valᶜ := by
    rw [← tail_support, hde, hdisj'.support_mul]
    exact subset_union_left
  let b : SecondSupport hk a := ⟨d.support, by
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hdc,hdk⟩, singleton_subset_iff.mpr hdy⟩⟩
  have heCycle : e.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by simp [he])
  have heSupport : e.support = a.valᶜ \ b.val := by
    rw [support_sdiff hdisj', ← hde, tail_support]
  refine ⟨⟨a,b,⟨c,hc,rfl⟩,⟨d,hd,rfl⟩,⟨e,heCycle,heSupport⟩⟩, Subtype.ext ?_⟩
  exact (hct.trans (congrArg (fun t ↦ c*t) hde)).symm

private theorem supported_weight {k : ℕ} {x : Fin (3*k)} {hk : 2 ≤ k} (a : FirstSupport k x)
    (b : SecondSupport hk a) :
    (∑ u : CyclesOn a.val × CyclesOn b.val × CyclesOn (a.valᶜ \ b.val),
      (X : ℝ[X]) ^ excedances (u.1.val*(u.2.1.val*u.2.2.val))) =
      (X*eulerian (k-1))^3 := by
  let wt (u : Equiv.Perm (Fin (3*k))) := (X : ℝ[X]) ^ excedances u
  have add_first (u : CyclesOn a.val) (v : CyclesOn b.val)
      (w : CyclesOn (a.valᶜ \ b.val)) :
      wt (u.val*(v.val*w.val)) = wt u.val * wt (v.val*w.val) := by
    simp only [wt, excedances_disjoint_mul (disj_first_tail u v w), pow_add]
  have add_tail (v : CyclesOn b.val) (w : CyclesOn (a.valᶜ \ b.val)) :
      wt (v.val*w.val) = wt v.val * wt w.val := by
    simp only [wt, excedances_disjoint_mul (disj_second_third v w), pow_add]
  change (∑ u : CyclesOn a.val × CyclesOn b.val × CyclesOn (a.valᶜ \ b.val),
    wt (u.1.val*(u.2.1.val*u.2.2.val))) = _
  rw [Fintype.sum_prod_type]
  simp_rw [add_first, ← mul_sum]
  rw [← sum_mul, singleCycleWeight (m := k-1) a.val (by have := (anchor_props a).2.1; omega)
    (by omega), Fintype.sum_prod_type]
  simp_rw [add_tail, ← mul_sum]
  rw [← sum_mul, singleCycleWeight (m := k-1) b.val (by have := (anchor_props b).2.1; omega)
    (by omega), singleCycleWeight (m := k-1) (a.valᶜ \ b.val)
    (by have := third_card a b; omega) (by omega)]
  ring

/-- The two anchored choices count each unordered partition of the support into
three equal blocks once. Each block carries its own genuine cycle. -/
theorem tripleCycleWeight_choose {k : ℕ} (hk : 2 ≤ k) :
    (∑ σ : Triples k, (X : ℝ[X])^excedances σ.val) =
      C (((3*k-1).choose (k-1) * (2*k-1).choose (k-1) : ℕ):ℝ) *
        (X*eulerian (k-1))^3 := by
  let x : Fin (3*k) := ⟨0, by omega⟩
  let e : Choices hk x ≃ Triples k := Equiv.ofBijective join ⟨join_inj, join_surj hk x⟩
  rw [← e.sum_comp (fun σ : Triples k ↦ (X : ℝ[X])^excedances σ.val)]
  change (∑ u : Choices hk x, (X : ℝ[X])^excedances
    (u.2.2.1.val*(u.2.2.2.1.val*u.2.2.2.2.val))) = _
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma, supported_weight]
  have card_second (a : FirstSupport k x) :
      Fintype.card (SecondSupport hk a) = (2*k-1).choose (k-1) := by
    rw [Fintype.card_coe, card_anchor (secondAnchor_mem hk a) (by omega), first_compl_card]
  have card_first : Fintype.card (FirstSupport k x) = (3*k-1).choose (k-1) := by
    rw [Fintype.card_coe, card_anchor (mem_univ x) (by omega), card_univ, Fintype.card_fin]
  simp only [sum_const, card_univ, card_second, card_first, nsmul_eq_mul, Nat.cast_mul,
    map_mul, map_natCast]
  ring

private theorem factorial_step (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) = (n:ℝ)*((n-1).factorial:ℝ) := by
  exact_mod_cast (show n.factorial = n*(n-1).factorial by
    nth_rw 1 [show n=n-1+1 by omega, Nat.factorial_succ]
    rw [Nat.sub_add_cancel hn])

private theorem factorial_anchor {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n-1).choose (k-1) : ℝ)*((k-1).factorial:ℝ)*((n-k).factorial:ℝ) =
      ((n-1).factorial:ℝ) := by
  exact_mod_cast (show (n-1).choose (k-1) * (k-1).factorial * (n-k).factorial =
    (n-1).factorial by
      simpa only [show n-1-(k-1)=n-k by omega] using
        Nat.choose_mul_factorial_mul_factorial (show k-1 ≤ n-1 by omega))

/-- The ordinary factorial form of the number of three-block supports. -/
theorem tripleSupport_count {k : ℕ} (hk : 1 ≤ k) :
    (((3*k-1).choose (k-1) * (2*k-1).choose (k-1) : ℕ):ℝ) =
      ((3*k).factorial:ℝ) / (6*(k.factorial:ℝ)^3) := by
  let a : ℝ := (3*k-1).choose (k-1)
  let b : ℝ := (2*k-1).choose (k-1)
  let f (n : ℕ) : ℝ := n.factorial
  have h₃ : a*f (k-1)*f (2*k)=f (3*k-1) := by
    simpa only [a, f, show 3*k-k=2*k by omega] using factorial_anchor hk (show k ≤ 3*k by omega)
  have h₂ : b*f (k-1)*f k=f (2*k-1) := by
    simpa only [b, f, show 2*k-k=k by omega] using factorial_anchor hk (show k ≤ 2*k by omega)
  have s₂ : f (2*k)=((2*k : ℕ):ℝ)*f (2*k-1) := factorial_step _ (by omega)
  have s₃ : f (3*k)=((3*k : ℕ):ℝ)*f (3*k-1) := factorial_step _ (by omega)
  have sk : f k=(k:ℝ)*f (k-1) := factorial_step _ hk
  push_cast only [Nat.cast_mul, Nat.cast_ofNat]
  change a*b = f (3*k)/(6*f k^3)
  apply (eq_div_iff (by dsimp only [f]; positivity)).2
  calc
    a*b*(6*f k^3) = ((3*k:ℕ):ℝ)*(a*f (k-1)*(((2*k:ℕ):ℝ)*(b*f (k-1)*f k))) := by
      rw [sk]
      push_cast
      ring
    _ = _ := by rw [h₂, ← s₂, h₃, ← s₃]

/-- The three-cycle contribution at the threshold, with the automorphism factor 3!. -/
def tripleContribution (k : ℕ) : ℝ[X] :=
  C (((3*k).factorial:ℝ) / (6*(k.factorial:ℝ)^3)) * (X*eulerian (k-1))^3

theorem tripleCycleWeight {k : ℕ} (hk : 2 ≤ k) :
    (∑ σ : {σ : Equiv.Perm (Fin (3*k)) // σ.cycleType = {k,k,k}},
      (X : ℝ[X])^excedances σ.val) = tripleContribution k := by
  change (∑ σ : Triples k, (X : ℝ[X])^excedances σ.val) = _
  rw [tripleCycleWeight_choose hk, tripleSupport_count (by omega), tripleContribution]

/-- At the threshold, three cycles for the original admissibility condition
have exactly the lengths k, k, k. -/
theorem allowed_three_iff_tripleType {k : ℕ} (hk : 2 ≤ k) (σ : Equiv.Perm (Fin (3*k))) :
    (Allowed k σ ∧ σ.cycleType.card = 3) ↔ σ.cycleType = {k,k,k} := by
  constructor
  · rintro ⟨ha, hc⟩
    have hsum : σ.cycleType.sum = 3*k := by
      rw [Equiv.Perm.sum_cycleType, support_univ_of_allowed ha hk, card_univ, Fintype.card_fin]
    obtain ⟨a,b,c,hl⟩ := List.length_eq_three.mp
      (show σ.cycleType.toList.length = 3 by simpa using hc)
    have hs : a+b+c = 3*k := by
      have h := Multiset.sum_toList σ.cycleType
      rw [hl, hsum] at h
      simpa [add_comm, add_left_comm, add_assoc] using h
    have lower (m : ℕ) (hm : m ∈ [a,b,c]) : k ≤ m := by
      apply le_of_mem_cycleType ha
      rwa [← Multiset.mem_toList, hl]
    have h₁ := lower a (by simp)
    have h₂ := lower b (by simp)
    have h₃ := lower c (by simp)
    have e₁ : a = k := by omega
    have e₂ : b = k := by omega
    have e₃ : c = k := by omega
    subst a b c
    calc
      σ.cycleType = (σ.cycleType.toList : Multiset ℕ) := by simp
      _ = ([k,k,k] : List ℕ) := congrArg (fun l : List ℕ ↦ (l : Multiset ℕ)) hl
      _ = _ := rfl
  · intro ht
    refine ⟨allowed_of_cycleType_lower ?_ ?_, by simp [ht]⟩
    · apply eq_univ_of_card
      rw [← Equiv.Perm.sum_cycleType, ht, Fintype.card_fin]
      simp
      omega
    · intro m hm
      simp [ht] at hm
      omega

/-- The contribution of precisely three cycles in the original enumerator. -/
theorem tripleThreshold_weight {k : ℕ} (hk : 2 ≤ k) :
    (∑ σ : Equiv.Perm (Fin (3*k)), if Allowed k σ ∧ σ.cycleType.card = 3
      then (X : ℝ[X])^excedances σ else 0) = tripleContribution k := by
  simp_rw [allowed_three_iff_tripleType hk]
  rw [← sum_filter, ← tripleCycleWeight hk]
  apply sum_subtype
  simp

/-- Normalize the true three-cycle contribution by the same scale as the one-cycle row. -/
theorem scaled_tripleCycleWeight {k : ℕ} (hk : 2 ≤ k) (r t : ℝ) (ht : t ≠ 1) :
    r^(3*k) * ((tripleContribution k).eval t / (1-t)^(3*k)) / (2*((3*k-1).factorial:ℝ)) =
      2/(k:ℝ)^2 * (scaledMoment r t k)^3 := by
  have hk₀ : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have ht₀ : (1:ℝ)-t ≠ 0 := sub_ne_zero.mpr ht.symm
  have hfk : ((k-1).factorial:ℝ) ≠ 0 := by positivity
  have hfn : ((3*k-1).factorial:ℝ) ≠ 0 := by positivity
  simp only [tripleContribution, eval_mul, eval_C, eval_pow, eval_X, scaledMoment, moment]
  rw [factorial_step (3*k) (by omega), factorial_step k (by omega),
    Nat.mul_comm 3 k, pow_mul r, pow_mul (1-t)]
  push_cast
  field_simp
  ring

#print axioms tripleCycleWeight_choose
#print axioms tripleSupport_count
#print axioms tripleCycleWeight
#print axioms allowed_three_iff_tripleType
#print axioms tripleThreshold_weight
#print axioms scaled_tripleCycleWeight

end LongCycleBounds.Band
