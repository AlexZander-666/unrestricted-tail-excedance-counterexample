import LongCycles.FirstSplit

/-! Two complementary cycles of unequal lengths, counted from the permutation itself. -/

noncomputable section
namespace LongCycleBounds.Band
open Polynomial LongCycles
open scoped Classical

private abbrev Supports (n a : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard a)
private abbrev Choices (n a : ℕ) := (s : Supports n a) × (CyclesOn s.val × CyclesOn s.valᶜ)
private abbrev Doubles (n a b : ℕ) := {σ : Equiv.Perm (Fin n) // σ.cycleType = {a,b}}

private theorem support_card {n a} (s : Supports n a) : s.val.card = a :=
  (Finset.mem_powersetCard.mp s.property).2

private theorem complement_card {n a b} (hn : a+b=n) (s : Supports n a) : s.valᶜ.card = b := by
  rw [Finset.card_compl, Fintype.card_fin, support_card s]
  omega

private theorem apart {n} {s : Finset (Fin n)} (c : CyclesOn s) (d : CyclesOn sᶜ) :
    c.val.Disjoint d.val := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, c.property.2, d.property.2]
  exact disjoint_compl_right

private def join {n a b} (hn : a+b=n) (u : Choices n a) : Doubles n a b :=
  ⟨u.2.1.val * u.2.2.val, by
    rw [(apart u.2.1 u.2.2).cycleType_mul, u.2.1.property.1.cycleType,
      u.2.2.property.1.cycleType, u.2.1.property.2, u.2.2.property.2,
      support_card u.1, complement_card hn u.1]
    rfl⟩

private theorem factors {n a} {s : Supports n a} (c : CyclesOn s.val) (d : CyclesOn s.valᶜ) :
    (c.val*d.val).cycleFactorsFinset = {c.val,d.val} := by
  rw [(apart c d).cycleFactorsFinset_mul_eq_union, c.property.1.cycleFactorsFinset_eq_singleton,
    d.property.1.cycleFactorsFinset_eq_singleton, Finset.singleton_union]

private theorem join_inj {n a b} (hn : a+b=n) (hab : a≠b) : Function.Injective (join hn) := by
  rintro ⟨s,c,d⟩ ⟨t,e,f⟩ h
  have he := congrArg Subtype.val h
  change c.val*d.val = e.val*f.val at he
  have hcert : c.val ∈ (c.val*d.val).cycleFactorsFinset := by rw [factors]; simp
  rw [he,factors,Finset.mem_insert,Finset.mem_singleton] at hcert
  have hcycle : c.val = e.val := hcert.resolve_right (fun hcf ↦ hab (by
    calc
      a = c.val.support.card := by rw [c.property.2, support_card]
      _ = f.val.support.card := congrArg (fun π : Equiv.Perm (Fin n) ↦ π.support.card) hcf
      _ = b := by rw [f.property.2, complement_card hn t]))
  have hst : s=t := Subtype.ext (c.property.2.symm.trans
    ((congrArg Equiv.Perm.support hcycle).trans e.property.2))
  subst t
  have hce : c=e := Subtype.ext hcycle
  subst e
  have hdf : d=f := Subtype.ext (mul_left_cancel he)
  subst f
  rfl

private theorem join_surj {n a b} (hn : a+b=n) : Function.Surjective (join hn) := by
  intro σ
  have hm : a ∈ σ.val.cycleType := by simp [σ.property]
  obtain ⟨c,d,he,hd,hc,hca⟩ := Equiv.Perm.mem_cycleType_iff.mp hm
  have hh : c.cycleType + d.cycleType = {a,b} := by
    rw [← hd.cycleType_mul, ← he, σ.property]
  rw [hc.cycleType, hca] at hh
  have ht : d.cycleType = {b} := add_left_cancel (a := ({a} : Multiset ℕ)) hh
  have hdc := Equiv.Perm.card_cycleType_eq_one.mp (show d.cycleType.card = 1 by simp [ht])
  have hdb : d.support.card = b := by simpa [hdc.cycleType] using ht
  have hall : c.support ∪ d.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hd.support_mul, hd.card_support_mul, hca, hdb, Fintype.card_fin, hn]
  have hcompl : d.support = c.supportᶜ := by
    ext x
    rw [Finset.mem_compl]
    constructor
    · exact fun h₂ h₁ ↦ Finset.disjoint_left.mp hd.disjoint_support h₁ h₂
    · intro hx
      have h : x ∈ c.support ∪ d.support := hall.symm ▸ Finset.mem_univ x
      exact (Finset.mem_union.mp h).resolve_left hx
  let s : Supports n a := ⟨c.support, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hca⟩⟩
  exact ⟨⟨s,⟨c,hc,rfl⟩,⟨d,hdc,hcompl⟩⟩, Subtype.ext he.symm⟩

/-- Unequal lengths canonically distinguish the first support. In contrast to equal lengths,
there is a full binomial coefficient for this unordered cycle type. -/
theorem unequal_two_cycle_weight {n a b : ℕ} (hn : a+b=n) (ha : 2≤a) (hb : 2≤b) (hab : a≠b) :
    (∑ σ : {σ : Equiv.Perm (Fin n) // σ.cycleType = {a,b}}, (X : ℝ[X])^excedances σ.val) =
    C (n.choose a : ℝ) * ((X*eulerian (a-1))*(X*eulerian (b-1))) := by
  let e : Choices n a ≃ Doubles n a b :=
    Equiv.ofBijective (join hn) ⟨join_inj hn hab,join_surj hn⟩
  rw [← e.sum_comp (fun σ : Doubles n a b ↦ (X : ℝ[X])^excedances σ.val)]
  change (∑ u : Choices n a, (X : ℝ[X])^excedances (u.2.1.val*u.2.2.val)) = _
  rw [Fintype.sum_sigma]
  have term (s : Supports n a) :
      (∑ u : CyclesOn s.val × CyclesOn s.valᶜ, (X : ℝ[X])^excedances (u.1.val*u.2.val)) =
      (X*eulerian (a-1))*(X*eulerian (b-1)) := by
    rw [Fintype.sum_prod_type]
    simp_rw [excedances_disjoint_mul (apart _ _), pow_add, ← Finset.mul_sum]
    rw [← Finset.sum_mul, singleCycleWeight (m := a-1) s.val (by have := support_card s; omega)
      (by omega), singleCycleWeight (m := b-1) s.valᶜ (by have := complement_card hn s; omega)
      (by omega)]
  simp_rw [term]
  simp [Supports, Finset.card_powersetCard, nsmul_eq_mul]

#print axioms unequal_two_cycle_weight
end LongCycleBounds.Band
