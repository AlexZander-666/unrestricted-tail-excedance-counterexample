import LongCycles.PermCycleBridge
import LongCycles.SingleCycleWeight

noncomputable section
namespace LongCycles
open Polynomial
open scoped Classical

private def halves (k : ℕ) (x : Fin (2*k)) :=
  (Finset.univ.powersetCard k).filter fun s : Finset (Fin (2*k)) => ({x} : Finset _) ⊆ s

private abbrev Choices (k : ℕ) (x : Fin (2*k)) :=
  (s : ↥(halves k x)) × (CyclesOn s.val × CyclesOn s.valᶜ)

private abbrev Doubles (k : ℕ) :=
  {σ : Equiv.Perm (Fin (2*k)) // σ.cycleType = {k,k}}

private theorem half_props {k} {x : Fin (2*k)} (s : ↥(halves k x)) :
    s.val.card = k ∧ x ∈ s.val := by
  simpa [halves] using s.property

private theorem half_compl {k} {x : Fin (2*k)} (s : ↥(halves k x)) : s.valᶜ.card = k := by
  rw [Finset.card_compl, Fintype.card_fin, (half_props s).1]
  omega

private theorem apart {n} {s : Finset (Fin n)} (c : CyclesOn s) (d : CyclesOn sᶜ) :
    c.val.Disjoint d.val := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, c.property.2, d.property.2]
  exact disjoint_compl_right

private def join {k} {x : Fin (2*k)} (u : Choices k x) : Doubles k :=
  ⟨u.2.1.val * u.2.2.val, by
    rw [(apart u.2.1 u.2.2).cycleType_mul, u.2.1.property.1.cycleType,
      u.2.2.property.1.cycleType, u.2.1.property.2, u.2.2.property.2,
      (half_props u.1).1, half_compl u.1]
    rfl⟩

private theorem recover_left {k} {x : Fin (2*k)} (u : Choices k x) :
    (join u).val.cycleOf x = u.2.1.val := by
  have h₁ : x ∈ u.2.1.val.support := u.2.1.property.2.symm ▸ (half_props u.1).2
  have h₂ : x ∉ u.2.2.val.support := by simp [u.2.2.property.2, (half_props u.1).2]
  exact (Equiv.Perm.cycleOf_mul_of_apply_right_eq_self (apart u.2.1 u.2.2).commute x
    (Equiv.Perm.notMem_support.mp h₂)).trans
    (u.2.1.property.1.cycleOf_eq (Equiv.Perm.mem_support.mp h₁))

private theorem join_inj {k} {x : Fin (2*k)} : Function.Injective (@join k x) := by
  rintro ⟨s, c, d⟩ ⟨t, e, f⟩ h
  have hcycle := congrArg (fun p : Doubles k => p.val.cycleOf x) h
  rw [recover_left, recover_left] at hcycle
  have hsup : s = t := Subtype.ext (c.property.2.symm.trans
    ((congrArg Equiv.Perm.support hcycle).trans e.property.2))
  subst t
  have hc : c = e := Subtype.ext hcycle
  subst e
  have hprod := congrArg Subtype.val h
  change c.val * d.val = c.val * f.val at hprod
  have hd : d = f := Subtype.ext (mul_left_cancel hprod)
  subst f
  rfl

private theorem in_image {k} {x : Fin (2*k)} (c d : Equiv.Perm (Fin (2*k)))
    (hc : c.IsCycle) (hd : d.IsCycle) (hs : c.support.card = k)
    (ht : d.support = c.supportᶜ) (hx : x ∈ c.support) :
    ∃ u : Choices k x, (join u).val = c*d := by
  let s : ↥(halves k x) := ⟨c.support, by simp [halves, hs, hx]⟩
  exact ⟨⟨s, ⟨c,hc,rfl⟩, ⟨d,hd,ht⟩⟩, rfl⟩

private theorem join_surj {k} (x : Fin (2*k)) : Function.Surjective (@join k x) := by
  intro σ
  have hm : k ∈ σ.val.cycleType := by simp [σ.property]
  obtain ⟨c,d,he,hd,hc,hk⟩ := Equiv.Perm.mem_cycleType_iff.mp hm
  have hh : c.cycleType + d.cycleType = {k,k} := by
    rw [← hd.cycleType_mul, ← he, σ.property]
  rw [hc.cycleType, hk] at hh
  have ht : d.cycleType = {k} := add_left_cancel (a := ({k} : Multiset ℕ)) hh
  have hdcy : d.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by simp [ht])
  have hdk : d.support.card = k := by simpa [hdcy.cycleType] using ht
  have all : c.support ∪ d.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hd.support_mul, hd.card_support_mul, hk, hdk, Fintype.card_fin]
    omega
  have hcompl : d.support = c.supportᶜ := by
    ext a
    rw [Finset.mem_compl]
    constructor
    · exact fun h₂ h₁ => Finset.disjoint_left.mp hd.disjoint_support h₁ h₂
    · intro ha
      have hall : a ∈ c.support ∪ d.support := all.symm ▸ Finset.mem_univ a
      exact (Finset.mem_union.mp hall).resolve_left ha
  by_cases hx : x ∈ c.support
  · obtain ⟨u,hu⟩ := in_image c d hc hdcy hk hcompl hx
    exact ⟨u, Subtype.ext (hu.trans he.symm)⟩
  · have hxc : x ∈ d.support := by simp [hcompl,hx]
    obtain ⟨u,hu⟩ := in_image d c hdcy hc hdk (by simp [hcompl]) hxc
    exact ⟨u, Subtype.ext (hu.trans (hd.commute.eq.symm.trans he.symm))⟩

/-- Two nontrivial k-cycles. Put the distinguished label into the first
support to account for the unordered pair of complementary supports once. -/
theorem twoCycleWeight {k : ℕ} (hk : 2 ≤ k) :
    (∑ σ : Doubles k, (X : Polynomial ℝ)^excedances σ.val) =
    C (((2*k).choose k / 2 : ℕ) : ℝ) * (X * eulerian (k-1))^2 := by
  let x : Fin (2*k) := ⟨0, by omega⟩
  let e : Choices k x ≃ Doubles k := Equiv.ofBijective join ⟨join_inj, join_surj x⟩
  rw [← e.sum_comp (fun σ : Doubles k => (X : Polynomial ℝ)^excedances σ.val)]
  change (∑ u : Choices k x, (X : Polynomial ℝ)^excedances (u.2.1.val*u.2.2.val)) = _
  rw [Fintype.sum_sigma]
  have term (s : ↥(halves k x)) :
      (∑ v : CyclesOn s.val × CyclesOn s.valᶜ,
        (X : Polynomial ℝ)^excedances (v.1.val*v.2.val)) = (X*eulerian (k-1))^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [excedances_disjoint_mul (apart _ _), pow_add, ← Finset.mul_sum]
    rw [← Finset.sum_mul, singleCycleWeight (m := k-1) s.val (by have := (half_props s).1; omega) (by omega),
      singleCycleWeight (m := k-1) s.valᶜ (by have := half_compl s; omega) (by omega), pow_two]
  simp_rw [term]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  rw [show (halves k x).card = (2*k).choose k / 2 from card_anchored_halves (by omega) x]
  simp

#print axioms twoCycleWeight

end LongCycles
