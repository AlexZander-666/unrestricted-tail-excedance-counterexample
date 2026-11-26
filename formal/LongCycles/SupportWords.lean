import LongCycles.AnchoredCycles
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin

noncomputable section
namespace LongCycles

/-- Each specified letter occurs exactly once. -/
abbrev Orderings {α : Type*} [DecidableEq α] (s : Finset α) :=
  {l : List α // l.Nodup ∧ l.toFinset = s}

/-- Remove the distinguished initial letter from a cycle word. -/
def deleteFirstEquiv {α : Type*} [DecidableEq α] (s : Finset α) (x : α) (hx : x ∈ s) :
    AnchoredWords s x ≃ Orderings (s.erase x) := by
  classical
  refine {
    toFun := fun w => ⟨w.val.tail, ?_, ?_⟩
    invFun := fun t => ⟨x :: t.val, ?_, ?_, rfl⟩
    left_inv := ?_
    right_inv := fun _ => Subtype.ext rfl }
  · exact w.property.1.tail
  · obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp w.property.2.2
    have hn := w.property.1
    have hw := w.property.2.1
    rw [ht] at hn hw ⊢
    simp only [List.nodup_cons] at hn
    simp only [List.toFinset_cons] at hw
    rw [← hw, Finset.erase_insert (by simpa using hn.1)]
    rfl
  · apply List.nodup_cons.mpr
    refine ⟨?_, t.property.1⟩
    intro h
    have h' : x ∈ t.val.toFinset := List.mem_toFinset.mpr h
    rw [t.property.2] at h'
    exact Finset.notMem_erase x s h'
  · simp [t.property.2, hx]
  · intro w
    apply Subtype.ext
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp w.property.2.2
    change x :: w.val.tail = w.val
    simp [ht]

/-- Read a rank permutation as letters in the increasing order of the support. -/
def orderedWord {α : Type*} [LinearOrder α] {m : ℕ} (s : Finset α) (h : s.card = m)
    (π : Equiv.Perm (Fin m)) : Orderings s := by
  classical
  let e := s.orderIsoOfFin h
  refine ⟨List.ofFn (fun i => (e (π i) : α)), List.nodup_ofFn.mpr ?_, ?_⟩
  · exact Subtype.coe_injective.comp (e.injective.comp π.injective)
  · ext x
    rw [List.mem_toFinset, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e (π i)).property
    · intro hx
      refine ⟨π.symm (e.symm ⟨x, hx⟩), ?_⟩
      simp

/-- Every ordering is uniquely determined by the permutation of its ranks. -/
def permOrderingEquiv {α : Type*} [LinearOrder α] {m : ℕ}
    (s : Finset α) (h : s.card = m) : Equiv.Perm (Fin m) ≃ Orderings s := by
  classical
  apply Equiv.ofBijective (orderedWord s h)
  constructor
  · intro a b hab
    have hf := List.ofFn_injective (congrArg Subtype.val hab)
    apply Equiv.ext
    intro i
    apply (s.orderIsoOfFin h).injective
    exact Subtype.ext (congrFun hf i)
  · intro w
    have hlen : w.val.length = m := by
      exact (List.toFinset_card_of_nodup w.property.1).symm.trans ((congrArg Finset.card w.property.2).trans h)
    let letter (i : Fin m) : s := ⟨w.val.get (i.cast hlen.symm), by
      have hmem := List.mem_toFinset.mpr (w.val.get_mem (i.cast hlen.symm))
      simpa only [w.property.2] using hmem⟩
    let f (i : Fin m) : Fin m := (s.orderIsoOfFin h).symm (letter i)
    have hf : Function.Injective f := by
      intro i j hij
      have hletter := (s.orderIsoOfFin h).symm.injective hij
      have hget := w.property.1.injective_get (congrArg Subtype.val hletter)
      exact Fin.ext (congrArg (fun t : Fin w.val.length => t.val) hget)
    refine ⟨Equiv.ofBijective f hf.bijective_of_finite, Subtype.ext ?_⟩
    apply List.ext_getElem
    · simpa [orderedWord] using hlen.symm
    · intro i hi hi'
      simp [orderedWord, f, letter]

end LongCycles
