import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic

noncomputable section
namespace LongCycles

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Genuine cycles with exactly the prescribed support. -/
abbrev CyclesOn (s : Finset α) := {p : Equiv.Perm α // p.IsCycle ∧ p.support = s}

/-- An ordering of exactly the support letters, rooted at a prescribed label. -/
abbrev AnchoredWords (s : Finset α) (x : α) :=
  {l : List α // l.Nodup ∧ l.toFinset = s ∧ l.head? = some x}

omit [Fintype α] in
private theorem anchoredLength {s : Finset α} {x : α} (w : AnchoredWords s x) :
    w.val.length = s.card := by
  exact (List.toFinset_card_of_nodup w.property.1).symm.trans (congrArg Finset.card w.property.2.1)

/-- Writing a cycle starting with x gives a bijection. In the application
x is the least support label; the bijection itself needs no linear order. -/
def cycleWordEquiv (s : Finset α) (x : α) (hx : x ∈ s) (hs : 2 ≤ s.card) :
    CyclesOn s ≃ AnchoredWords s x := by
  classical
  refine {
    toFun := fun c => ⟨c.val.toList x, Equiv.Perm.nodup_toList _ _, ?_, ?_⟩
    invFun := fun w => ⟨w.val.formPerm, List.isCycle_formPerm w.property.1 ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have hx' : x ∈ c.val.support := c.property.2.symm ▸ hx
    calc
      (c.val.toList x).toFinset = (c.val.cycleOf x).support := by
        ext y
        simp only [List.mem_toFinset, Equiv.Perm.mem_toList_iff, Equiv.Perm.mem_support_cycleOf_iff]
      _ = s := by rw [c.property.1.cycleOf_eq (Equiv.Perm.mem_support.mp hx'), c.property.2]
  · have hx' : x ∈ c.val.support := c.property.2.symm ▸ hx
    have hlen := Equiv.Perm.length_toList_pos_of_mem_support c.val x hx'
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen,
      Equiv.Perm.toList_getElem_zero c.val x hx']
  · rwa [anchoredLength]
  · rw [List.support_formPerm_of_nodup _ w.property.1]
    · exact w.property.2.1
    · intro y he
      have hlen := anchoredLength w
      rw [he] at hlen
      simp at hlen
      omega
  · intro c
    apply Subtype.ext
    change (c.val.toList x).formPerm = c.val
    rw [Equiv.Perm.formPerm_toList]
    exact c.property.1.cycleOf_eq (Equiv.Perm.mem_support.mp (c.property.2.symm ▸ hx))
  · intro w
    apply Subtype.ext
    change w.val.formPerm.toList x = w.val
    have hlen : 2 ≤ w.val.length := by rwa [anchoredLength]
    have hback := Equiv.Perm.toList_formPerm_nontrivial w.val hlen w.property.1
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp w.property.2.2
    simpa [ht] using hback

end LongCycles
