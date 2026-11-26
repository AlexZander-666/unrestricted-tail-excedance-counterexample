import LongCycleBounds.DescentRows
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

namespace LongCycleBounds
open Polynomial LongCycles
noncomputable section

private theorem descent_positions {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    descents σ = (Finset.univ.filter fun i : Fin n ↦ σ i.succ < σ i.castSucc).card := by
  classical
  unfold descents
  let emb : Fin n ↪ Fin (n+1) := ⟨Fin.castSucc, Fin.castSucc_injective _⟩
  have eq : (Finset.univ.filter fun x : Fin (n+1) ↦
      ∃ y : Fin (n+1), y.val = x.val+1 ∧ σ y < σ x) =
      (Finset.univ.filter fun i : Fin n ↦ σ i.succ < σ i.castSucc).map emb := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    constructor
    · rintro ⟨y, hy, hlt⟩
      have hv : x.val < n := by have := y.isLt; omega
      let i : Fin n := ⟨x.val,hv⟩
      have hi : i.succ = y := Fin.ext (by simpa [i] using hy.symm)
      exact ⟨i, hi ▸ hlt, rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨i.succ,rfl,hi⟩
  rw [eq, Finset.card_map]

theorem complement_descents {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    descents σ + descents (σ.trans Fin.revPerm) = n := by
  classical
  rw [descent_positions,descent_positions]
  have pred (i : Fin n) : (σ.trans Fin.revPerm) i.succ < (σ.trans Fin.revPerm) i.castSucc ↔
      ¬σ i.succ < σ i.castSucc := by
    change (σ i.succ).rev < (σ i.castSucc).rev ↔ _
    rw [Fin.rev_lt_rev, not_lt]
    exact lt_iff_le_and_ne.trans (and_iff_left (σ.injective.ne (ne_of_lt (Fin.castSucc_lt_succ : i.castSucc < i.succ))))
  simp_rw [pred]
  simpa using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun i : Fin n ↦ σ i.succ < σ i.castSucc)

/-- Reciprocity on the original sum over permutations follows by complementing each value. -/
theorem eulerian_reciprocity (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    t^n * (eulerian (n+1)).eval t⁻¹ = (eulerian (n+1)).eval t := by
  classical
  let e : Equiv.Perm (Equiv.Perm (Fin (n+1))) :=
    ⟨fun σ ↦ σ.trans Fin.revPerm, fun σ ↦ σ.trans Fin.revPerm,
     fun σ ↦ by apply Equiv.ext; intro i; exact Fin.rev_rev _, fun σ ↦ by apply Equiv.ext; intro i; exact Fin.rev_rev _⟩
  unfold eulerian
  simp only [eval_finsetSum,eval_pow,eval_X,Finset.mul_sum]
  trans ∑ σ : Equiv.Perm (Fin (n+1)), t^descents (e σ)
  swap
  · exact Equiv.sum_comp e (fun σ ↦ t^descents σ)
  apply Finset.sum_congr rfl
  intro σ _
  have h := complement_descents σ
  change t^n * (t⁻¹)^descents σ = t^descents (σ.trans Fin.revPerm)
  have hp := congrArg (fun j : ℕ ↦ t^j) h
  change t^(descents σ+descents (σ.trans Fin.revPerm)) = t^n at hp
  rw [pow_add] at hp
  rw [← hp, inv_pow]
  field_simp

#print axioms complement_descents
#print axioms eulerian_reciprocity
end
end LongCycleBounds
