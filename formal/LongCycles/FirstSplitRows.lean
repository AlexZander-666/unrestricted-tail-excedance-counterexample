import LongCycles.PermCycleBridge
import LongCycles.SingleCycleWeight

noncomputable section
namespace LongCycles

open Polynomial
open scoped BigOperators

/-- A singleton cycle type of length n is exactly a cycle on all n labels. -/
theorem singleton_iff_fullCycle {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.cycleType = {n} ↔ σ.IsCycle ∧ σ.support = Finset.univ := by
  constructor
  · intro h
    refine ⟨Equiv.Perm.card_cycleType_eq_one.mp (by simp [h]), ?_⟩
    apply Finset.eq_univ_of_card
    rw [← Equiv.Perm.sum_cycleType, h]
    simp
  · rintro ⟨hc, hs⟩
    rw [hc.cycleType, hs]
    simp

private theorem sum_conditional {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p] [Fintype (Subtype p)] (f : ι → M) :
    (∑ i, if p i then f i else 0) = ∑ i : Subtype p, f i.val := by
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  simp

private theorem full_sum {n : ℕ} (hn : 2 ≤ n) :
    (∑ σ : Equiv.Perm (Fin n), if σ.cycleType = {n} then (X : Polynomial ℝ)^excedances σ else 0)
      = X * eulerian (n-1) := by
  classical
  let t := (Finset.univ : Finset (Fin n))
  have hs : t.card = (n-1)+1 := by simp [t]; omega
  have hw := singleCycleWeight t hs (by omega : 0 < n-1)
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
      if σ.IsCycle ∧ σ.support = t then (X : Polynomial ℝ)^excedances σ else 0 := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [singleton_iff_fullCycle, t]
    _ = ∑ σ : CyclesOn t, (X : Polynomial ℝ)^excedances σ.val :=
      sum_conditional _ _
    _ = _ := hw

/-- At 2k-1 letters the second cycle type has too many moved points. -/
theorem firstRow_fromPermutations {k : ℕ} (hk : 2 ≤ k) :
    enumerator (2*k-1) k = X * eulerian (2*k-2) := by
  classical
  let n := 2*k-1
  have hneq : n ≠ 2*k := by dsimp [n]; omega
  have he : ∀ σ : Equiv.Perm (Fin n), Allowed k σ ↔ σ.cycleType = {n} := by
    intro σ
    rw [allowed_iff_first_split_types hk (Or.inl rfl)]
    exact or_iff_left (fun h => hneq h.2)
  have hw := full_sum (show 2 ≤ n by dsimp [n]; omega)
  rw [show 2*k-2 = n-1 by dsimp [n]; omega]
  unfold enumerator
  change (∑ σ : Equiv.Perm (Fin n), if Allowed k σ then X^excedances σ else 0) = _
  simpa only [he] using hw

/-- At 2k letters split the defining sum into exactly the two
nonoverlapping cycle types. -/
theorem secondRow_fromPermutations {k : ℕ} (hk : 2 ≤ k) :
    enumerator (2*k) k = X * eulerian (2*k-1) +
      ∑ σ : {σ : Equiv.Perm (Fin (2*k)) // σ.cycleType = {k,k}},
        (X : Polynomial ℝ)^excedances σ.val := by
  classical
  let n := 2*k
  let wt (σ : Equiv.Perm (Fin n)) := (X : Polynomial ℝ)^excedances σ
  have he : ∀ σ : Equiv.Perm (Fin n), Allowed k σ ↔ σ.cycleType = {n} ∨ σ.cycleType = {k,k} := by
    intro σ
    simpa [n] using (allowed_iff_first_split_types (σ := σ) hk (Or.inr rfl))
  have hne : ({n} : Multiset ℕ) ≠ {k,k} := by
    intro h
    have := congrArg Multiset.card h
    simp at this
  calc
    enumerator n k = ∑ σ, ((if σ.cycleType = {n} then wt σ else 0) +
      (if σ.cycleType = {k,k} then wt σ else 0)) := by
        unfold enumerator
        apply Finset.sum_congr rfl
        intro σ _
        by_cases ha : σ.cycleType = {n}
        · have hb : σ.cycleType ≠ {k,k} := fun h => hne (ha.symm.trans h)
          simp [he, ha, wt]
        · simp [he, ha, wt]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) (full_sum (show 2 ≤ n by dsimp [n]; omega))
        (sum_conditional _ wt)

end LongCycles
