import LongCycleBounds.EulerianSturm
import LongCycleFinite.Assembly

namespace LongCycleBounds
open Polynomial LongCycles LongCycleFinite
noncomputable section

/-- Interlacing in the original permutation formulation at the first split. -/
theorem large_firstSplit_original (k : ℕ) (hk : 201 ≤ k) :
    WeakRealInterlacing (enumerator (2*k-1) k) (enumerator (2*k) k) := by
  obtain ⟨hp,hq⟩ := firstSplit_quotients k (by omega)
  rw [hp,hq]
  exact weak_mul_X_of_strict (large_firstSplit_strict k hk)

private theorem singleton_below_split {n k : ℕ} (hk : 2 ≤ k) (lo : k ≤ n) (hi : n < 2*k)
    (σ : Equiv.Perm (Fin n)) : Allowed k σ ↔ σ.cycleType = {n} := by
  classical
  constructor
  · intro h
    have total : σ.cycleType.toList.sum = n := by
      simp [Equiv.Perm.sum_cycleType, support_univ_of_allowed h hk]
    have lower : ∀ j ∈ σ.cycleType.toList, k ≤ j := fun j hj ↦ le_of_mem_cycleType h (by simpa using hj)
    have single : σ.cycleType.toList = [n] := by
      generalize σ.cycleType.toList = l at total lower ⊢
      cases l with
      | nil => simp at total; omega
      | cons a l =>
        cases l with
        | nil => simpa using total
        | cons b l =>
          have ha := lower a (by simp)
          have hb := lower b (by simp)
          simp at total
          omega
    simpa using congrArg (fun l : List ℕ ↦ (l : Multiset ℕ)) single
  · intro h
    apply allowed_of_cycleType_lower ((singleton_iff_fullCycle σ).mp h).2
    simpa [h] using lo

/-- Before two cycles fit, the original enumerator is precisely the single-cycle row. -/
theorem beforeSplitRow {n k : ℕ} (hk : 2 ≤ k) (lo : k ≤ n) (hi : n < 2*k) :
    enumerator n k = X * eulerian (n-1) := by
  classical
  let t := (Finset.univ : Finset (Fin n))
  have hs : t.card = (n-1)+1 := by simp [t]; omega
  have cond (σ : Equiv.Perm (Fin n)) :
      Allowed k σ ↔ σ.IsCycle ∧ σ.support=t :=
    (singleton_below_split hk lo hi σ).trans (singleton_iff_fullCycle σ)
  unfold enumerator
  simp_rw [cond,← Finset.sum_filter]
  calc
    _ = ∑ σ : CyclesOn t, (X : Polynomial ℝ)^excedances σ.val := by
      apply Finset.sum_subtype
      simp
    _ = _ := singleCycleWeight t hs (by omega)

/-- Both lengths lie below the first possible split. -/
theorem beforeSplitInterlacing {n k : ℕ} (hk : 3 ≤ k) (lo : k ≤ n) (hi : n+1 < 2*k) :
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  rw [beforeSplitRow (by omega : 2 ≤ k) lo (by omega),
      beforeSplitRow (by omega : 2 ≤ k) (by omega : k ≤ n+1) hi]
  apply weak_mul_X_of_strict (d := n-2)
  have h := eulerian_consecutive_strict (n-2)
  simpa only [show n-2+1=n-1 by omega,show n-1+1=n+1-1 by omega] using h

/-- For every k ≥ 201 the original consecutive-row conjecture holds up to and
including the first row pair for which two disjoint cycles can occur. -/
theorem throughFirstSplit {n k : ℕ} (hk : 201 ≤ k) (lo : k ≤ n) (hi : n < 2*k) :
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  by_cases h : n+1<2*k
  · exact beforeSplitInterlacing (by omega) lo h
  · have e : n=2*k-1 := by omega
    have e' : n+1=2*k := by omega
    rw [e',e]
    exact large_firstSplit_original k hk

#print axioms large_firstSplit_original
#print axioms beforeSplitRow
#print axioms beforeSplitInterlacing
#print axioms throughFirstSplit
end
end LongCycleBounds
