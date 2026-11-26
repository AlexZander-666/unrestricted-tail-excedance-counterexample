import LongCycleBounds.BandCycles

/-! Enumeration by the smaller cycle length in the full two-cycle regime. -/
noncomputable section
namespace LongCycleBounds.Band
open Polynomial LongCycles Finset
open scoped Classical

def lengthPair (n a : ℕ) : Multiset ℕ := {a,n-a}

private theorem min_injective {n a b : ℕ} (ha : a≤n/2) (hb : b≤n/2)
    (he : lengthPair n a = lengthPair n b) : a=b := by
  have ha' : a ∈ lengthPair n b := he ▸ (by simp [lengthPair] : a ∈ lengthPair n a)
  have hb' : b ∈ lengthPair n a := he.symm ▸ (by simp [lengthPair] : b ∈ lengthPair n b)
  simp [lengthPair] at ha' hb'
  omega

private theorem different_card (n a : ℕ) : ({n} : Multiset ℕ) ≠ lengthPair n a := by
  intro h
  simpa [lengthPair] using congrArg Multiset.card h

/-- The original no-short-return condition is equivalent to this disjoint cycle-type partition.
The interval of smaller lengths is empty throughout the single-cycle regime. -/
theorem allowed_iff_band_types {n k : ℕ} (hk : 2≤k) (hkn : k≤n) (hn : n<3*k)
    (σ : Equiv.Perm (Fin n)) : Allowed k σ ↔
    σ.cycleType={n} ∨ ∃ a ∈ Icc k (n/2), σ.cycleType=lengthPair n a := by
  constructor
  · intro h
    have hsum : σ.cycleType.sum = n := by
      rw [Equiv.Perm.sum_cycleType, support_univ_of_allowed h hk]; simp
    let l := σ.cycleType.toList
    have hl : (l : Multiset ℕ) = σ.cycleType := by simp [l]
    have hs : l.sum = n := by simpa [l] using hsum
    have hb (a : ℕ) (ha : a∈l) : k≤a := le_of_mem_cycleType h (by simpa [l] using ha)
    cases he : l with
    | nil => simp [he] at hs; omega
    | cons a rest =>
      cases rest with
      | nil =>
        left
        simp [he] at hs
        rw [← hl, he, hs]; rfl
      | cons b tail =>
        have ha := hb a (by simp [he])
        have hb' := hb b (by simp [he])
        cases tail with
        | nil =>
          simp [he] at hs
          right
          by_cases hab : a≤b
          · refine ⟨a,mem_Icc.mpr ⟨ha,by omega⟩,?_⟩
            rw [← hl, he, lengthPair, show n-a=b by omega]; rfl
          · refine ⟨b,mem_Icc.mpr ⟨hb',by omega⟩,?_⟩
            rw [← hl, he, lengthPair, show n-b=a by omega]
            exact Multiset.cons_swap a b 0
        | cons c tail =>
          have hc := hb c (by simp [he])
          simp [he] at hs
          omega
  · intro h
    apply allowed_of_cycleType_lower
    · apply Finset.eq_univ_of_card
      rw [← Equiv.Perm.sum_cycleType,Fintype.card_fin]
      rcases h with h | ⟨a,ha,h⟩
      · simp [h]
      · have := (mem_Icc.mp ha).2
        simp [h,lengthPair]; omega
    · intro x hx
      rcases h with h | ⟨a,ha,h⟩
      · simp [h] at hx; omega
      · obtain ⟨hal,har⟩ := mem_Icc.mp ha
        simp [h,lengthPair] at hx
        omega

private theorem conditional_sum {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p] [Fintype (Subtype p)] (f : ι → M) :
    (∑ i, if p i then f i else 0) = ∑ i : Subtype p, f i.val := by
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  simp

private theorem full_weight (n : ℕ) (hn : 2≤n) :
    (∑ σ : Equiv.Perm (Fin n), if σ.cycleType={n} then (X : ℝ[X])^excedances σ else 0) =
      X*eulerian (n-1) := by
  let s := (univ : Finset (Fin n))
  have hw := singleCycleWeight (m := n-1) s (by simp [s]; omega) (by omega)
  simp only [singleton_iff_fullCycle]
  exact (conditional_sum _ _).trans hw

/-- Unordered support multiplicity for a smaller part of size a. -/
def supportMultiplicity (n a : ℕ) : ℕ := if a=n-a then n.choose a / 2 else n.choose a

def cycleContribution (n a : ℕ) : ℝ[X] :=
  C (supportMultiplicity n a : ℝ) * ((X*eulerian (a-1))*(X*eulerian (n-a-1)))

private theorem conditional_pair {n a : ℕ} (ha : 2≤a) (har : a≤n/2) :
    (∑ σ : Equiv.Perm (Fin n), if σ.cycleType=lengthPair n a then (X : ℝ[X])^excedances σ else 0)
      = cycleContribution n a := by
  by_cases he : a=n-a
  · obtain rfl : n=2*a := by omega
    have harith : 2*a-a = a := by omega
    simp only [lengthPair,cycleContribution,supportMultiplicity,harith,if_true,← pow_two]
    exact (conditional_sum _ _).trans (twoCycleWeight ha)
  · unfold lengthPair cycleContribution
    rw [conditional_sum, supportMultiplicity, if_neg he]
    convert unequal_two_cycle_weight (n := n) (a := a) (b := n-a) (by omega) ha (by omega) he using 2

/-- Exact original polynomial in the complete range with at most two cycles. -/
theorem enumerator_band {n k : ℕ} (hk : 2≤k) (hkn : k≤n) (hn : n<3*k) :
    enumerator n k = X*eulerian (n-1) + ∑ a ∈ Icc k (n/2), cycleContribution n a := by
  let wt (σ : Equiv.Perm (Fin n)) := (X : ℝ[X])^excedances σ
  let part (σ : Equiv.Perm (Fin n)) (a : ℕ) : ℝ[X] := if σ.cycleType=lengthPair n a then wt σ else 0
  have split (σ : Equiv.Perm (Fin n)) :
      (if Allowed k σ then wt σ else 0) =
      (if σ.cycleType={n} then wt σ else 0) + ∑ a ∈ Icc k (n/2), part σ a := by
    rw [allowed_iff_band_types hk hkn hn]
    by_cases h : σ.cycleType={n}
    · simp [h,part,different_card]
    · simp only [h, false_or,if_false,zero_add]
      by_cases h' : ∃ a ∈ Icc k (n/2), σ.cycleType=lengthPair n a
      · obtain ⟨a,ha,he⟩ := h'
        rw [if_pos ⟨a,ha,he⟩,sum_eq_single_of_mem a ha]
        · simp [part,he]
        · intro b hb hba
          have hne : σ.cycleType≠lengthPair n b := fun he' ↦ hba
            (min_injective (mem_Icc.mp hb).2 (mem_Icc.mp ha).2 (he'.symm.trans he))
          simp [part,hne]
      · rw [if_neg h']
        symm
        apply sum_eq_zero
        intro a ha
        simp [part,show σ.cycleType≠lengthPair n a from fun he ↦ h' ⟨a,ha,he⟩]
  unfold enumerator
  change (∑ σ, if Allowed k σ then wt σ else 0) = _
  simp_rw [split]
  rw [sum_add_distrib, full_weight n (by omega),sum_comm]
  congr 1
  apply sum_congr rfl
  intro a ha
  exact conditional_pair (by have := (mem_Icc.mp ha).1; omega) (mem_Icc.mp ha).2

#print axioms allowed_iff_band_types
#print axioms enumerator_band
end LongCycleBounds.Band
