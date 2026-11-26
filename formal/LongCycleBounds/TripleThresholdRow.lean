import LongCycleBounds.BandShape
import LongCycleBounds.TripleCycleWeight

/-! The quotient of the first row that permits three long cycles. -/
namespace LongCycleBounds.Band
open Polynomial LongCycles Finset
open scoped Classical

noncomputable section

/-- At the three-cycle threshold, the new contribution has three cycles of length
exactly $k$. The denominator $6$ counts their support orderings. -/
def thresholdQuotient (k : ℕ) : ℝ[X] :=
  deformedRow (3*k) k 1 +
    C (((3*k).factorial : ℝ) / (6*(k.factorial : ℝ)^3)) * X^2 * eulerian (k-1)^3

/-- The cubic cannot change the leading term, and its factor $X^2$ preserves
the constant term. -/
theorem thresholdQuotient_shape {k : ℕ} (hk : 2 ≤ k) :
    (thresholdQuotient k).natDegree = 3*k-2 ∧ (thresholdQuotient k).Monic ∧
      (thresholdQuotient k).eval 0 = 1 := by
  let cubic := C (((3*k).factorial : ℝ) / (6*(k.factorial : ℝ)^3)) *
    X^2 * eulerian (k-1)^3
  have hbase := deformed_shape (n := 3*k) hk (by omega) (by omega) 1
  have hcubic : cubic.natDegree ≤ 2+3*(k-2) := by
    calc
      _ ≤ (C (((3*k).factorial : ℝ) / (6*(k.factorial : ℝ)^3)) * X^2).natDegree +
            (eulerian (k-1)^3).natDegree := natDegree_mul_le
      _ ≤ (X^2 : ℝ[X]).natDegree + 3*(eulerian (k-1)).natDegree := by
        exact Nat.add_le_add (natDegree_C_mul_le ..) natDegree_pow_le
      _ = _ := by
        rw [natDegree_X_pow, show k-1 = k-2+1 by omega, (eulerian_degree_monic _).1]
  have hlt : cubic.natDegree < (deformedRow (3*k) k 1).natDegree := by
    rw [hbase.1]
    omega
  change (deformedRow (3*k) k 1 + cubic).natDegree = 3*k-2 ∧
    (deformedRow (3*k) k 1 + cubic).Monic ∧ (deformedRow (3*k) k 1 + cubic).eval 0 = 1
  exact ⟨(natDegree_add_eq_left_of_natDegree_lt hlt).trans hbase.1,
    hbase.2.1.add_of_left (degree_lt_degree hlt), by simp [cubic, hbase.2.2]⟩

/-- The threshold quotient is reciprocal on every nonzero real input. -/
theorem thresholdQuotient_reciprocity {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ≠ 0) :
    t^(3*k-2) * (thresholdQuotient k).eval t⁻¹ = (thresholdQuotient k).eval t := by
  have order : 3*k-2 = (k-2)*3+4 := by omega
  have hrec : t^(k-2) * (eulerian (k-1)).eval t⁻¹ = (eulerian (k-1)).eval t := by
    simpa only [show k-2+1 = k-1 by omega] using eulerian_reciprocity (k-2) ht
  simp only [thresholdQuotient, eval_add, mul_add,
    deformed_reciprocity hk (show k ≤ 3*k by omega) 1 ht]
  congr 1
  simp only [eval_mul, eval_pow, eval_X, eval_C]
  rw [← hrec, order, pow_add, pow_mul]
  field_simp

#print axioms thresholdQuotient_shape
#print axioms thresholdQuotient_reciprocity

private theorem allowed_iff_threshold_types {k : ℕ} (hk : 2 ≤ k)
    (σ : Equiv.Perm (Fin (3*k))) : Allowed k σ ↔
      σ.cycleType = {3*k} ∨
        (∃ a ∈ Icc k (3*k/2), σ.cycleType = lengthPair (3*k) a) ∨
        σ.cycleType = {k,k,k} := by
  constructor
  · intro h
    have hsum : σ.cycleType.sum = 3*k := by
      rw [Equiv.Perm.sum_cycleType, support_univ_of_allowed h hk]
      simp
    let l := σ.cycleType.toList
    have hl : (l : Multiset ℕ) = σ.cycleType := Multiset.coe_toList _
    have hs : l.sum = 3*k := by simpa [l] using hsum
    have lower (a : ℕ) (ha : a ∈ l) : k ≤ a :=
      le_of_mem_cycleType h (by simpa [l] using ha)
    cases he : l with
    | nil => simp [he] at hs; omega
    | cons a rest =>
      cases rest with
      | nil =>
        left
        simp [he] at hs
        rw [← hl, he, hs]
        rfl
      | cons b tail =>
        have ha := lower a (by simp [he])
        have hb := lower b (by simp [he])
        cases tail with
        | nil =>
          simp [he] at hs
          apply Or.inr ∘ Or.inl
          by_cases hab : a ≤ b
          · refine ⟨a, mem_Icc.mpr ⟨ha, by omega⟩, ?_⟩
            rw [← hl, he, lengthPair, show 3*k-a = b by omega]
            rfl
          · refine ⟨b, mem_Icc.mpr ⟨hb, by omega⟩, ?_⟩
            rw [← hl, he, lengthPair, show 3*k-b = a by omega]
            exact Multiset.cons_swap a b 0
        | cons c tail =>
          have hc := lower c (by simp [he])
          cases tail with
          | nil =>
            apply Or.inr ∘ Or.inr
            apply (allowed_three_iff_tripleType hk σ).1
            exact ⟨h, by rw [← hl, he]; rfl⟩
          | cons d tail =>
            have hd := lower d (by simp [he])
            simp [he] at hs
            omega
  · rintro (hs | ⟨a, ha, hs⟩ | hs)
    · apply allowed_of_cycleType_lower
      · apply eq_univ_of_card
        rw [← Equiv.Perm.sum_cycleType, Fintype.card_fin, hs]
        simp
      · intro b hb
        simp [hs] at hb
        omega
    · obtain ⟨hal, har⟩ := mem_Icc.mp ha
      apply allowed_of_cycleType_lower
      · apply eq_univ_of_card
        rw [← Equiv.Perm.sum_cycleType, Fintype.card_fin, hs]
        simp [lengthPair]
        omega
      · intro b hb
        simp [hs, lengthPair] at hb
        omega
    · exact ((allowed_three_iff_tripleType hk σ).2 hs).1

private theorem weight_on_subtype {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] [Fintype (Subtype p)] (f : ι → ℝ[X]) :
    (∑ a, if p a then f a else 0) = ∑ a : Subtype p, f a.val := by
  rw [← sum_filter]
  apply sum_subtype
  simp

private theorem threshold_single_weight {k : ℕ} (hk : 2 ≤ k) :
    (∑ σ : Equiv.Perm (Fin (3*k)), if σ.cycleType = {3*k}
      then (X : ℝ[X])^excedances σ else 0) = X*eulerian (3*k-1) := by
  let s := (univ : Finset (Fin (3*k)))
  have h := singleCycleWeight (m := 3*k-1) s (by simp [s]; omega) (by omega)
  simp only [singleton_iff_fullCycle]
  exact (weight_on_subtype _ _).trans h

private theorem threshold_pair_weight {k a : ℕ} (ha : 2 ≤ a) (har : a ≤ 3*k/2) :
    (∑ σ : Equiv.Perm (Fin (3*k)), if σ.cycleType = lengthPair (3*k) a
      then (X : ℝ[X])^excedances σ else 0) = cycleContribution (3*k) a := by
  by_cases he : a = 3*k-a
  · have hn : 3*k = 2*a := by omega
    rw [hn]
    have opposite : 2*a-a = a := by omega
    simp only [lengthPair, cycleContribution, supportMultiplicity, opposite, if_true, ← pow_two]
    exact (weight_on_subtype _ _).trans (twoCycleWeight ha)
  · unfold lengthPair cycleContribution
    rw [weight_on_subtype, supportMultiplicity, if_neg he]
    convert unequal_two_cycle_weight (n := 3*k) (a := a) (b := 3*k-a)
      (by omega) ha (by omega) he using 2

private theorem threshold_pair_unique {n a b : ℕ} (ha : a ≤ n/2) (hb : b ≤ n/2)
    (h : lengthPair n a = lengthPair n b) : a = b := by
  have a_mem : a ∈ lengthPair n b := h ▸ (by simp [lengthPair] : a ∈ lengthPair n a)
  have b_mem : b ∈ lengthPair n a := h.symm ▸ (by simp [lengthPair] : b ∈ lengthPair n b)
  simp [lengthPair] at a_mem b_mem
  omega

/-- Decompose the original permutation sum at the threshold by its number of cycles. -/
theorem actual_threshold_row_add_triple {k : ℕ} (hk : 2 ≤ k) :
    enumerator (3*k) k = X*deformedRow (3*k) k 1 + tripleContribution k := by
  let n := 3*k
  let W (σ : Equiv.Perm (Fin n)) := (X : ℝ[X])^excedances σ
  let pair (σ : Equiv.Perm (Fin n)) (a : ℕ) :=
    if σ.cycleType = lengthPair n a then W σ else 0
  have one_two (σ : Equiv.Perm (Fin n)) (a : ℕ) (h : σ.cycleType = {n}) :
      σ.cycleType ≠ lengthPair n a := by
    intro h'
    have e := congrArg Multiset.card (h.symm.trans h')
    simp [lengthPair] at e
  have three_two (σ : Equiv.Perm (Fin n)) (a : ℕ) (h : σ.cycleType = {k,k,k}) :
      σ.cycleType ≠ lengthPair n a := by
    intro h'
    have e := congrArg Multiset.card (h.symm.trans h')
    simp [lengthPair] at e
  have one_three (σ : Equiv.Perm (Fin n)) (h : σ.cycleType = {n}) :
      σ.cycleType ≠ {k,k,k} := by
    intro h'
    have e := congrArg Multiset.card (h.symm.trans h')
    simp at e
  have split (σ : Equiv.Perm (Fin n)) :
      (if Allowed k σ then W σ else 0) =
        (if σ.cycleType = {n} then W σ else 0) +
          (∑ a ∈ Icc k (n/2), pair σ a) +
          (if σ.cycleType = {k,k,k} then W σ else 0) := by
    by_cases h₁ : σ.cycleType = {n}
    · have allowed := (allowed_iff_threshold_types hk σ).2 (Or.inl h₁)
      have noPairs : (∑ a ∈ Icc k (n/2), pair σ a) = 0 :=
        sum_eq_zero fun a _ ↦ if_neg (one_two σ a h₁)
      rw [if_pos allowed, if_pos h₁, noPairs, if_neg (one_three σ h₁)]
      simp
    by_cases h₃ : σ.cycleType = {k,k,k}
    · have allowed := ((allowed_three_iff_tripleType hk σ).2 h₃).1
      have noPairs : (∑ a ∈ Icc k (n/2), pair σ a) = 0 :=
        sum_eq_zero fun a _ ↦ if_neg (three_two σ a h₃)
      rw [if_pos allowed, if_neg h₁, noPairs, if_pos h₃]
      simp
    rw [allowed_iff_threshold_types hk]
    simp only [show (3*k : ℕ) = n from rfl, h₁, h₃, false_or, or_false,
      if_false, zero_add, add_zero]
    by_cases hasPair : ∃ a ∈ Icc k (n/2), σ.cycleType = lengthPair n a
    · obtain ⟨a, ha, he⟩ := hasPair
      rw [if_pos ⟨a, ha, he⟩, sum_eq_single_of_mem a ha]
      · simp [pair, he]
      · intro b hb hne
        have different : σ.cycleType ≠ lengthPair n b := fun e ↦
          hne (threshold_pair_unique (mem_Icc.mp hb).2 (mem_Icc.mp ha).2 (e.symm.trans he))
        simp [pair, different]
    · rw [if_neg hasPair]
      symm
      apply sum_eq_zero
      intro a ha
      simp [pair, show σ.cycleType ≠ lengthPair n a from fun he ↦ hasPair ⟨a, ha, he⟩]
  have cubic :
      (∑ σ : Equiv.Perm (Fin n), if σ.cycleType = {k,k,k} then W σ else 0) =
        tripleContribution k := by
    dsimp only [W]
    simp_rw [← allowed_three_iff_tripleType hk]
    exact tripleThreshold_weight hk
  have unordered :
      (∑ a ∈ Icc k (n/2), cycleContribution n a) =
        X*(C (1/2 : ℝ)*∑ a ∈ Icc k (n-k),
          C (n.choose a:ℝ)*X*eulerian (a-1)*eulerian (n-a-1)) := by
    have oriented :
        (∑ a ∈ Icc k (n-k), orderedTerm n a) =
          X*(∑ a ∈ Icc k (n-k), C (n.choose a:ℝ)*X*eulerian (a-1)*eulerian (n-a-1)) := by
      rw [mul_sum]
      exact sum_congr rfl (fun a _ ↦ by unfold orderedTerm; ring)
    let E := ∑ a ∈ Icc k (n/2), cycleContribution n a
    change E = _
    calc
      E = C (1/2 : ℝ)*(2*E) := by
        rw [← mul_assoc, ← map_ofNat (f := C) (n := 2), ← map_mul]
        norm_num
      _ = _ := by
        rw [show 2*E = _ from twice_contributions n k hk (by dsimp [n]; omega), oriented]
        ring
  unfold enumerator
  change (∑ σ, if Allowed k σ then W σ else 0) =
    X*deformedRow n k 1 + tripleContribution k
  simp_rw [split]
  rw [sum_add_distrib, sum_add_distrib, cubic, sum_comm]
  have pairs :
      (∑ a ∈ Icc k (n/2), ∑ σ : Equiv.Perm (Fin n), pair σ a) =
        ∑ a ∈ Icc k (n/2), cycleContribution n a := by
    apply sum_congr rfl
    intro a ha
    obtain ⟨ha, hb⟩ := mem_Icc.mp ha
    exact threshold_pair_weight (by omega) hb
  rw [show (∑ σ : Equiv.Perm (Fin n), if σ.cycleType = {n} then W σ else 0) =
    X*eulerian (n-1) from threshold_single_weight hk, pairs, unordered, deformedRow, mul_add]

/-- The threshold quotient is the exact original enumerator with its zero factor removed. -/
theorem actual_threshold_row {k : ℕ} (hk : 2 ≤ k) :
    enumerator (3*k) k = X*thresholdQuotient k := by
  rw [actual_threshold_row_add_triple hk, thresholdQuotient, tripleContribution]
  ring

#print axioms actual_threshold_row_add_triple
#print axioms actual_threshold_row

end
end LongCycleBounds.Band
