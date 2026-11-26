import LongCycles.Statement
import LongCycles.CycleSizes
import Mathlib.GroupTheory.Perm.Cycle.Type

noncomputable section
namespace LongCycles

/-- Every genuine cycle length of an admissible permutation meets the
cutoff. Mathlib's cycleType omits fixed points; support_univ_of_allowed
below is needed before its sum may be identified with n. -/
theorem le_of_mem_cycleType {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Allowed k σ) {m : ℕ} (hm : m ∈ σ.cycleType) : k ≤ m := by
  obtain ⟨c, τ, heq, hd, hc, hm'⟩ := Equiv.Perm.mem_cycleType_iff.mp hm
  have ho : orderOf c = m := hc.orderOf.trans hm'
  obtain ⟨x, hx, _⟩ := hc
  have hf : τ x = x := (hd x).resolve_left hx
  have hmpos : 0 < m := lt_trans (by decide : 0 < 1)
    (Equiv.Perm.one_lt_of_mem_cycleType hm)
  have hpow : (c ^ m) = 1 := ho ▸ pow_orderOf_eq_one c
  by_contra! hmk
  apply h x m hmpos hmk
  rw [heq, hd.commute.mul_pow, Equiv.Perm.mul_apply,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hf, hpow, Equiv.Perm.one_apply]

theorem support_univ_of_allowed {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Allowed k σ) (hk : 1 < k) : σ.support = Finset.univ := by
  ext x
  simp [Equiv.Perm.mem_support, ne_fixed_of_allowed h hk x]

/-- The original orbit test restricts the cycle types to the one-cycle
case and the two equal-length cases at the first split. -/
theorem only_first_split_types {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Allowed k σ) (hk : 2 ≤ k) (hn : n = 2*k-1 ∨ n = 2*k) :
    σ.cycleType = {n} ∨ (σ.cycleType = {k, k} ∧ n = 2*k) := by
  classical
  have hs : σ.cycleType.sum = n := by
    rw [Equiv.Perm.sum_cycleType, support_univ_of_allowed h hk]
    simp
  have hls : σ.cycleType.toList.sum = n := by simpa using hs
  have hl : ∀ x ∈ σ.cycleType.toList, k ≤ x := by
    intro x hx
    exact le_of_mem_cycleType h (by simpa using hx)
  have hh := firstSplitLengths hk σ.cycleType.toList hl (by simpa only [hls] using hn)
  rw [hls] at hh
  rcases hh with hx | ⟨hx, hn'⟩
  · left
    simpa using congrArg (fun l : List ℕ => (l : Multiset ℕ)) hx
  · right
    refine ⟨?_, hn'⟩
    calc
      σ.cycleType = ([k,k] : List ℕ) := by simpa using congrArg (fun l : List ℕ => (l : Multiset ℕ)) hx
      _ = {k,k} := rfl

/-- Recover the original return-time test from cycleType. Its omitted
fixed points have to be excluded explicitly. -/
theorem allowed_of_cycleType_lower {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (hs : σ.support = Finset.univ) (hl : ∀ m ∈ σ.cycleType, k ≤ m) :
    Allowed k σ := by
  classical
  intro x j hj hjk
  have hx : x ∈ σ.support := by rw [hs]; exact Finset.mem_univ _
  have hmove := Equiv.Perm.mem_support.mp hx
  have hc := Equiv.Perm.isCycle_cycleOf σ hmove
  have hm : (σ.cycleOf x).support.card ∈ σ.cycleType := by
    rw [Equiv.Perm.cycleType, Multiset.mem_map]
    exact ⟨σ.cycleOf x, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx, rfl⟩
  have hjord : j < orderOf (σ.cycleOf x) := by
    rw [hc.orderOf]
    exact hjk.trans_le (hl _ hm)
  have hx' : x ∈ (σ.cycleOf x).support := Equiv.Perm.mem_support.mpr (by
    simpa only [Equiv.Perm.cycleOf_apply_self] using hmove)
  rw [← hc.support_pow_of_pos_of_lt_orderOf hj hjord, Equiv.Perm.mem_support,
    Equiv.Perm.cycleOf_pow_apply_self] at hx'
  exact hx'

theorem allowed_iff_first_split_types {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (hk : 2 ≤ k) (hn : n = 2*k-1 ∨ n = 2*k) :
    Allowed k σ ↔ σ.cycleType = {n} ∨ (σ.cycleType = {k, k} ∧ n = 2*k) := by
  refine ⟨fun h => only_first_split_types h hk hn, fun h => ?_⟩
  apply allowed_of_cycleType_lower
  · apply Finset.eq_univ_of_card
    rw [← Equiv.Perm.sum_cycleType, Fintype.card_fin]
    rcases h with h | ⟨h,h'⟩
    · simp [h]
    · simp [h, h', two_mul]
  · intro m hm
    rcases h with h | ⟨h,_⟩
    · simp [h] at hm
      omega
    · have : m = k := by simpa [h] using hm
      omega

/-- On disjoint supports, the moved points contributing excedances are
disjoint and their union is precisely the excedance set of the product. -/
theorem excedances_disjoint_mul {n : ℕ} {c d : Equiv.Perm (Fin n)}
    (hd : c.Disjoint d) : excedances (c*d) = excedances c + excedances d := by
  classical
  let ec := Finset.univ.filter fun x : Fin n => x < c x
  let ed := Finset.univ.filter fun x : Fin n => x < d x
  have he : (Finset.univ.filter fun x : Fin n => x < (c*d) x) = ec ∪ ed := by
    ext x
    simp only [ec, ed, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hd x with h | h
    · rw [hd.commute.eq, Equiv.Perm.mul_apply, h]
      simp
    · rw [Equiv.Perm.mul_apply, h]
      simp
  have hdis : Disjoint ec ed := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (Finset.mem_filter.mp hx).2.ne'
    have hy' := (Finset.mem_filter.mp hy).2.ne'
    exact (hd x).elim hx' hy'
  unfold excedances
  rw [he, Finset.card_union_of_disjoint hdis]

/-- By Pascal and complementary subset sizes, choosing the half which
contains a fixed distinguished label effects the division by two. -/
theorem central_choose_twice {k : ℕ} (hk : 1 ≤ k) :
    (2*k).choose k = 2 * (2*k-1).choose (k-1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [show 2*(j+1) = (2*j+1)+1 by omega, Nat.choose_succ_succ']
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm_half, show j.succ - 1 = j by omega]
  omega

/-- Actual number of k-element supports containing the distinguished point,
expressed as the unordered pair coefficient in FirstSplitFamily. -/
theorem card_anchored_halves {k : ℕ} (hk : 1 ≤ k) (x : Fin (2*k)) :
    ((Finset.univ.powersetCard k).filter fun s : Finset (Fin (2*k)) =>
       ({x} : Finset (Fin (2*k))) ⊆ s).card = (2*k).choose k / 2 := by
  rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
    (by simpa using hk), central_choose_twice hk]
  simp

end LongCycles
