import Std

namespace LongCycles

/-- A list of cycle lengths, each at least k, has at most two entries when
its sum is 2*k-1 or 2*k. Two entries are possible only at the latter
threshold and then both lengths are k. No ordering of the list is assumed. -/
theorem firstSplitLengths {k : Nat} (hk : 2 ≤ k) (l : List Nat)
    (h : ∀ m ∈ l, k ≤ m) (hs : l.sum = 2 * k - 1 ∨ l.sum = 2 * k) :
    l = [l.sum] ∨ (l = [k, k] ∧ l.sum = 2 * k) := by
  cases l with
  | nil => simp at hs; omega
  | cons a l =>
    cases l with
    | nil => simp
    | cons b l =>
      have ha := h a (by simp)
      have hb := h b (by simp)
      cases l with
      | nil =>
        simp at hs
        have ea : a = k := by omega
        have eb : b = k := by omega
        subst a
        subst b
        right
        exact ⟨rfl, by simp; omega⟩
      | cons c l =>
        have hc := h c (by simp)
        simp at hs
        omega

end LongCycles
