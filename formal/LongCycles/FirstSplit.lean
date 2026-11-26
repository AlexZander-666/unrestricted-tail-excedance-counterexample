import LongCycles.FirstSplitRows
import LongCycles.TwoCycleWeight

noncomputable section
namespace LongCycles

/-- The two first-split identities for every k ≥ 2, with the rows
defined by the original excedance-weighted sum over permutations. -/
theorem firstSplitFamily : FirstSplitFamily := by
  intro k hk
  refine ⟨firstRow_fromPermutations hk, ?_⟩
  rw [secondRow_fromPermutations hk, twoCycleWeight hk]
  ring

#print axioms firstSplitFamily

end LongCycles
