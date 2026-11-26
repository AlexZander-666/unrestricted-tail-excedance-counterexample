import LongCycles.WordWeight

noncomputable section
namespace LongCycles

open Polynomial
open scoped BigOperators

noncomputable instance {n : ℕ} (s : Finset (Fin n)) : Fintype (CyclesOn s) :=
  Fintype.ofFinite _

/-- Uniform, weight-preserving bijection on any specified support. -/
theorem weightedCycleEquiv {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m+1) (hm : 0 < m) :
    ∃ e : Equiv.Perm (Fin m) ≃ CyclesOn s,
      ∀ π, excedances (e π).val = 1 + descents π := by
  classical
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  let x := s.min' hne
  have hx : x ∈ s := s.min'_mem hne
  have ht : (s.erase x).card = m := by rw [Finset.card_erase_of_mem hx, hs]; omega
  let e := (s.erase x).orderEmbOfFin ht
  have hxmin (i : Fin m) : x < e i := by
    have hmem := Finset.mem_erase.mp ((s.erase x).orderEmbOfFin_mem ht i)
    exact lt_of_le_of_ne (s.min'_le _ hmem.2) hmem.1.symm
  let u := (Equiv.mulLeft (Fin.revPerm : Equiv.Perm (Fin m))).trans
    ((permOrderingEquiv _ ht).trans ((deleteFirstEquiv s x hx).symm.trans
      (cycleWordEquiv s x hx (by omega)).symm))
  refine ⟨u, ?_⟩
  intro π
  exact excedances_ranked_word x e hm hxmin π

/-- Weighted sum of all actual cycles with a given (m+1)-element support. -/
theorem singleCycleWeight {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m+1) (hm : 0 < m) :
    (∑ c : CyclesOn s, (X : Polynomial ℝ) ^ (excedances c.val)) = X * eulerian m := by
  classical
  obtain ⟨e, he⟩ := weightedCycleEquiv s hs hm
  rw [← e.sum_comp (fun c : CyclesOn s => (X : Polynomial ℝ)^(excedances c.val))]
  simp_rw [he, pow_add, pow_one]
  simp only [eulerian, Finset.mul_sum]

end LongCycles
