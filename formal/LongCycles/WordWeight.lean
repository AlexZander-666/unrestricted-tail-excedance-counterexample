import LongCycles.Statement
import LongCycles.SupportWords

noncomputable section
namespace LongCycles

/-- The excedances of a rooted cyclic word consist of its first edge and
the ascents between consecutive letters of its tail. -/
theorem excedances_rooted_word {n m : ℕ} (x : Fin n) (f : Fin m → Fin n)
    (hm : 0 < m) (hf : Function.Injective f) (hx : ∀ i, x < f i) :
    excedances (x :: List.ofFn f).formPerm =
      1 + (Finset.univ.filter fun i : Fin m =>
        ∃ j : Fin m, j.val = i.val + 1 ∧ f i < f j).card := by
  classical
  let w := x :: List.ofFn f
  let D := Finset.univ.filter fun i : Fin m =>
    ∃ j : Fin m, j.val = i.val + 1 ∧ f i < f j
  have hnot : x ∉ List.ofFn f := by
    rintro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact (hx i).ne' hi
  have hn : w.Nodup := List.nodup_cons.mpr ⟨hnot, List.nodup_ofFn.mpr hf⟩
  have hroot : w.formPerm x = f ⟨0, hm⟩ := by
    have H := List.formPerm_apply_getElem_zero w hn (by simp [w, hm])
    change w.formPerm x = (List.ofFn f)[0]'(_) at H
    simpa using H
  have hnext (i : Fin m) (h : i.val + 1 < m) :
      w.formPerm (f i) = f ⟨i.val + 1, h⟩ := by
    have H := List.formPerm_apply_lt_getElem w hn (i.val+1) (by simp [w]; omega)
    simpa [w] using H
  have hlast (i : Fin m) (h : ¬ i.val+1 < m) : w.formPerm (f i) = x := by
    have hi : i.val+1 = (List.ofFn f).length := by simp; omega
    have H := List.formPerm_apply_getElem_length x (List.ofFn f)
    have eqv : (x :: List.ofFn f)[(List.ofFn f).length] = f i := by
      simp only [← hi, List.getElem_cons_succ, List.getElem_ofFn]
    exact eqv ▸ H
  have hxD : x ∉ D.image f := by
    rintro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact (hx i).ne' hi
  have hset : (Finset.univ.filter fun y : Fin n => y < w.formPerm y) = insert x (D.image f) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hy
      by_cases hyx : y = x
      · exact Or.inl hyx
      · right
        have hyw : y ∈ w := by
          by_contra H
          rw [List.formPerm_apply_of_notMem H] at hy
          exact lt_irrefl _ hy
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ((List.mem_cons.mp hyw).resolve_left hyx)
        by_cases hi : i.val+1 < m
        · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨_,hi⟩, rfl, hnext i hi ▸ hy⟩⟩, rfl⟩
        · exact False.elim ((hx i).asymm (hlast i hi ▸ hy))
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · rw [hroot]
        exact hx _
      · obtain ⟨j, hj, hlt⟩ := (Finset.mem_filter.mp hi).2
        have hh : i.val+1 < m := hj ▸ j.isLt
        rw [hnext i hh]
        exact (show j = ⟨i.val+1, hh⟩ from Fin.ext hj) ▸ hlt
  change (Finset.univ.filter fun y : Fin n => y < w.formPerm y).card = 1 + D.card
  rw [hset, Finset.card_insert_of_notMem hxD, Finset.card_image_of_injective _ hf, Nat.add_comm]

/-- Reversing the ranks of the tail exchanges its ascents with descents of
the permutation in the definition of the ordinary Eulerian polynomial. -/
theorem excedances_ranked_word {n m : ℕ} (x : Fin n) (e : Fin m ↪o Fin n)
    (hm : 0 < m) (hx : ∀ i, x < e i) (π : Equiv.Perm (Fin m)) :
    excedances (x :: List.ofFn (fun i => e (π i).rev)).formPerm = 1 + descents π := by
  rw [excedances_rooted_word x (fun i => e (π i).rev) hm (e.injective.comp (Fin.rev_injective.comp π.injective))
    (fun i => hx (π i).rev)]
  simp [descents]

end LongCycles
