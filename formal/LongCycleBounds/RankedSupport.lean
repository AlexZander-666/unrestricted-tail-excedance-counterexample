import LongCycleBounds.UniversalInsertion

/-! Extending a permutation by the order-preserving ranks of any support. -/
noncomputable section
namespace LongCycleBounds.Insertion
open LongCycles Finset Equiv

abbrev Supported {n : ℕ} (s : Finset (Fin n)) :=
  {f : Perm (Fin n) // ∀ x, x ∉ s → f x=x}

def placeEquiv {n m : ℕ} (s : Finset (Fin n)) (h : s.card=m) :
    Perm (Fin m) ≃ Supported s :=
  ((s.orderIsoOfFin h).toEquiv.permCongr).trans (Perm.subtypeEquivSubtypePerm (·∈s))

theorem place_image {n m : ℕ} (s : Finset (Fin n)) (h : s.card=m) (f : Perm (Fin m))
    (i : Fin m) :
    (placeEquiv s h f).val (s.orderEmbOfFin h i) = s.orderEmbOfFin h (f i) := by
  change ((s.orderIsoOfFin h).toEquiv.permCongr f).ofSubtype
    ((s.orderIsoOfFin h i : s) : Fin n) = _
  rw [Perm.ofSubtype_apply_of_mem _ (s.orderIsoOfFin h i).property]
  simp [Equiv.permCongr_apply]
  exact (s.orderIsoOfFin h).symm_apply_apply i

theorem place_pow_image {n m : ℕ} (s : Finset (Fin n)) (h : s.card=m) (f : Perm (Fin m))
    (i : Fin m) (a : ℕ) :
    ((placeEquiv s h f).val^a) (s.orderEmbOfFin h i) = s.orderEmbOfFin h ((f^a) i) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [pow_succ',Perm.mul_apply,ih,place_image,pow_succ',Perm.mul_apply]

/-- Rank placement preserves the strict excedance count on an arbitrary prescribed support. -/
theorem excedances_place {n m : ℕ} (s : Finset (Fin n)) (h : s.card=m) (f : Perm (Fin m)) :
    excedances (placeEquiv s h f).val = excedances f := by
  classical
  let e := s.orderEmbOfFin h
  have sets : (univ.filter fun x ↦ x < (placeEquiv s h f).val x) =
      (univ.filter fun i ↦ i<f i).map e.toEmbedding := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_map]
    constructor
    · intro moved
      have hx : x∈s := by
        by_contra no
        rw [(placeEquiv s h f).property _ no] at moved
        exact lt_irrefl _ moved
      obtain ⟨i,hi⟩ : ∃ i, e i=x := by
        change x∈Set.range (s.orderEmbOfFin h)
        rwa [range_orderEmbOfFin]
      subst x
      have hx' : e i < e (f i) := by simpa only [e,place_image] using moved
      exact ⟨i,e.lt_iff_lt.mp hx',rfl⟩
    · rintro ⟨i,hi,rfl⟩
      change e i < (placeEquiv s h f).val (s.orderEmbOfFin h i)
      rw [place_image]
      exact e.strictMono hi
  unfold excedances
  rw [sets, card_map]

theorem lengthAt_place {n m : ℕ} (s : Finset (Fin n)) (h : s.card=m) (f : Perm (Fin m))
    (i : Fin m) : lengthAt (placeEquiv s h f).val (s.orderEmbOfFin h i) = lengthAt f i := by
  have returns (a : ℕ) : ((placeEquiv s h f).val^a) (s.orderEmbOfFin h i) = s.orderEmbOfFin h i
      ↔ (f^a) i=i := by rw [place_pow_image]; exact (s.orderEmbOfFin h).injective.eq_iff
  exact le_antisymm (lengthAt_le_return _ _ (lengthAt_pos _ _) ((returns _).mpr (pow_lengthAt _ _)))
    (lengthAt_le_return _ _ (lengthAt_pos _ _) ((returns _).mp (pow_lengthAt _ _)))

end LongCycleBounds.Insertion
