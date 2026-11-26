import Statement

/-! Inserting the maximum into the actual permutations in the Eulerian sum. -/

noncomputable section
open scoped BigOperators Classical

namespace ClusterGraphAudit.EulerianInsertion

open Polynomial

/-- Insert the maximum label at the position `k`. The other positions retain order. -/
def insertMax {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  ((finSuccEquiv' k).trans π.optionCongr).trans (finSuccEquiv' (Fin.last n)).symm

@[simp]
theorem insertMax_at {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    insertMax π k k = Fin.last n := by
  simp [insertMax]

@[simp]
theorem insertMax_above {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin (n + 1)) (i : Fin n) :
    insertMax π k (k.succAbove i) = (π i).castSucc := by
  simp [insertMax]

private theorem insertMax_injective (n : ℕ) : Function.Injective
    (fun a : Equiv.Perm (Fin n) × Fin (n + 1) ↦ insertMax a.1 a.2) := by
  rintro ⟨π, k⟩ ⟨τ, l⟩ h
  change insertMax π k = insertMax τ l at h
  have hk : k = l := (insertMax τ l).injective (by rw [← h, insertMax_at, h, insertMax_at])
  subst l
  have he : π = τ := by
    apply Equiv.ext
    intro i
    apply Fin.castSucc_injective n
    simpa only [insertMax_above] using congrArg (fun f : Equiv.Perm (Fin (n + 1)) ↦
      f (k.succAbove i)) h
  subst τ
  rfl

/-- Removing the maximum and recording its slot recovers the original permutation. -/
def insertMaxEquiv (n : ℕ) : Equiv.Perm (Fin n) × Fin (n + 1) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨insertMax_injective n, Fintype.card_congr
      ((Equiv.prodComm _ _).trans Equiv.Perm.decomposeFin.symm)⟩)

@[simp]
theorem insertMaxEquiv_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    insertMaxEquiv n (π, k) = insertMax π k := rfl

/-- Inverting insertion locates the maximum in the new permutation. -/
theorem inverse_slot {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ((insertMaxEquiv n).symm σ).2 = σ.symm (Fin.last n) := by
  let data := (insertMaxEquiv n).symm σ
  have he : insertMax data.1 data.2 = σ := (insertMaxEquiv n).apply_symm_apply σ
  apply σ.injective
  simpa only [insertMax_at, Equiv.apply_symm_apply] using
    congrArg (fun τ : Equiv.Perm (Fin (n + 1)) ↦ τ data.2) he.symm

/-- The old permutation returned by the inverse has precisely the surviving labels. -/
theorem inverse_values {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    let data := (insertMaxEquiv n).symm σ
    σ (data.2.succAbove i) = (data.1 i).castSucc := by
  let data := (insertMaxEquiv n).symm σ
  have he : insertMax data.1 data.2 = σ := (insertMaxEquiv n).apply_symm_apply σ
  simpa only [insertMax_above] using
    congrArg (fun τ : Equiv.Perm (Fin (n + 1)) ↦ τ (data.2.succAbove i)) he.symm

private theorem val_above {n : ℕ} (k : Fin (n + 1)) (i : Fin n) :
    (k.succAbove i).val = if i.val < k.val then i.val else i.val + 1 := by
  by_cases h : i.val < k.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt k i (show i.castSucc < k from h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc k i (show k ≤ i.castSucc from Nat.le_of_not_gt h)]
    rfl

private theorem adjacency_above {n : ℕ} (k : Fin (n + 1)) (i j : Fin n) :
    (k.succAbove i).val + 1 = (k.succAbove j).val ↔
      i.val + 1 = j.val ∧ j.castSucc ≠ k := by
  have he : j.castSucc ≠ k ↔ j.val ≠ k.val :=
    ⟨fun h e ↦ h (Fin.ext e), fun h e ↦ h (congrArg Fin.val e)⟩
  simp only [val_above, he]
  split_ifs <;> omega

private theorem slot_is_predecessor {n : ℕ} (k : Fin (n + 1)) (j : Fin n) :
    k.val + 1 = (k.succAbove j).val ↔ j.castSucc = k := by
  rw [val_above]
  constructor
  · intro h
    apply Fin.ext
    change j.val = k.val
    split_ifs at h <;> omega
  · intro h
    have he : j.val = k.val := congrArg Fin.val h
    simp [he]

/-- Descents indexed by their right endpoints. -/
def rightDescents {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ ∃ i : Fin n, i.val + 1 = j.val ∧ π j < π i)

@[simp]
theorem mem_rightDescents {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    j ∈ rightDescents π ↔ ∃ i : Fin n, i.val + 1 = j.val ∧ π j < π i := by
  simp [rightDescents]

/-- Passing from left endpoints to right endpoints preserves the original descent count. -/
theorem descents_eq_card_right {n : ℕ} (π : Equiv.Perm (Fin n)) :
    descents π = (rightDescents π).card := by
  let left := Finset.univ.filter (fun i : Fin n ↦ ∃ j : Fin n, j.val = i.val + 1 ∧ π j < π i)
  change left.card = (rightDescents π).card
  have hmem (i : Fin n) (hi : i ∈ left) :
      ∃ j : Fin n, j.val = i.val + 1 ∧ π j < π i := (Finset.mem_filter.mp hi).2
  let f (i : Fin n) (hi : i ∈ left) : Fin n := (hmem i hi).choose
  have hf (i : Fin n) (hi : i ∈ left) : (f i hi).val = i.val + 1 ∧ π (f i hi) < π i :=
    (hmem i hi).choose_spec
  refine Finset.card_bij f (fun i hi ↦ (mem_rightDescents π _).mpr ⟨i, (hf i hi).1.symm,
    (hf i hi).2⟩) ?_ ?_
  · intro i hi j hj h
    apply Fin.ext
    have he := congrArg Fin.val h
    rw [(hf i hi).1, (hf j hj).1] at he
    omega
  · intro j hj
    obtain ⟨i, he, hi⟩ := (mem_rightDescents π j).mp hj
    have hleft : i ∈ left := Finset.mem_filter.mpr ⟨Finset.mem_univ i, j, he.symm, hi⟩
    exact ⟨i, hleft, Fin.ext ((hf i hleft).1.trans he)⟩

private theorem inserted_not_rightDescent {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    k ∉ rightDescents (insertMax π k) := by
  intro h
  obtain ⟨i, _, hi⟩ := (mem_rightDescents _ _).mp h
  rw [insertMax_at] at hi
  exact (not_lt_of_ge (Fin.le_last _)) hi

private theorem mem_insertMax_above {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin (n + 1))
    (j : Fin n) : k.succAbove j ∈ rightDescents (insertMax π k) ↔
    j ∈ rightDescents π ∨ j.castSucc = k := by
  rw [mem_rightDescents, mem_rightDescents]
  constructor
  · rintro ⟨a, ha, hlt⟩
    rcases eq_or_ne a k with he | hne
    · subst a
      exact Or.inr ((slot_is_predecessor k j).mp ha)
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hne
      exact Or.inl ⟨i, ((adjacency_above k i j).mp ha).1,
        by simpa only [insertMax_above, Fin.castSucc_lt_castSucc_iff] using hlt⟩
  · by_cases hk : j.castSucc = k
    · intro _
      exact ⟨k, (slot_is_predecessor k j).mpr hk, by simp⟩
    · rintro (⟨i, hi, hij⟩ | he)
      · exact ⟨k.succAbove i, (adjacency_above k i j).mpr ⟨hi, hk⟩, by simpa using hij⟩
      · exact (hk he).elim

/-- Inserting the maximum adds the old position immediately after that slot
to the right-descent set, unless the slot is last. -/
theorem rightDescents_insertMax {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin (n + 1)) :
    rightDescents (insertMax π k) =
      (rightDescents π ∪ Finset.univ.filter (fun j : Fin n ↦ j.castSucc = k)).map
        ⟨k.succAbove, (Fin.strictMono_succAbove k).injective⟩ := by
  ext j
  rcases eq_or_ne j k with he | hne
  · subst j
    refine iff_of_false (inserted_not_rightDescent π k) ?_
    rw [Finset.mem_map]
    rintro ⟨i, _, hi⟩
    exact k.succAbove_ne i hi
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hne
    change _ ↔ (⟨k.succAbove, (Fin.strictMono_succAbove k).injective⟩ : Fin n ↪ _)
      i ∈ _
    rw [Finset.mem_map', mem_insertMax_above, Finset.mem_union, Finset.mem_filter_univ]

@[simp]
theorem descents_insertMax_last {n : ℕ} (π : Equiv.Perm (Fin n)) :
    descents (insertMax π (Fin.last n)) = descents π := by
  have h : (Finset.univ.filter fun i : Fin n ↦ i.castSucc = Fin.last n) = ∅ := by
    ext i
    simp
  simp only [descents_eq_card_right, rightDescents_insertMax, Finset.card_map, h,
    Finset.union_empty]

theorem descents_insertMax_castSucc {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    descents (insertMax π j.castSucc) =
      if j ∈ rightDescents π then descents π else descents π + 1 := by
  have hf : (Finset.univ.filter fun i : Fin n ↦ i.castSucc = j.castSucc) = {j} := by
    ext i
    simp
  have hu : rightDescents π ∪ {j} = insert j (rightDescents π) := by
    ext i
    simp
  simp only [descents_eq_card_right, rightDescents_insertMax, Finset.card_map, hf, hu]
  by_cases hj : j ∈ rightDescents π
  · rw [if_pos hj, Finset.insert_eq_of_mem hj]
  · rw [if_neg hj, Finset.card_insert_of_notMem hj]

/-- The two insertion weights for a permutation with `d` descents. -/
theorem sum_insertion_weights {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (∑ k : Fin (n + 1), (X : Polynomial ℤ) ^ descents (insertMax π k)) =
      (descents π + 1) • X ^ descents π + (n - descents π) • X ^ (descents π + 1) := by
  have hterm (j : Fin n) : (X : Polynomial ℤ) ^ descents (insertMax π j.castSucc) =
      if j ∈ rightDescents π then X ^ descents π else X ^ (descents π + 1) := by
    rw [descents_insertMax_castSucc]
    split_ifs <;> rfl
  rw [Fin.sum_univ_castSucc, descents_insertMax_last]
  simp_rw [hterm, Finset.sum_ite, Finset.sum_const]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_notMem_eq_sdiff,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin, ← descents_eq_card_right, add_nsmul, one_nsmul]
  abel

/-- The classical Eulerian differential operator. -/
def step (m : ℤ) (p : Polynomial ℤ) : Polynomial ℤ :=
  (1 + C m * X) * p + X * (1 - X) * derivative p

private theorem X_mul_derivative_X_pow (d : ℕ) :
    (X : Polynomial ℤ) * derivative (X ^ d) = C (d : ℤ) * X ^ d := by
  cases d with
  | zero => simp
  | succ d =>
    rw [derivative_X_pow_succ, Nat.cast_succ, pow_succ]
    ring

/-- The operator reproduces the two slot counts on the monomial of a permutation. -/
theorem step_X_pow {m d : ℕ} (hd : d ≤ m) :
    step (m : ℤ) ((X : Polynomial ℤ) ^ d) =
      (d + 1) • X ^ d + (m - d) • X ^ (d + 1) := by
  calc
    _ = (1 + C (m : ℤ) * X) * X ^ d + (1 - X) * (X * derivative (X ^ d)) := by
      unfold step
      ring
    _ = _ := by
      rw [X_mul_derivative_X_pow]
      simp only [nsmul_eq_mul, ← C_eq_natCast, Nat.cast_add, Nat.cast_one, Nat.cast_sub hd, pow_succ]
      ring

theorem step_sum {α : Type*} (m : ℤ) (s : Finset α) (f : α → Polynomial ℤ) :
    step m (∑ a ∈ s, f a) = ∑ a ∈ s, step m (f a) := by
  simp only [step, derivative_sum, Finset.mul_sum, Finset.sum_add_distrib]

/-- The descent enumerator, with the empty permutation allowed at length zero. -/
def row (n : ℕ) : Polynomial ℤ :=
  ∑ π : Equiv.Perm (Fin n), X ^ descents π

@[simp]
theorem row_eq_eulerian (m : Size) : row m.val = eulerian m := rfl

/-- The maximum-insertion recurrence on full permutation sums. -/
theorem row_succ (n : ℕ) : step (n : ℤ) (row n) = row (n + 1) := by
  unfold row
  rw [step_sum]
  calc
    _ = ∑ π : Equiv.Perm (Fin n), ∑ k : Fin (n + 1), X ^ descents (insertMax π k) := by
      apply Finset.sum_congr rfl
      intro π _
      have hd : descents π ≤ n := by
        rw [descents_eq_card_right]
        simpa only [Fintype.card_fin] using Finset.card_le_univ (rightDescents π)
      rw [step_X_pow hd, sum_insertion_weights]
    _ = ∑ z : Equiv.Perm (Fin n) × Fin (n + 1), X ^ descents (insertMax z.1 z.2) :=
      (Fintype.sum_prod_type' (fun (π : Equiv.Perm (Fin n)) (k : Fin (n + 1)) ↦
        (X : Polynomial ℤ) ^ descents (insertMax π k))).symm
    _ = _ := Fintype.sum_equiv (insertMaxEquiv n)
      (fun z ↦ (X : Polynomial ℤ) ^ descents (insertMax z.1 z.2))
      (fun π ↦ (X : Polynomial ℤ) ^ descents π) (fun _ ↦ rfl)

/-- The same recurrence on the actual complete-component row in the statement. -/
theorem eulerian_succ (m : Size) : step (m.val : ℤ) (eulerian m) =
    eulerian ⟨m.val + 1, Nat.succ_pos _⟩ := row_succ m.val

@[simp]
theorem step_coeff_zero (m : ℤ) (p : Polynomial ℤ) : (step m p).coeff 0 = p.coeff 0 := by
  simp [step, coeff_zero_eq_eval_zero]

@[simp]
theorem row_zero : row 0 = 1 := by
  let : Unique (Equiv.Perm (Fin 0)) := uniqueOfSubsingleton 1
  have hd (π : Equiv.Perm (Fin 0)) : descents π = 0 := by
    simp [descents]
  simp [row, hd]

@[simp]
theorem row_one : row 1 = 1 := by
  rw [← row_succ 0, row_zero]
  norm_num [step]

@[simp]
theorem row_two : row 2 = 1 + X := by
  rw [← row_succ 1, row_one]
  norm_num [step]

theorem eulerian_one : eulerian ⟨1, by decide⟩ = 1 := row_one

theorem eulerian_two : eulerian ⟨2, by decide⟩ = 1 + X := row_two

theorem row_coeff_zero (n : ℕ) : (row n).coeff 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [← row_succ n, step_coeff_zero, ih]

theorem eulerian_coeff_zero (m : Size) : (eulerian m).coeff 0 = 1 := row_coeff_zero m.val

#print axioms insertMaxEquiv
#print axioms inverse_slot
#print axioms inverse_values
#print axioms descents_eq_card_right
#print axioms rightDescents_insertMax
#print axioms sum_insertion_weights
#print axioms step_X_pow
#print axioms row_succ
#print axioms eulerian_succ
#print axioms row_zero
#print axioms eulerian_one
#print axioms eulerian_two
#print axioms eulerian_coeff_zero

end ClusterGraphAudit.EulerianInsertion
