import LongCycleBounds.InsertionBoundary

/-! Inserting the maximum into an arrow of an actual permutation. -/
noncomputable section
namespace LongCycleBounds.Insertion
open LongCycles Equiv Finset

private def predecessor {n : ℕ} :
    Option (Fin n) × Perm (Fin n) ≃ Option (Fin n) × Perm (Fin n) where
  toFun u := (u.2.symm.optionCongr u.1,u.2)
  invFun u := (u.2.optionCongr u.1,u.2)
  left_inv := by rintro ⟨a,f⟩; simp [optionCongr_symm]
  right_inv := by
    rintro ⟨a,f⟩
    change (f.symm.optionCongr (f.optionCongr a), f) = _
    rw [optionCongr_symm, Equiv.symm_apply_apply]

/-- Delete the largest letter, recording its predecessor; none means it was fixed. -/
def deleteMax {n : ℕ} : Perm (Fin (n+1)) ≃ Option (Fin n) × Perm (Fin n) :=
  (finSuccEquivLast.permCongr.trans Perm.decomposeOption).trans predecessor

/-- Replace the old arrow from i to its image with a path through the new maximum. -/
def insertAfter {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : Perm (Fin (n+1)) :=
  deleteMax.symm (some i,σ)

@[simp] theorem deleteMax_insertAfter {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    deleteMax (insertAfter σ i) = (some i,σ) := deleteMax.apply_symm_apply _

private theorem insert_formula {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) (j : Fin (n+1)) :
    insertAfter σ i j = finSuccEquivLast.symm
      ((swap none (some (σ i)) * σ.optionCongr) (finSuccEquivLast j)) := rfl

@[simp] theorem insert_last {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    insertAfter σ i (Fin.last n) = (σ i).castSucc := by
  simp [insert_formula]

@[simp] theorem insert_source {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    insertAfter σ i i.castSucc = Fin.last n := by simp [insert_formula]

theorem insert_other {n : ℕ} (σ : Perm (Fin n)) {i j : Fin n} (h : j ≠ i) :
    insertAfter σ i j.castSucc = (σ j).castSucc := by
  simp [insert_formula, Equiv.swap_apply_def,h]

/-- The greatest label contributes no excedance, and exactly one old position can change. -/
theorem excedances_insertAfter {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    excedances (insertAfter σ i) = excedances σ + if i < σ i then 0 else 1 := by
  simp only [excedances,Finset.card_filter,Fin.sum_univ_castSucc,insert_last,
    not_lt_of_ge (Fin.le_last _),if_false,add_zero]
  have ea (j : Fin n) : (if j.castSucc < insertAfter σ i j.castSucc then 1 else 0) =
      (if j < σ j then 1 else 0) + (if j=i then (if i<σ i then 0 else 1) else 0) := by
    by_cases h : j=i
    · subst j; simp [Fin.castSucc_lt_last]; split <;> rfl
    · simp [h, insert_other σ h]
  simp_rw [ea]
  simp [Finset.sum_add_distrib]

/-- First positive return time, including fixed points. -/
def lengthAt {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) := Function.minimalPeriod σ i

theorem lengthAt_pos {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : 0 < lengthAt σ i :=
  Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts i)

theorem pow_lengthAt {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : (σ ^ lengthAt σ i) i = i := by
  rw [←Perm.iterate_eq_pow]
  exact Function.isPeriodicPt_minimalPeriod σ i

theorem lengthAt_le_return {n h : ℕ} (σ : Perm (Fin n)) (i : Fin n) (hh : 0<h)
    (he : (σ^h) i=i) : lengthAt σ i ≤ h :=
  Function.IsPeriodicPt.minimalPeriod_le hh (by
    change (σ : Fin n → Fin n)^[h] i = i
    rwa [Perm.iterate_eq_pow])

theorem allowed_iff_lengthAt {n k : ℕ} (σ : Perm (Fin n)) :
    Allowed k σ ↔ ∀ i, k ≤ lengthAt σ i := by
  constructor
  · intro ok i
    by_contra! h
    exact ok i _ (lengthAt_pos σ i) h (pow_lengthAt σ i)
  · intro lower i h hp small ret
    exact (Nat.not_lt_of_ge ((lower i).trans (lengthAt_le_return σ i hp ret))) small

theorem lengthAt_pow {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) (h : ℕ) :
    lengthAt σ ((σ^h) i) = lengthAt σ i := by
  rw [←Perm.iterate_eq_pow]
  exact Function.minimalPeriod_apply_iterate (σ.injective.mem_periodicPts i) h

private theorem max_walk {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) {h : ℕ}
    (hpos : 0<h) (hlim : h ≤ lengthAt σ i) :
    (insertAfter σ i ^ h) (Fin.last n) = ((σ ^ h) i).castSucc := by
  induction h with
  | zero => omega
  | succ h ih =>
    by_cases hz : h=0
    · subst h; simp
    · have ne : (σ^h) i ≠ i := fun e ↦ by
        have := lengthAt_le_return σ i (by omega) e
        omega
      rw [pow_succ', Perm.mul_apply, ih (by omega) (by omega), insert_other σ ne,
        pow_succ', Perm.mul_apply]

/-- The orbit containing the new maximum has one more element than the selected old orbit. -/
theorem lengthAt_insert_last {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    lengthAt (insertAfter σ i) (Fin.last n) = lengthAt σ i + 1 := by
  have ret : (insertAfter σ i ^ (lengthAt σ i+1)) (Fin.last n) = Fin.last n := by
    rw [pow_succ',Perm.mul_apply,max_walk σ i (lengthAt_pos _ _) le_rfl,pow_lengthAt,insert_source]
  apply le_antisymm (lengthAt_le_return _ _ (by omega) ret)
  by_contra! early
  have walk := max_walk σ i (lengthAt_pos (insertAfter σ i) (Fin.last n)) (by omega)
  rw [pow_lengthAt] at walk
  exact (Fin.castSucc_ne_last _) walk.symm

private theorem positive_visit {n : ℕ} (σ : Perm (Fin n)) {i j : Fin n}
    (hj : σ.SameCycle i j) :
    ∃ h, 0<h ∧ h ≤ lengthAt σ i ∧ (σ^h) i=j := by
  obtain ⟨u,hu⟩ := hj.exists_nat_pow_eq
  have e : (σ^(u % lengthAt σ i)) i =j := by
    rw [←hu, ← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow]
    exact Function.iterate_mod_minimalPeriod_eq
  by_cases z : u % lengthAt σ i = 0
  · simp only [z,pow_zero,Perm.one_apply] at e
    exact ⟨_,lengthAt_pos _ _,le_rfl,(pow_lengthAt _ _).trans e⟩
  · exact ⟨_,Nat.pos_of_ne_zero z,(Nat.mod_lt _ (lengthAt_pos _ _)).le,e⟩

private theorem outside_walk {n : ℕ} (σ : Perm (Fin n)) {i j : Fin n}
    (different : ¬σ.SameCycle i j) (h : ℕ) :
    (insertAfter σ i ^ h) j.castSucc = ((σ^h) j).castSucc := by
  induction h with
  | zero => simp
  | succ h ih =>
    have ne : (σ^h) j ≠ i := by
      intro e
      apply different
      rw [←e]
      exact (Perm.SameCycle.refl σ j).pow_left
    rw [pow_succ',Perm.mul_apply,ih,insert_other σ ne,pow_succ',Perm.mul_apply]

/-- All old orbits are preserved; exactly the selected orbit grows by one. -/
theorem lengthAt_insert_castSucc {n : ℕ} (σ : Perm (Fin n)) (i j : Fin n) :
    lengthAt (insertAfter σ i) j.castSucc =
      lengthAt σ j + if σ.SameCycle i j then 1 else 0 := by
  classical
  by_cases a : σ.SameCycle i j
  · rw [if_pos a]
    obtain ⟨h,hp,hl,he⟩ := positive_visit σ a
    have eq := max_walk σ i hp hl
    rw [he] at eq
    calc
      _ = lengthAt (insertAfter σ i) (Fin.last n) := by
        rw [←eq,lengthAt_pow]
      _ = lengthAt σ i+1 := lengthAt_insert_last _ _
      _ = _ := by rw [←he,lengthAt_pow]
  · rw [if_neg a,add_zero]
    have same (h : ℕ) : (insertAfter σ i^h) j.castSucc = j.castSucc ↔ (σ^h) j=j := by
      rw [outside_walk σ a]; simp
    exact le_antisymm (lengthAt_le_return _ _ (lengthAt_pos _ _) ((same _).mpr (pow_lengthAt _ _)))
      (lengthAt_le_return _ _ (lengthAt_pos _ _) ((same _).mp (pow_lengthAt _ _)))

/-- Deletion of the maximum preserves admissibility exactly on the long-cycle branch. -/
theorem allowed_insert_long_iff {n k : ℕ} (σ : Perm (Fin n)) (i : Fin n) :
    (Allowed k (insertAfter σ i) ∧ k < lengthAt (insertAfter σ i) (Fin.last n)) ↔
      Allowed k σ := by
  classical
  rw [allowed_iff_lengthAt,allowed_iff_lengthAt,lengthAt_insert_last]
  constructor
  · rintro ⟨all,long⟩ j
    by_cases a : σ.SameCycle i j
    · obtain ⟨h,_,_,he⟩ := positive_visit σ a
      rw [←he,lengthAt_pow]; omega
    · have h := all j.castSucc
      simpa [lengthAt_insert_castSucc,a] using h
  · intro ok
    constructor
    · refine Fin.lastCases ?_ (fun j ↦ ?_)
      · rw [lengthAt_insert_last]; exact le_trans (ok i) (Nat.le_succ _)
      · rw [lengthAt_insert_castSucc]; exact (ok j).trans (Nat.le_add_right _ _)
    · exact Nat.lt_succ_of_le (ok i)

abbrev Admissible (n k : ℕ) := {σ : Perm (Fin n) // Allowed k σ}

abbrev LongBranch (n k : ℕ) := {τ : Perm (Fin (n+1)) //
    Allowed k τ ∧ k < lengthAt τ (Fin.last n)}

instance (n k : ℕ) : Fintype (Admissible n k) := Fintype.ofFinite _
instance (n k : ℕ) : Fintype (LongBranch n k) := Fintype.ofFinite _

/-- The full long branch is in bijection with every admissible predecessor and each old arrow. -/
def longBranchEquiv {n k : ℕ} (hk : 1≤k) :
    Admissible n k × Fin n ≃ LongBranch n k := by
  let f (u : Admissible n k × Fin n) : LongBranch n k :=
    ⟨insertAfter u.1.val u.2,(allowed_insert_long_iff _ _).2 u.1.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨⟨σ,hs⟩,i⟩ ⟨⟨τ,ht⟩,j⟩ e
    have h := congrArg (fun a : LongBranch n k ↦ deleteMax a.val) e
    change deleteMax (insertAfter σ i) = deleteMax (insertAfter τ j) at h
    simpa [and_comm] using h
  · rintro ⟨τ,hτ⟩
    obtain ⟨⟨a,σ⟩,he⟩ := deleteMax.symm.surjective τ
    cases a with
    | none =>
      have fixed : τ (Fin.last n)=Fin.last n := by
        rw [←he]
        change finSuccEquivLast.symm ((swap none none * σ.optionCongr : Perm (Option (Fin n)))
            (finSuccEquivLast (Fin.last n)))=_
        simp
      have lim := lengthAt_le_return τ (Fin.last n) (by decide : 0<1) (by simpa using fixed)
      omega
    | some i =>
      change insertAfter σ i=τ at he
      refine ⟨(⟨σ,(allowed_insert_long_iff σ i).1 (he ▸ hτ)⟩,i),?_⟩
      exact Subtype.ext he

@[simp] theorem longBranchEquiv_apply {n k : ℕ} (hk : 1≤k) (u : Admissible n k × Fin n) :
    (longBranchEquiv hk u).val = insertAfter u.1.val u.2 := rfl

open Polynomial

theorem insertion_weight {n : ℕ} (σ : Perm (Fin n)) :
    (∑ i, (X : Polynomial ℝ)^excedances (insertAfter σ i)) =
      C (n:ℝ)*X*X^excedances σ + X*(1-X)*derivative (X^excedances σ) := by
  classical
  let a := (univ : Finset (Fin n)).filter (fun i ↦ i<σ i)
  let b := (univ : Finset (Fin n)).filter (fun i ↦ ¬i<σ i)
  let d := excedances σ
  have ha : a.card=d := rfl
  have hab : a.card+b.card=n := by simpa [a,b] using
    (card_filter_add_card_filter_not (s:=univ) (fun i : Fin n ↦ i<σ i))
  have count : (n:ℝ) = (d:ℝ)+(b.card:ℝ) := by exact_mod_cast (show n=d+b.card by omega)
  have elem (i : Fin n) : (X:Polynomial ℝ)^excedances (insertAfter σ i) =
      if i<σ i then X^d else X^d*X := by
    rw [excedances_insertAfter]; by_cases h : i<σ i <;> simp [h,d,pow_succ]
  simp_rw [elem]
  rw [sum_ite]
  change (∑ _ ∈ a, (X:Polynomial ℝ)^d)+(∑ _ ∈ b, X^d*X)=_
  rw [sum_const,sum_const,ha]
  change d • (X:Polynomial ℝ)^d + b.card • (X^d*X) =
    C (n:ℝ)*X*X^d+X*(1-X)*derivative (X^d)
  rw [derivative_X_pow,count,map_add]
  simp only [nsmul_eq_mul,map_natCast]
  cases d with
  | zero => simp
  | succ d => simp only [Nat.succ_sub_one,pow_succ,Nat.cast_succ]; ring

theorem enumerator_eq_admissible_sum (n k : ℕ) :
    enumerator n k = ∑ σ : Admissible n k, (X:Polynomial ℝ)^excedances σ.val := by
  classical
  unfold enumerator
  rw [←sum_filter]
  apply Finset.sum_subtype
  simp

/-- The two differential summands of the published recurrence on arbitrary rows. -/
theorem longBranch_weight {n k : ℕ} (hk : 1≤k) :
    (∑ τ : LongBranch n k, (X:Polynomial ℝ)^excedances τ.val) =
      C (n:ℝ)*X*enumerator n k + X*(1-X)*derivative (enumerator n k) := by
  rw [← (longBranchEquiv (n:=n) hk).sum_comp (fun τ ↦ (X:Polynomial ℝ)^excedances τ.val),
    Fintype.sum_prod_type,enumerator_eq_admissible_sum,derivative_sum,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro σ _
  exact insertion_weight σ.val

#print axioms longBranch_weight
#print axioms allowed_insert_long_iff
end LongCycleBounds.Insertion
