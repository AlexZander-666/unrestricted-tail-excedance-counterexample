import LongCycleBounds.BandRows

/-! Finite ordered support lengths and their cyclic reindexing. -/
noncomputable section

namespace LongCycleBounds.Band

open Finset

/-- The third length is determined by the first two. The pairs remain ordered. -/
def tripleWindow (j k : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc k (j-2*k)) ×ˢ (Icc k (j-2*k))).filter (fun v ↦ v.1+v.2 ≤ j-k)

@[simp] theorem mem_tripleWindow {j k a b : ℕ} :
    (a,b) ∈ tripleWindow j k ↔ k ≤ a ∧ k ≤ b ∧ a+b ≤ j-k := by
  simp only [tripleWindow, mem_filter, mem_product, mem_Icc]
  omega

/-- Interchange between the pair index and the nested interval sum. -/
theorem sum_tripleWindow {M : Type*} [AddCommMonoid M] (j k : ℕ) (f : ℕ × ℕ → M) :
    ∑ v ∈ tripleWindow j k, f v =
      ∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k), f (a,b) := by
  unfold tripleWindow
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro a ha
  rw [← sum_filter]
  congr 1
  ext b
  obtain ⟨a_low,a_high⟩ := mem_Icc.mp ha
  simp only [mem_filter,mem_Icc]
  omega

/-- Rotation replaces the first two coordinates by the second and third.
This is a reindexing of the entire finite sum, including its fixed points. -/
theorem sum_triple_rotate {M : Type*} [AddCommMonoid M] {j k : ℕ} (hk : 1 ≤ k)
    (f : ℕ × ℕ → M) :
    (∑ v ∈ tripleWindow j k, f (v.2,j-v.1-v.2)) = ∑ v ∈ tripleWindow j k, f v := by
  apply sum_bij' (fun v _ ↦ (v.2,j-v.1-v.2)) (fun v _ ↦ (j-v.1-v.2,v.1))
  · rintro ⟨a,b⟩ h
    simp only [mem_tripleWindow] at h ⊢
    omega
  · rintro ⟨a,b⟩ h
    simp only [mem_tripleWindow] at h ⊢
    omega
  · rintro ⟨a,b⟩ h
    simp only [mem_tripleWindow] at h
    apply Prod.ext
    · dsimp only
      omega
    · rfl
  · rintro ⟨a,b⟩ h
    simp only [mem_tripleWindow] at h
    apply Prod.ext
    · rfl
    · dsimp only
      omega
  · exact fun _ _ ↦ rfl

/-- The ordered-support multiplicity is invariant under cyclic relabelling. -/
theorem choose_triple_rotate {j a b c : ℕ} (hj : a+b+c=j) :
    j.choose b * (j-b).choose c = j.choose a * (j-a).choose b := by
  have support (u v w : ℕ) (h : u+v+w=j) :
      j.choose u * (j-u).choose v * (u.factorial*v.factorial*w.factorial) = j.factorial := by
    have first := Nat.choose_mul_factorial_mul_factorial (n := j) (k := u) (by omega)
    have next := Nat.choose_mul_factorial_mul_factorial (n := j-u) (k := v) (by omega)
    rw [show j-u-v=w by omega] at next
    calc
      _ = j.choose u * u.factorial * ((j-u).choose v*v.factorial*w.factorial) := by ring
      _ = _ := by rw [next, first]
  have h := support b c a (by omega)
  have h' := support a b c hj
  have eq : j.choose b * (j-b).choose c * (a.factorial*b.factorial*c.factorial) =
      j.choose a * (j-a).choose b * (a.factorial*b.factorial*c.factorial) := by
    convert h.trans h'.symm using 1
    ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) eq

#print axioms sum_tripleWindow
#print axioms sum_triple_rotate
#print axioms choose_triple_rotate

end LongCycleBounds.Band
