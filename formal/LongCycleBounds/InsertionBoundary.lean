import LongCycleBounds.BandMoments

/-! The insertion recurrence in normalized real coordinates, including the first split. -/
noncomputable section
namespace LongCycleBounds.Band
open LongCycles Polynomial Finset

/-- The real alternating moment indexed by cycle size, evaluated at t = -exp(-x). -/
def cycleMoment (a : ℕ) (x : ℝ) : ℝ := moment a (-Real.exp (-x))

/-- A rational-function proof, valid on the entire real axis. -/
theorem cycleMoment_hasDerivAt {a : ℕ} (ha : 1≤a) (x : ℝ) :
    HasDerivAt (cycleMoment a) (-cycleMoment (a+1) x) x := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  let t := -Real.exp (-x)
  have ht : 1-t ≠ 0 := by dsimp [t]; linarith [Real.exp_pos (-x)]
  have did := hasDerivAt_id (𝕜 := ℝ) t
  have db := (hasDerivAt_const t (1:ℝ)).sub did
  have rat := (did.mul ((eulerian m).hasDerivAt t)).div (db.pow (m+1)) (pow_ne_zero _ ht)
  have dt : HasDerivAt (fun y : ℝ ↦ -Real.exp (-y)) (-t) x := by
    exact (((hasDerivAt_id x).neg.exp).neg).congr_deriv (by simp [t])
  apply (rat.comp x dt).congr_deriv
  · change _ = - (t*(eulerian (m+1)).eval t/(1-t)^((m+1)+1))
    rw [longEulerian_succ]
    simp only [eval_add,eval_mul,eval_sub,eval_C,eval_X,eval_one,id_eq,
      Nat.cast_add,Nat.cast_one,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Nat.succ_sub_one]
    rw [pow_succ (1-t) (m+1),pow_succ (1-t) m]
    field_simp
    ring

private theorem reflectIcc (f : ℕ → ℝ) (n k : ℕ) (hk : k≤n) :
    ∑ a ∈ Icc k (n-k), f (n-a) = ∑ a ∈ Icc k (n-k), f a := by
  apply sum_bij' (fun a _ ↦ n-a) (fun a _ ↦ n-a)
  all_goals intros a ha; obtain ⟨_,_⟩ := mem_Icc.mp ha
  all_goals first | exact mem_Icc.mpr ⟨by omega,by omega⟩ | congr 1 <;> omega

private def pairSum (n k : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc k (n-k), (n.choose a : ℝ)*f a*f (n-a)

/-- Pascal's rule, folded by reflection before extracting the last endpoint. -/
private theorem pairSum_next {p k : ℕ} (hk : 1≤k) (hp : 2*k≤p+1) (f : ℕ → ℝ) :
    pairSum (p+1) k f =
      2 * (∑ a ∈ Icc k (p-k), (p.choose a : ℝ)*f a*f (p-a+1)) +
      2 * (p.choose (k-1) : ℝ)*f k*f (p+1-k) := by
  let B (a : ℕ) := (p.choose a : ℝ)*f a*f (p+1-a)
  have term (a : ℕ) (ha : a∈Icc k (p+1-k)) :
      ((p+1).choose a : ℝ)*f a*f (p+1-a) = B (p+1-a)+B a := by
    obtain ⟨hal,har⟩ := mem_Icc.mp ha
    have he : p+1-(p+1-a)=a := by omega
    have hc : p.choose (p+1-a) = p.choose (a-1) := by
      rw [show p+1-a=p-(a-1) by omega,Nat.choose_symm (by omega)]
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
    simp only [B,he,hc,Nat.succ_sub_one,Nat.choose_succ_succ,Nat.cast_add]
    ring
  unfold pairSum
  rw [sum_congr rfl term,sum_add_distrib,reflectIcc B _ _ (by omega),← two_mul]
  have he : p+1-k=p-k+1 := by omega
  rw [he, sum_Icc_succ_top (by omega : k≤p-k+1)]
  have inner : ∑ a ∈ Icc k (p-k), B a =
      ∑ a ∈ Icc k (p-k), (p.choose a : ℝ)*f a*f (p-a+1) := by
    apply sum_congr rfl
    intro a ha
    have := (mem_Icc.mp ha).2
    simp only [B,show p+1-a=p-a+1 by omega]
  have hc : p.choose (p-k+1)=p.choose (k-1) := by
    rw [show p-k+1=p-(k-1) by omega,Nat.choose_symm (by omega)]
  rw [inner]
  simp only [B,hc,show p+1-(p-k+1)=k by omega]
  ring

private theorem pairSum_hasDerivAt {p k : ℕ} (hk : 1≤k) (hpk : k≤p) (x : ℝ) :
    HasDerivAt (fun y ↦ pairSum p k (fun a ↦ cycleMoment a y))
      (-(2 * ∑ a ∈ Icc k (p-k), (p.choose a : ℝ)*cycleMoment a x*cycleMoment (p-a+1) x)) x := by
  let f (a : ℕ) := cycleMoment a x
  let B (a : ℕ) := (p.choose a : ℝ)*f a*f (p-a+1)
  have hterm (a : ℕ) (ha : a∈Icc k (p-k)) :
      HasDerivAt (fun y ↦ (p.choose a : ℝ)*cycleMoment a y*cycleMoment (p-a) y)
        (-(B (p-a)+B a)) x := by
    obtain ⟨hal,har⟩ := mem_Icc.mp ha
    have hd := ((cycleMoment_hasDerivAt (a:=a) (by omega) x).const_mul (p.choose a : ℝ)).mul
      (cycleMoment_hasDerivAt (a:=p-a) (by omega) x)
    apply hd.congr_deriv
    simp only [B,f,Nat.choose_symm (show a≤p by omega),show p-(p-a)=a by omega]
    ring
  have h := HasDerivAt.fun_sum hterm
  apply h.congr_deriv
  change _ = -(2* ∑ a ∈ Icc k (p-k), B a)
  rw [sum_neg_distrib,sum_add_distrib,reflectIcc B p k hpk,two_mul]

/-- The original permutation enumerator with the insertion denominator. -/
def normalizedEnumerator (n k : ℕ) (x : ℝ) : ℝ :=
  let t := -Real.exp (-x)
  (enumerator n k).eval t / (1-t)^n

private theorem normalized_eq {n k : ℕ} (hk : 2≤k) (lo : k≤n) (hi : n<3*k) (x : ℝ) :
    normalizedEnumerator n k x = cycleMoment n x +
      1/2 * pairSum n k (fun a ↦ cycleMoment a x) := by
  dsimp only [normalizedEnumerator]
  rw [actual_band_row hk lo hi, eval_mul, eval_X, deformed_eval]
  · rfl
  · exact ne_of_lt (by linarith [Real.exp_pos (-x)])

/-- At every real x, including zero, the derivative of the preceding actual row equals
the boundary correction minus the next actual row. -/
theorem normalizedEnumerator_hasDerivAt {n k : ℕ} (hk : 2≤k) (lo : 2*k≤n) (hi : n<3*k)
    (x : ℝ) : HasDerivAt (normalizedEnumerator (n-1) k)
      ((n-1).choose (k-1)*cycleMoment k x*cycleMoment (n-k) x-normalizedEnumerator n k x) x := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simp only [Nat.succ_sub_one]
  have h := (cycleMoment_hasDerivAt (a:=p) (by omega) x).add
    ((pairSum_hasDerivAt (p:=p) (k:=k) (by omega) (by omega) x).const_mul (1/2 : ℝ))
  rw [show normalizedEnumerator p k = (fun y ↦ cycleMoment p y + 1/2 * pairSum p k (fun a ↦ cycleMoment a y)) from funext (normalized_eq hk (by omega) (by omega))]
  apply h.congr_deriv
  · rw [normalized_eq hk (by omega) hi,pairSum_next (by omega) lo]
    ring

/-- The published insertion boundary, normalized on the full two-cycle range. -/
theorem normalizedEnumerator_insertion {n k : ℕ} (hk : 2≤k) (lo : 2*k≤n) (hi : n<3*k)
    (x : ℝ) : normalizedEnumerator n k x =
      -deriv (normalizedEnumerator (n-1) k) x +
        (n-1).choose (k-1)*cycleMoment k x*cycleMoment (n-k) x := by
  rw [(normalizedEnumerator_hasDerivAt hk lo hi x).deriv]
  ring

/-- Below the first split the sum over ordered supports is empty. -/
theorem normalizedEnumerator_beforeSplit {n k : ℕ} (hk : 2≤k) (lo : k≤n) (hi : n<2*k) :
    normalizedEnumerator n k = cycleMoment n := by
  funext x
  rw [normalized_eq hk lo (by omega)]
  simp [pairSum, Icc_eq_empty_of_lt (show n-k<k by omega)]

/-- The same pair of adjacent original rows before the first split has no boundary correction. -/
theorem normalizedEnumerator_insertion_beforeSplit {n k : ℕ} (hk : 2≤k) (lo : k<n)
    (hi : n<2*k) (x : ℝ) : normalizedEnumerator n k x =
      -deriv (normalizedEnumerator (n-1) k) x := by
  rw [normalizedEnumerator_beforeSplit hk (by omega) hi,
      normalizedEnumerator_beforeSplit hk (by omega) (show n-1<2*k by omega),
      (cycleMoment_hasDerivAt (a:=n-1) (by omega) x).deriv, neg_neg,
      show n-1+1=n by omega]

/-- At 2k the two equal-size missing ends of Pascal's rule give one correction. -/
theorem normalizedEnumerator_firstSplit (k : ℕ) (hk : 2≤k) (x : ℝ) :
    normalizedEnumerator (2*k) k x = -deriv (normalizedEnumerator (2*k-1) k) x +
      (2*k-1).choose (k-1)*(cycleMoment k x)^2 := by
  rw [normalizedEnumerator_insertion hk (le_refl _) (by omega : 2*k<3*k) x,
      show 2*k-k=k by omega]
  ring

#print axioms normalizedEnumerator_firstSplit
#print axioms normalizedEnumerator_insertion_beforeSplit
#print axioms cycleMoment_hasDerivAt
#print axioms normalizedEnumerator_hasDerivAt
#print axioms normalizedEnumerator_insertion

end LongCycleBounds.Band
