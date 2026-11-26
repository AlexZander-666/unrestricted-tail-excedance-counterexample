import LongCycleBounds.UniversalShortBranch

/-! The Rakotoson--Rakotondrajao insertion recurrence on arbitrary original rows. -/
noncomputable section
namespace LongCycleBounds.Insertion
open LongCycles Finset Equiv Polynomial
open scoped Classical

private theorem sum_subtype_ite {A : Type*} [Fintype A] (q : A → Prop)
    [Fintype {a // q a}] (f : A → ℝ[X]) :
    (∑ a : {a // q a}, f a.val) = ∑ a, if q a then f a else 0 := by
  rw [← sum_filter]
  symm
  apply Finset.sum_subtype
  simp

/-- Partition the actual row by whether the orbit of its greatest letter has
minimum permitted length or is strictly longer. -/
theorem partition_max (n k : ℕ) :
    enumerator (n+1) k =
      (∑ τ : LongBranch n k, (X:ℝ[X])^excedances τ.val) +
      (∑ τ : ShortBranch (Fin.last n) k, (X:ℝ[X])^excedances τ.val) := by
  let f (τ : Perm (Fin (n+1))) := (X:ℝ[X])^excedances τ
  rw [sum_subtype_ite (fun τ : Perm (Fin (n+1)) ↦ Allowed k τ ∧ k<lengthAt τ (Fin.last n)) f,
    sum_subtype_ite (fun τ : Perm (Fin (n+1)) ↦ Allowed k τ ∧ lengthAt τ (Fin.last n)=k) f,
    ← sum_add_distrib]
  unfold enumerator
  apply sum_congr rfl
  intro τ _
  by_cases allowed : Allowed k τ
  · have lower := (allowed_iff_lengthAt τ).mp allowed (Fin.last n)
    rcases lt_or_eq_of_le lower with lt|eq
    · simp [allowed,lt,lt.ne',f]
    · simp [eq,f]
  · simp [allowed]

/-- Published polynomial recurrence, with n the lower row index. -/
theorem enumerator_succ {n k : ℕ} (hk : 2 ≤ k) :
    enumerator (n+1) k =
      C (n:ℝ)*X*enumerator n k + X*(1-X)*derivative (enumerator n k) +
      C (n.choose (k-1):ℝ)*(X*eulerian (k-1))*enumerator (n+1-k) k := by
  rw [partition_max,longBranch_weight (by omega),shortBranch_weight _ hk,Nat.add_one_sub_one]

open LongCycleBounds.Band

/-- Differentiation in logarithmic coordinates, including x=0. -/
theorem universal_hasDerivAt {n k : ℕ} (hk : 2≤k) (hn : k≤n+1) (x : ℝ) :
    HasDerivAt (normalizedEnumerator n k)
      ((n.choose (k-1):ℝ)*cycleMoment k x*normalizedEnumerator (n+1-k) k x -
        normalizedEnumerator (n+1) k x) x := by
  let t := -Real.exp (-x)
  let b := 1-t
  have hb : b ≠ 0 := by dsimp [b,t]; linarith [Real.exp_pos (-x)]
  have dt : HasDerivAt (fun y : ℝ ↦ -Real.exp (-y)) (-t) x :=
    (((hasDerivAt_id x).neg.exp).neg).congr_deriv (by simp [t])
  have base := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
  have deriv := ((enumerator n k).hasDerivAt t).div (base.pow n) (pow_ne_zero _ hb)
  apply (deriv.comp x dt).congr_deriv
  simp only [id_eq,Pi.sub_apply,Pi.pow_apply,zero_sub]
  unfold normalizedEnumerator cycleMoment moment
  change _ = (n.choose (k-1):ℝ)*(t*(eulerian (k-1)).eval t/b^k)*
    ((enumerator (n+1-k) k).eval t/b^(n+1-k))-(enumerator (n+1) k).eval t/b^(n+1)
  rw [enumerator_succ hk]
  simp only [eval_add,eval_mul,eval_sub,eval_C,eval_X,eval_one]
  change (((derivative (enumerator n k)).eval t*b^n - (enumerator n k).eval t *
      ((n:ℝ)*b^(n-1)*(-1)))/(b^n)^2)*(-t) = _
  have np : 1≤n := by omega
  have one : b^n=b^(n-1)*b := by rw [←pow_succ, Nat.sub_add_cancel np]
  have split : b^k*b^(n+1-k)=b^(n+1) := by rw [←pow_add]; congr 1; omega
  let A := (eulerian (k-1)).eval t
  let Q := (enumerator (n+1-k) k).eval t
  let P := (enumerator n k).eval t
  let P' := (derivative (enumerator n k)).eval t
  let c : ℝ := n.choose (k-1)
  change ((P'*b^n-P*((n:ℝ)*b^(n-1)*(-1)))/(b^n)^2)*(-t) =
    c*(t*A/b^k)*(Q/b^(n+1-k)) - ((n:ℝ)*t*P+t*b*P'+c*(t*A)*Q)/b^(n+1)
  have combine : c*(t*A/b^k)*(Q/b^(n+1-k)) = c*(t*A)*Q/b^(n+1) := by
    rw [←split]; ring
  rw [combine,pow_succ b n,one]
  field_simp [hb]
  ring

/-- Universal normalized recurrence for the true excedance enumerators. -/
theorem universal_normalized_insertion {n k : ℕ} (hk : 2≤k) (hn : k<n) (x : ℝ) :
    normalizedEnumerator n k x = -deriv (normalizedEnumerator (n-1) k) x +
      ((n-1).choose (k-1):ℝ)*cycleMoment k x*normalizedEnumerator (n-k) k x := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [Nat.succ_sub_one,(universal_hasDerivAt hk (by omega) x).deriv]
  ring

#print axioms enumerator_succ
#print axioms universal_normalized_insertion
end LongCycleBounds.Insertion
