import LongCycleBounds.LinearTransfer
import LongCycleBounds.BandOuterMoments

/-! Differentiating the grouped original row and controlling its insertion boundary. -/
noncomputable section
namespace LongCycleBounds.Band
open Real Filter Set
open scoped Topology

private theorem shifted_transfer_hasSum {j k : ℕ} (hk : 2≤k) (lo : k≤j) (hi : j<3*k)
    (x : ℝ) (hx : 0<x) :
    HasSum (fun i : ℕ ↦ -((-1:ℝ)^i*Outer.weight (j-1) x i*transferWeight j k (i+1)))
      (normalizedEnumerator j k x) := by
  let f (l : ℕ) := (-exp (-x))^l*(l:ℝ)^(j-1)*transferWeight j k l
  have h : HasSum f (normalizedEnumerator j k x) := normalizedEnumerator_hasSum_transfer hk lo hi x hx
  have h0 : f 0=0 := by simp [f,zero_pow (by omega : j-1≠0)]
  have e : HasSum (fun i ↦ f (i+1)) (normalizedEnumerator j k x) := by
    simpa [h0] using (hasSum_nat_add_iff' 1).2 h
  apply e.congr_fun
  intro i
  simp only [f,Outer.weight,Nat.cast_add,Nat.cast_one]
  rw [show -exp (-x)=(-1)*exp (-x) by ring,mul_pow,pow_succ (-1:ℝ)]
  ring

/-- Positive array index i corresponds to label i+1, hence the sign change for the row. -/
theorem normalizedEnumerator_eq_shifted_transfer {j k : ℕ} (hk : 2≤k) (lo : k≤j) (hi : j<3*k)
    (x : ℝ) (hx : 0<x) : normalizedEnumerator j k x =
      -(∑' i : ℕ, (-1:ℝ)^i*Outer.weight (j-1) x i*transferWeight j k (i+1)) := by
  rw [← (shifted_transfer_hasSum hk lo hi x hx).tsum_eq,tsum_neg]

private theorem weight_hasDerivAt (N i : ℕ) (y : ℝ) :
    HasDerivAt (fun z ↦ Outer.weight N z i) (-Outer.weight (N+1) y i) y := by
  have he := ((hasDerivAt_id (𝕜:=ℝ) y).neg.exp.pow (i+1)).const_mul (((i:ℝ)+1)^N)
  apply he.congr_deriv
  simp only [Outer.weight, Pi.neg_apply, id_eq,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,
    pow_succ (exp (-y)) i,pow_succ ((i:ℝ)+1) N]
  ring

/-- Ordinary derivative, in the same zero-based array convention as Outer.mode. -/
theorem normalizedEnumerator_deriv_shifted_transfer {j k : ℕ} (hk : 2≤k) (lo : k≤j)
    (hi : j<3*k) (x : ℝ) (hx : 0<x) : deriv (normalizedEnumerator j k) x =
      ∑' i : ℕ, (-1:ℝ)^i*Outer.weight j x i*transferWeight j k (i+1) := by
  let g (i : ℕ) (y : ℝ) := -((-1:ℝ)^i*Outer.weight (j-1) y i*transferWeight j k (i+1))
  let g' (i : ℕ) (y : ℝ) := (-1:ℝ)^i*Outer.weight j y i*transferWeight j k (i+1)
  have localDeriv (i : ℕ) (y : ℝ) : HasDerivAt (g i) (g' i y) y := by
    have h := (((weight_hasDerivAt (j-1) i y).const_mul ((-1:ℝ)^i)).mul_const
      (transferWeight j k (i+1))).neg
    apply h.congr_deriv
    simp [g',show j-1+1=j by omega]
  have hhalf : 0<x/2 := by linarith
  have domain : x∈Ioi (x/2) := by exact show x/2<x by linarith
  have envelope := (Outer.summable_weight j (x/2) hhalf).mul_left (13/4 : ℝ)
  have bound (i : ℕ) (y : ℝ) (hy : y∈Ioi (x/2)) :
      ‖g' i y‖ ≤ (13/4)*Outer.weight j (x/2) i := by
    obtain ⟨hl,hu⟩ := transferWeight_bounds (j:=j) (k:=k) (l:=i+1) (by omega) lo hi.le (by omega)
    have hpos : 0≤transferWeight j k (i+1) := by linarith
    have hw : Outer.weight j y i ≤ Outer.weight j (x/2) i := by
      unfold Outer.weight
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (exp_pos _).le _ _
      exact exp_le_exp.mpr (neg_le_neg (le_of_lt hy))
    simp only [g',norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Real.norm_of_nonneg (Outer.weight_pos ..).le, Real.norm_of_nonneg hpos]
    rw [mul_comm (13/4:ℝ)]
    exact mul_le_mul hw hu hpos (Outer.weight_pos ..).le
  have h := hasDerivAt_tsum_of_isPreconnected envelope isOpen_Ioi isPreconnected_Ioi
    (fun i y _ ↦ localDeriv i y) bound domain (shifted_transfer_hasSum hk lo hi x hx).summable domain
  apply HasDerivAt.deriv
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx] with y hy
  exact (shifted_transfer_hasSum hk lo hi y hy).tsum_eq.symm

/-- Original signed insertion boundary. -/
def insertionBoundary (n k : ℕ) (x : ℝ) : ℝ :=
  (n-1).choose (k-1)*cycleMoment k x*cycleMoment (n-k) x

private theorem moment_neg_outer {a : ℕ} (ha : 1≤a) (x : ℝ) (hx : 0<x) :
    cycleMoment a x = -Outer.moment (a-1) x := by
  rw [cycleMoment,moment,outerMoment_eq_evaluation _ _ hx,show a-1+1=a by omega,sub_neg_eq_add]
  ring

/-- Comparison with the unweighted peak W, at every positive x satisfying the two
balanced-support size inequalities. -/
theorem insertionBoundary_mode_bound {n k : ℕ} (hk : 1≤k) (hn : k<n)
    (hA : 2*n≤5*(k-1)) (hB : 2*n≤5*(n-k-1)) (x : ℝ) (hx : 0<x) :
    |insertionBoundary n k x| * √(n:ℝ) ≤ 8*Outer.weight (n-2) x (Outer.mode (n-2) x hx) := by
  have h := mode_product (A:=k-1) (B:=n-k-1) (j:=n) (by omega) hA hB x hx
  rw [show k-1+1=k by omega] at h
  have hchoose : (n-1).choose (k-1) ≤ n.choose k := by
    have hp := Nat.choose_succ_succ (n-1) (k-1)
    simp only [Nat.succ_eq_add_one,show n-1+1=n by omega,show k-1+1=k by omega] at hp
    omega
  rw [insertionBoundary,moment_neg_outer hk x hx,moment_neg_outer (by omega) x hx,
    abs_mul,abs_mul,abs_neg,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
  have hcast : (((n-1).choose (k-1):ℕ):ℝ) ≤ (n.choose k:ℝ) := by exact_mod_cast hchoose
  have he := mul_le_mul_of_nonneg_right hcast (show 0 ≤ |Outer.moment (k-1) x| * |Outer.moment (n-k-1) x| by positivity)
  have ht := (mul_le_mul_of_nonneg_right he (sqrt_nonneg n)).trans h
  linarith only [ht]

/-- In the proposed linear-width range, the signed correction is too small to use up
two fifths of the unweighted mode. -/
theorem insertionBoundary_linear_small {n k d : ℕ} (hn : n=2*k+d) (hN : 10^6≤n)
    (width : 10000*d≤n) (x : ℝ) (hx : 0<x) :
    |insertionBoundary n k x| < 2/5*Outer.weight (n-2) x (Outer.mode (n-2) x hx) := by
  have h := insertionBoundary_mode_bound (n:=n) (k:=k) (by omega) (by omega) (by omega)
    (by omega) x hx
  have hs : (20:ℝ)<√(n:ℝ) := (lt_sqrt (by norm_num)).2 (by exact_mod_cast (by omega : 400<n))
  have hw := Outer.weight_pos (n-2) x (Outer.mode (n-2) x hx)
  by_contra! bad
  have contra := mul_lt_mul_of_pos_left hs (show 0 < |insertionBoundary n k x| by linarith)
  nlinarith

/-- The insertion identity transfers dominance of the actual derivative to the sign
of the actual successor. This algebraic implication holds at every real x. -/
theorem normalizedEnumerator_insertion_sign {n k : ℕ} (hk : 2≤k) (lo : 2*k≤n)
    (hi : n<3*k) (x : ℝ)
    (h : |insertionBoundary n k x| < |deriv (normalizedEnumerator (n-1) k) x|) :
    0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x) := by
  rw [normalizedEnumerator_insertion hk lo hi x]
  change 0 < (-deriv (normalizedEnumerator (n-1) k) x+insertionBoundary n k x)*
    (-deriv (normalizedEnumerator (n-1) k) x)
  rcases le_or_gt 0 (deriv (normalizedEnumerator (n-1) k) x) with hd|hd
  · rw [abs_of_nonneg hd] at h
    have left := le_abs_self (insertionBoundary n k x)
    have pos := (abs_nonneg _).trans_lt h
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · rw [abs_of_neg hd] at h
    have left := neg_abs_le (insertionBoundary n k x)
    exact mul_pos (by linarith) (by linarith)

#print axioms normalizedEnumerator_insertion_sign
#print axioms normalizedEnumerator_eq_shifted_transfer
#print axioms normalizedEnumerator_deriv_shifted_transfer
#print axioms insertionBoundary_mode_bound
#print axioms insertionBoundary_linear_small
end LongCycleBounds.Band
