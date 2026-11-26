import LongCycleBounds.BandMoments
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds

/-! A uniform local binomial bound from monotonicity of the Stirling remainder. -/
noncomputable section
namespace LongCycleBounds.Band
open Real

private def correction (n : ℕ) : ℝ := Stirling.stirlingSeq n * √2

private theorem correction_lower {n : ℕ} (hn : 0<n) : 2 ≤ correction n := by
  have h := mul_le_mul_of_nonneg_right (Stirling.sqrt_pi_le_stirlingSeq hn.ne') (sqrt_nonneg 2)
  change 2 ≤ Stirling.stirlingSeq n * √2
  apply le_trans _ h
  rw [← sqrt_mul (le_of_lt Real.pi_pos),Real.le_sqrt (by norm_num) (by positivity)]
  linarith [pi_gt_three]

private theorem correction_anti {a n : ℕ} (ha : 0<a) (han : a≤n) :
    correction n ≤ correction a := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  exact mul_le_mul_of_nonneg_right (Stirling.stirlingSeq'_antitone (show b ≤ m by omega)) (sqrt_nonneg 2)

private theorem factorial_unscaled {n : ℕ} (hn : 0<n) :
    (n.factorial:ℝ)*(exp 1)^n = correction n * √(n:ℝ)*(n:ℝ)^n := by
  unfold correction Stirling.stirlingSeq
  rw [sqrt_mul (by norm_num : 0≤(2:ℝ)),div_pow]
  field_simp

private theorem binomial_modal {A B M : ℕ} (hA : 0<A) (hB : 0<B) (hM : A+B=M) :
    2*√(A:ℝ)*√(B:ℝ)*(M.choose A:ℝ)*(A:ℝ)^A*(B:ℝ)^B ≤ √(M:ℝ)*(M:ℝ)^M := by
  have hc : (M.choose A:ℝ)*A.factorial*B.factorial = M.factorial := by
    exact_mod_cast (show M.choose A*A.factorial*B.factorial = M.factorial by
      simpa [show M-A=B by omega] using Nat.choose_mul_factorial_mul_factorial (show A≤M by omega))
  have id : (M.choose A:ℝ)*(correction A*√(A:ℝ)*(A:ℝ)^A)*(correction B*√(B:ℝ)*(B:ℝ)^B) =
      correction M*√(M:ℝ)*(M:ℝ)^M := by
    rw [← factorial_unscaled hA,← factorial_unscaled hB,← factorial_unscaled (show 0<M by omega),
      ← hM,pow_add]
    rw [hM]
    linear_combination ((exp 1)^A*(exp 1)^B)*hc
  have hleft := mul_le_mul_of_nonneg_right (correction_lower hB)
    (show 0 ≤ (M.choose A:ℝ)*√(A:ℝ)*(A:ℝ)^A*√(B:ℝ)*(B:ℝ)^B by positivity)
  have hright := mul_le_mul_of_nonneg_right (correction_anti hA (show A≤M by omega))
    (show 0 ≤ √(M:ℝ)*(M:ℝ)^M by positivity)
  have hcan : 0<correction A := lt_of_lt_of_le (by norm_num) (correction_lower hA)
  apply (mul_le_mul_iff_right₀ hcan).mp
  calc
    _ ≤ (M.choose A:ℝ)*(correction A*√(A:ℝ)*(A:ℝ)^A)*(correction B*√(B:ℝ)*(B:ℝ)^B) := by
      nlinarith only [mul_le_mul_of_nonneg_left hleft hcan.le]
    _ = _ := id
    _ ≤ _ := by linarith only [hright]

/-- Comparing the weighted product at u,v with its optimum at A:B. -/
private theorem weighted_product {A B M : ℕ} (hA : 0<A) (hB : 0<B) (hM : A+B=M)
    {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    u^A*v^B*(M:ℝ)^M ≤ (A:ℝ)^A*(B:ℝ)^B*(u+v)^M := by
  have hMr : (A:ℝ)+B=M := by exact_mod_cast hM
  have hMp : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  let z := ((M:ℝ)*u)/((A:ℝ)*(u+v))
  let w := ((M:ℝ)*v)/((B:ℝ)*(u+v))
  have hz : 0<z := by dsimp [z]; positivity
  have hw : 0<w := by dsimp [w]; positivity
  have hlin : (A:ℝ)*(z-1)+(B:ℝ)*(w-1)=0 := by dsimp [z,w]; field_simp; nlinarith [hMr]
  have hlog : log (z^A*w^B) ≤ log 1 := by
    rw [log_mul (by positivity) (by positivity),log_pow,log_pow,log_one]
    linarith [mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hz) (Nat.cast_nonneg A : 0≤(A:ℝ)),
      mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hw) (Nat.cast_nonneg B : 0≤(B:ℝ))]
  have hzw := (log_le_log_iff (by positivity) zero_lt_one).mp hlog
  dsimp [z,w] at hzw
  rw [div_pow,div_pow,mul_pow,mul_pow,mul_pow,mul_pow] at hzw
  field_simp at hzw
  rw [show (M:ℝ)^M=(M:ℝ)^A*(M:ℝ)^B by rw [← pow_add,hM],
    show (u+v)^M=(u+v)^A*(u+v)^B by rw [← pow_add,hM]]
  linarith only [hzw]

private theorem binomial_any {A B M : ℕ} (hA : 0<A) (hB : 0<B) (hM : A+B=M)
    {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    2*√(A:ℝ)*√(B:ℝ)*(M.choose A:ℝ)*(u^A*v^B) ≤ √(M:ℝ)*(u+v)^M := by
  have hMp : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have h1 := mul_le_mul_of_nonneg_left (weighted_product hA hB hM hu hv)
    (show 0 ≤ 2*√(A:ℝ)*√(B:ℝ)*(M.choose A:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right (binomial_modal hA hB hM)
    (show 0 ≤ (u+v)^M by positivity)
  apply (mul_le_mul_iff_left₀ (pow_pos hMp M)).mp
  linarith only [h1,h2]

private theorem choose_shift (A B : ℕ) :
    ((A+B+2).choose (A+1) : ℝ)*((A:ℝ)+1)*((B:ℝ)+1) =
      ((A:ℝ)+B+2)*((A:ℝ)+B+1)*((A+B).choose A:ℝ) := by
  have h := Nat.add_one_mul_choose_eq (A+B+1) A
  have h' := Nat.choose_mul_succ_eq (A+B) A
  rw [show A+B+1-A=B+1 by omega] at h'
  exact_mod_cast (show (A+B+2).choose (A+1)*(A+1)*(B+1) =
    (A+B+2)*(A+B+1)*(A+B).choose A by rw [← h]; nlinarith [h'])

/-- The ordered coefficient bound for balanced cycle sizes. Here A=a−1 and B=b−1.
The band forces 5A,5B≥2j, stronger than needed. This estimate is uniform over u,v>0. -/
theorem shifted_binomial_bound {A B j : ℕ} (hj : A+B+2=j)
    (hA : 2*j≤5*A) (hB : 2*j≤5*B) {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    (j.choose (A+1):ℝ)*(u^A*v^B)*√(j:ℝ) ≤ 8*(u+v)^(A+B) := by
  let M := A+B
  have hM : A+B=M := rfl
  have hJ : 0<(j:ℝ) := by exact_mod_cast (show 0<j by omega)
  have hAr : 2*(j:ℝ)≤5*A := by exact_mod_cast hA
  have hBr : 2*(j:ℝ)≤5*B := by exact_mod_cast hB
  have hbase := binomial_any (show 0<A by omega) (show 0<B by omega) hM hu hv
  have hden : 2*(j:ℝ)/5 ≤ √(A:ℝ)*√(B:ℝ) := by
    rw [← sqrt_mul (by positivity : 0≤(A:ℝ)),le_sqrt (by positivity) (by positivity)]
    nlinarith only [mul_le_mul (show 2*(j:ℝ)/5≤A by linarith) (show 2*(j:ℝ)/5≤B by linarith)
      (by positivity : 0≤2*(j:ℝ)/5) (Nat.cast_nonneg A : (0:ℝ)≤A)]
  have hrt : √(M:ℝ) ≤ √(j:ℝ) := sqrt_le_sqrt (by exact_mod_cast (show M≤j by omega))
  have msmall : (M.choose A:ℝ)*(u^A*v^B)*√(j:ℝ) ≤ (5/4:ℝ)*(u+v)^M := by
    apply (mul_le_mul_iff_left₀ (sqrt_pos.mpr hJ)).mp
    have h1 := mul_le_mul_of_nonneg_right hden (show 0≤(M.choose A:ℝ)*(u^A*v^B) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hrt (show 0≤(u+v)^M by positivity)
    have h3 := sq_sqrt hJ.le
    rw [mul_assoc _ (√(j:ℝ)) (√(j:ℝ)),← sq,h3]
    linarith only [h1,h2,hbase]
  have hc : (j.choose (A+1):ℝ)*((A:ℝ)+1)*((B:ℝ)+1)=
      (j:ℝ)*((j:ℝ)-1)*(M.choose A:ℝ) := by
    subst j
    push_cast
    convert choose_shift A B using 1; ring
  have hmul : (j:ℝ)^2 ≤ (25/4:ℝ)*((A:ℝ)+1)*((B:ℝ)+1) := by
    nlinarith only [mul_le_mul (show (j:ℝ)≤5/2*((A:ℝ)+1) by linarith)
      (show (j:ℝ)≤5/2*((B:ℝ)+1) by linarith) hJ.le
      (show 0≤5/2*((A:ℝ)+1) by positivity)]
  have hchoose : (j.choose (A+1):ℝ) ≤ (25/4:ℝ)*(M.choose A:ℝ) := by
    apply (mul_le_mul_iff_left₀ (show 0<((A:ℝ)+1)*((B:ℝ)+1) by positivity)).mp
    nlinarith only [hc,mul_le_mul_of_nonneg_right hmul (Nat.cast_nonneg (M.choose A) : (0:ℝ)≤_),
      mul_nonneg hJ.le (Nat.cast_nonneg (M.choose A) : (0:ℝ)≤_)]
  have last := mul_le_mul_of_nonneg_right hchoose
    (show 0≤u^A*v^B*√(j:ℝ) by positivity)
  change _ ≤ 8*(u+v)^M
  linarith only [last,msmall,show 0≤(u+v)^M by positivity]

#print axioms shifted_binomial_bound
end LongCycleBounds.Band
