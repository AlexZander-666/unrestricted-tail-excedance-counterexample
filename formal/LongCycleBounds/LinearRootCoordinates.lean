import LongCycleBounds.LinearOuterBridge
import LongCycleBounds.BandShape
noncomputable section
namespace LongCycleBounds.Band
open Polynomial Real LongCycles

/-- At a root, the numerator of the differentiated rational row is the only contribution. -/
theorem normalized_deriv_at_original_root {p k : ℕ} (x : ℝ)
    (hz : (enumerator p k).eval (-exp (-x))=0) :
    deriv (normalizedEnumerator p k) x =
      exp (-x)*(enumerator p k).derivative.eval (-exp (-x))/(1+exp (-x))^p := by
  have dt : HasDerivAt (fun y : ℝ ↦ -exp (-y)) (exp (-x)) x :=
    (((hasDerivAt_id x).neg.exp).neg).congr_deriv (by simp)
  have h := (((enumerator p k).hasDerivAt (-exp (-x))).comp x dt).div
    (((hasDerivAt_const x (1:ℝ)).sub dt).pow p) (by
      change (1- -exp (-x))^p ≠ 0
      rw [sub_neg_eq_add]
      positivity)
  apply HasDerivAt.deriv
  apply h.congr_deriv
  change (_ * exp (-x) * (1- -exp (-x))^p - (enumerator p k).eval (-exp (-x))*_) /
    ((1- -exp (-x))^p)^2 = _
  rw [hz,zero_mul,sub_zero,sub_neg_eq_add]
  field_simp

/-- Differentiation of a reciprocal polynomial at a real root, without negative powers. -/
theorem reciprocal_derivative_at_root (P : ℝ[X]) (D : ℕ)
    (recip : ∀ u : ℝ, u≠0 → u^D*P.eval u⁻¹=P.eval u)
    {t : ℝ} (ht : t≠0) (hz : P.eval t=0) :
    t^2*P.derivative.eval t = -(t^D)*P.derivative.eval t⁻¹ := by
  have zi : P.eval t⁻¹=0 := (mul_eq_zero.mp ((recip _ ht).trans hz)).resolve_left (pow_ne_zero _ ht)
  have eqn : (fun u : ℝ ↦ u^D*P.eval u⁻¹) =ᶠ[nhds t] fun u ↦ P.eval u := by
    filter_upwards [eventually_ne_nhds ht] with u hu
    exact recip u hu
  have h := ((hasDerivAt_pow D t).mul ((P.hasDerivAt t⁻¹).comp t (hasDerivAt_inv ht)))
  have he := (h.congr_of_eventuallyEq eqn.symm).unique (P.hasDerivAt t)
  simp only [Function.comp_apply,zi,mul_zero,zero_add] at he
  rw [← he]
  field_simp

private theorem sign_of_normalized {n k : ℕ} (hk : 2≤k) (lo : k<n) (hi : n<3*k)
    (x : ℝ) (hz : (deformedRow (n-1) k 1).eval (-exp (-x))=0)
    (h : 0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x)) :
    (deformedRow n k 1).eval (-exp (-x)) *
      (deformedRow (n-1) k 1).derivative.eval (-exp (-x)) < 0 := by
  let t := -exp (-x)
  let P := deformedRow (n-1) k 1
  let Q := deformedRow n k 1
  have ht : t<0 := neg_lt_zero.mpr (exp_pos _)
  have hp : enumerator (n-1) k = X*P := actual_band_row hk (by omega) (by omega)
  have hq : enumerator n k = X*Q := actual_band_row hk (by omega) hi
  have z : (enumerator (n-1) k).eval t=0 := by rw [hp,eval_mul,hz,mul_zero]
  have hp' : (enumerator (n-1) k).derivative.eval t=t*P.derivative.eval t := by
    rw [hp,derivative_mul,derivative_X,one_mul,eval_add,eval_mul,eval_X,hz,zero_add]
  have hv : normalizedEnumerator n k x = t*Q.eval t/(1-t)^n := by
    dsimp only [normalizedEnumerator]
    rw [hq,eval_mul,eval_X]
  have hd : deriv (normalizedEnumerator (n-1) k) x = -t*(enumerator (n-1) k).derivative.eval t/(1-t)^(n-1) := by
    simpa only [t, neg_neg, sub_neg_eq_add] using normalized_deriv_at_original_root x z
  rw [hp'] at hd
  change Q.eval t*P.derivative.eval t<0
  by_contra! bad
  have prod : normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x) =
      (t^3/((1-t)^n*(1-t)^(n-1)))*(Q.eval t*P.derivative.eval t) := by
    rw [hv,hd]
    ring
  have neg : t^3/((1-t)^n*(1-t)^(n-1))≤0 := by
    have hp : 0<1-t := by linarith
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ht.le (sq_nonneg t)]
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg neg bad)) (prod ▸ h)

/-- A sign test on normalized original rows for x≥0 yields the required Sturm sign
at every negative root of the preceding quotient, including t = -1 and t < -1. -/
theorem all_negative_root_sign {n k : ℕ} (hk : 2≤k) (lo : k<n) (hi : n<3*k)
    (h : ∀ x : ℝ, 0≤x → normalizedEnumerator (n-1) k x=0 →
       0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x))
    {t : ℝ} (ht : t<0) (hz : (deformedRow (n-1) k 1).eval t=0) :
    (deformedRow n k 1).eval t * (deformedRow (n-1) k 1).derivative.eval t < 0 := by
  let P := deformedRow (n-1) k 1
  let Q := deformedRow n k 1
  let D := n-1-2
  have unit (u : ℝ) (hu : u<0) (hl : -1≤u) (z : P.eval u=0) :
      Q.eval u*P.derivative.eval u<0 := by
    let x := -log (-u)
    have hx : 0≤x := neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))
    have coord : -exp (-x)=u := by
      simp only [x,neg_neg,exp_log (show 0< -u by linarith)]
    have zn : normalizedEnumerator (n-1) k x=0 := by
      dsimp only [normalizedEnumerator]
      rw [coord,actual_band_row hk (by omega) (by omega),eval_mul,z,mul_zero,zero_div]
    have out := sign_of_normalized hk lo hi x (by rwa [coord]) (h x hx zn)
    rwa [coord] at out
  by_cases hl : -1≤t
  · exact unit _ ht hl hz
  have pr : ∀ u : ℝ, u≠0 → u^D*P.eval u⁻¹=P.eval u :=
    fun _ hu ↦ deformed_reciprocity hk (by omega) 1 hu
  have qr : t^(D+1)*Q.eval t⁻¹=Q.eval t := by
    rw [show D+1=n-2 by dsimp [D]; omega]
    exact deformed_reciprocity hk (by omega) 1 ht.ne
  have zi : P.eval t⁻¹=0 := (mul_eq_zero.mp ((pr _ ht.ne).trans hz)).resolve_left (pow_ne_zero _ ht.ne)
  have invsign := unit t⁻¹ (inv_lt_zero.mpr ht)
    (by rw [inv_eq_one_div,le_div_iff_of_neg ht]; linarith) zi
  have pd := reciprocal_derivative_at_root P D pr ht.ne hz
  have id : t^2*(Q.eval t*P.derivative.eval t) =
      ((-t)*(t^D)^2)*(Q.eval t⁻¹*P.derivative.eval t⁻¹) := by
    rw [← qr,pow_succ]
    linear_combination (t^D*t*Q.eval t⁻¹)*pd
  have fac : 0<(-t)*(t^D)^2 := mul_pos (neg_pos.mpr ht) (sq_pos_of_ne_zero (pow_ne_zero _ ht.ne))
  exact neg_of_mul_neg_right (id.trans_lt (mul_neg_of_pos_of_neg fac invsign)) (sq_nonneg t)

#print axioms normalized_deriv_at_original_root
#print axioms reciprocal_derivative_at_root
#print axioms all_negative_root_sign
end LongCycleBounds.Band
