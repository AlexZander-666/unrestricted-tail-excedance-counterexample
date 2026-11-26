import LongCycleBounds.LinearRootCoordinates
import LongCycleBounds.LinearRowInduction

namespace LongCycleBounds.Band
open Polynomial Real LongCycles LongCycleFinite Finset
noncomputable section

/-- At a root with t = -exp(-x), any pair of actual quotient rows has the Sturm sign
when the normalized successor has the sign of minus the derivative of the predecessor. -/
private theorem quotient_sign_at_exp {n k : ℕ} (P Q : ℝ[X])
    (hp : enumerator (n-1) k = X*P) (hq : enumerator n k = X*Q)
    (x : ℝ) (hz : P.eval (-exp (-x))=0)
    (h : 0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x)) :
    Q.eval (-exp (-x)) * P.derivative.eval (-exp (-x)) < 0 := by
  let t := -exp (-x)
  have ht : t<0 := neg_lt_zero.mpr (exp_pos _)
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

/-- Transport from the exponential chart and use reciprocal symmetry on the other half-axis. -/
theorem actual_quotient_root_sign {n k : ℕ} (hn : 3 ≤ n) (P Q : ℝ[X])
    (hp : enumerator (n-1) k = X*P) (hq : enumerator n k = X*Q)
    (recP : ∀ u : ℝ, u≠0 → u^(n-1-2)*P.eval u⁻¹=P.eval u)
    (recQ : ∀ u : ℝ, u≠0 → u^(n-2)*Q.eval u⁻¹=Q.eval u)
    (h : ∀ x : ℝ, 0≤x → normalizedEnumerator (n-1) k x=0 →
       0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x))
    {t : ℝ} (ht : t<0) (hz : P.eval t=0) :
    Q.eval t * P.derivative.eval t < 0 := by
  let D := n-1-2
  have unit (u : ℝ) (hu : u<0) (hl : -1≤u) (z : P.eval u=0) :
      Q.eval u*P.derivative.eval u<0 := by
    let x := -log (-u)
    have hx : 0≤x := neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))
    have coord : -exp (-x)=u := by
      simp only [x,neg_neg,exp_log (show 0< -u by linarith)]
    have zn : normalizedEnumerator (n-1) k x=0 := by
      dsimp only [normalizedEnumerator]
      rw [coord,hp,eval_mul,z,mul_zero,zero_div]
    have out := quotient_sign_at_exp P Q hp hq x (by rwa [coord]) (h x hx zn)
    rwa [coord] at out
  by_cases hl : -1≤t
  · exact unit _ ht hl hz
  have qr : t^(D+1)*Q.eval t⁻¹=Q.eval t := by
    rw [show D+1=n-2 by dsimp [D]; omega]
    exact recQ _ ht.ne
  have zi : P.eval t⁻¹=0 := (mul_eq_zero.mp ((recP _ ht.ne).trans hz)).resolve_left (pow_ne_zero _ ht.ne)
  have invsign := unit t⁻¹ (inv_lt_zero.mpr ht)
    (by rw [inv_eq_one_div,le_div_iff_of_neg ht]; linarith) zi
  have pd := reciprocal_derivative_at_root P D recP ht.ne hz
  have id : t^2*(Q.eval t*P.derivative.eval t) =
      ((-t)*(t^D)^2)*(Q.eval t⁻¹*P.derivative.eval t⁻¹) := by
    rw [← qr,pow_succ]
    linear_combination (t^D*t*Q.eval t⁻¹)*pd
  have fac : 0<(-t)*(t^D)^2 := mul_pos (neg_pos.mpr ht) (sq_pos_of_ne_zero (pow_ne_zero _ ht.ne))
  exact neg_of_mul_neg_right (id.trans_lt (mul_neg_of_pos_of_neg fac invsign)) (sq_nonneg t)

/-- From one fully ordered predecessor pair, a reciprocal original successor extends the chain. -/
theorem extend_actual_interlacing {n k : ℕ} (hn : 4 ≤ n) (L P Q : ℝ[X])
    (prev : StrictNegativeInterlacing L P (n-4)) (hmP : P.Monic)
    (hmQ : Q.Monic) (hdQ : Q.natDegree=n-2) (cQ : 0 < Q.eval 0)
    (hp : enumerator (n-1) k=X*P) (hq : enumerator n k=X*Q)
    (recP : ∀ u : ℝ, u≠0 → u^(n-1-2)*P.eval u⁻¹=P.eval u)
    (recQ : ∀ u : ℝ, u≠0 → u^(n-2)*Q.eval u⁻¹=Q.eval u)
    (sign : ∀ x : ℝ, 0≤x → normalizedEnumerator (n-1) k x=0 →
       0 < normalizedEnumerator n k x * (-deriv (normalizedEnumerator (n-1) k) x)) :
    StrictNegativeInterlacing P Q (n-3) ∧
      WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  obtain ⟨_,v,_,_,_,fv,_,mv,_,nv,_⟩ := prev
  rw [hmP.leadingCoeff,map_one,one_mul] at fv
  have h := linear_sturm_step v fv mv nv hmQ (hdQ.trans (by omega)) cQ
    (fun _ ht hz ↦ actual_quotient_root_sign (by omega) P Q hp hq recP recQ sign ht hz)
  have hh : StrictNegativeInterlacing P Q (n-3) := by simpa only [show n-4+1=n-3 by omega] using h
  exact ⟨hh, hp ▸ hq ▸ weak_mul_X_of_strict hh⟩

#print axioms actual_quotient_root_sign
#print axioms extend_actual_interlacing
end
end LongCycleBounds.Band
