import LongCycleBounds.MarkedLogistic
import LongCycleBounds.UniversalRecurrence

/-! Transport of the derangement insertion identity through the transposition mark. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Finset PowerSeries Real
open scoped Classical

def time (x : ℝ) : ℝ := -exp (-x)
def normalizedRow (u : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (row j u).eval (time x)/(1-time x)^j

private def flow (u x : ℝ) := normalizedEGF u (time x)
private def bcoef (u x : ℝ) := (u-1)*time x/(2*(1-time x)^2)
def alpha (u x : ℝ) := u*time x/(1-time x)^2
def beta (u x : ℝ) := (1-u)*time x*(1+time x)/(2*(1-time x)^3)

private theorem coeff_flow (u x : ℝ) (i : ℕ) :
    coeff i (flow u x)=normalizedRow u i x/i.factorial := by
  rw [flow,normalizedEGF,coeff_rescale]
  simp only [egf,coeff_mk,normalizedRow,div_pow,one_pow]
  ring

private theorem flow_deformation (u x : ℝ) :
    flow u x=flow 1 x*quadraticExp (bcoef u x) := by
  unfold flow normalizedEGF
  rw [egf_two_cycle_deformation,map_mul]
  congr 1
  apply PowerSeries.ext
  intro i
  rw [coeff_rescale]
  simp only [quadraticExp,coeff_mk]
  split_ifs with hi
  · have p : 2*(i/2)=i := by omega
    have rel : bcoef u x = ((u-1)*time x/2)*(1/(1-time x))^2 := by
      unfold bcoef
      field_simp
    rw [rel,mul_pow,←pow_mul,p]
    ring
  · ring

private def CoeffDeriv (f : ℝ → PowerSeries ℝ) (g : PowerSeries ℝ) (x : ℝ) :=
  ∀ i, HasDerivAt (fun y ↦ coeff i (f y)) (coeff i g) x

private theorem coeffDeriv_mul {f h : ℝ → PowerSeries ℝ} {g l : PowerSeries ℝ} {x : ℝ}
    (df : CoeffDeriv f g x) (dh : CoeffDeriv h l x) :
    CoeffDeriv (fun y ↦ f y*h y) (g*h x+f x*l) x := by
  intro j
  simp only [map_add,coeff_mul,←Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun ij _ ↦ (df ij.1).mul (dh ij.2)

private theorem baseTransport (x : ℝ) : CoeffDeriv (flow 1)
    (C (time x/(1-time x)^2)*(flow 1 x*X) - PowerSeries.derivative ℝ (flow 1 x)) x := by
  intro j
  simp only [coeff_flow,map_sub,coeff_C_mul,coeff_derivative]
  have origin (y : ℝ) : normalizedRow 1 0 y = 1 := by
    simpa [egf,normalizedRow,coeff_mk] using egf_constant 1 (time y)
  have one (y : ℝ) : normalizedRow 1 1 y = 0 := by
    have r := row_succ_eval 0 1 (time y)
    simp [cycleDerivativeCoeff] at r
    simp [normalizedRow,r]
  cases j with
  | zero =>
    simp only [origin,coeff_zero_mul_X,mul_zero,one,Nat.factorial_zero,
      Nat.cast_one,div_one,zero_div,zero_mul,sub_zero]
    exact hasDerivAt_const x 1
  | succ m =>
    rw [coeff_succ_mul_X,coeff_flow]
    have hc := (Insertion.universal_hasDerivAt (n:=m+1) (k:=2) (by decide) (by omega) x).div_const
      ((m+1).factorial:ℝ)
    have actual (q : ℕ) : normalizedRow 1 q = Band.normalizedEnumerator q 2 := by
      funext y
      simp [normalizedRow,Band.normalizedEnumerator,time,row_one]
    simp only [actual]
    apply hc.congr_deriv
    rw [show m+1+1-2=m by omega]
    simp only [Nat.reduceSubDiff,Nat.choose_one_right,Band.cycleMoment,Band.moment,
      longEulerian_one,Polynomial.eval_one,mul_one]
    rw [Nat.factorial_succ (m+1),Nat.cast_mul,Nat.cast_succ]
    simp only [Nat.cast_succ]
    rw [Nat.factorial_succ m,Nat.cast_mul,Nat.cast_succ]
    unfold time
    field_simp

private theorem b_derivative (u x : ℝ) : HasDerivAt (bcoef u) (beta u x) x := by
  have dt : HasDerivAt time (-time x) x := by
    exact (((hasDerivAt_id x).neg.exp).neg).congr_deriv (by simp [time])
  have ne : 1-time x≠0 := by dsimp [time];linarith [exp_pos (-x)]
  have db := (dt.const_mul (u-1)).div (((hasDerivAt_const x (1:ℝ)).sub dt).pow 2 |>.const_mul 2)
    (show 2*(1-time x)^2≠0 by positivity)
  apply db.congr_deriv
  change (((u-1)*(-time x)) * (2 * (1-time x)^2) - ((u-1)*time x) *
    (2*(2*(1-time x)^1*(0-(-time x)))))/(2*(1-time x)^2)^2 = _
  unfold beta
  field_simp [ne]
  ring

private theorem tilted_deriv (u x : ℝ) : CoeffDeriv (fun y ↦ quadraticExp (bcoef u y))
    (C (beta u x)*(quadraticExp (bcoef u x)*X^2)) x := by
  intro i
  rw [coeff_C_mul,coeff_mul_X_pow']
  simp only [quadraticExp,coeff_mk]
  by_cases zero : i=0
  · subst i
    simpa using hasDerivAt_const x (1:ℝ)
  by_cases even : i%2=0
  · have hi : 2 ≤ i := by omega
    have he : (i-2)%2=0 := by omega
    have he' : i/2=(i-2)/2+1 := by omega
    simp only [even,hi,he,if_true,he']
    apply (((b_derivative u x).pow ((i-2)/2+1)).div_const (((i-2)/2+1).factorial:ℝ)).congr_deriv
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    simp only [Nat.add_one_sub_one]
    field_simp
  · have he : (i-2)%2≠0 ∨ ¬2 ≤ i := by omega
    simp only [even,if_false]
    rcases he with he|he
    · simp [he,hasDerivAt_const]
    · simp [he,hasDerivAt_const]

private theorem tilted_z_derivative (v : ℝ) :
    PowerSeries.derivative ℝ (quadraticExp v) =
      (PowerSeries.C (2*v)*PowerSeries.X)*quadraticExp v := by
  apply PowerSeries.ext
  intro n
  rw [show (PowerSeries.C (2*v)*PowerSeries.X)*quadraticExp v =
    PowerSeries.C (2*v)*(quadraticExp v*PowerSeries.X) by ring,
    PowerSeries.coeff_derivative,PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    simp [quadraticExp,PowerSeries.coeff_mk]
  | succ d =>
    rw [PowerSeries.coeff_succ_mul_X]
    simp only [quadraticExp,PowerSeries.coeff_mk]
    by_cases h : d%2=0
    · have a : (d+1+1)%2=0 := by omega
      have b : (d+1+1)/2=d/2+1 := by omega
      have c : (d:ℝ)+1+1=2*((d/2:ℕ):ℝ)+2 := by
        exact_mod_cast (show d+1+1=2*(d/2)+2 by omega)
      rw [if_pos a,if_pos h,b,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,Nat.cast_succ,c]
      have z : (↑(d/2:ℕ)+1:ℝ)≠0 := by positivity
      have f : (((d/2).factorial:ℕ):ℝ)≠0 := by positivity
      field_simp
    · have a : (d+1+1)%2≠0 := by omega
      simp [a,h]

private theorem transport (u x : ℝ) : CoeffDeriv (flow u) (
    (C (alpha u x)*X+C (beta u x)*X^2)*flow u x - PowerSeries.derivative ℝ (flow u x)) x := by
  have h := coeffDeriv_mul (baseTransport x) (tilted_deriv u x)
  have hc : C (alpha u x)=C (time x/(1-time x)^2)+C (2*bcoef u x) := by
    rw [←map_add]
    congr 1
    unfold alpha bcoef
    have ne : 1-time x≠0 := by dsimp [time];linarith [exp_pos (-x)]
    field_simp [ne]
    ring
  intro i
  simp_rw [flow_deformation u]
  apply (h i).congr_deriv
  congr 1
  rw [Derivation.leibniz,tilted_z_derivative,hc]
  simp only [smul_eq_mul]
  ring

/-- Original marked rows with the lower index written as m+2. This holds
for every real mark u and logarithmic parameter x, including x=0. -/
theorem normalizedRow_hasDerivAt (u x : ℝ) (m : ℕ) :
    HasDerivAt (normalizedRow u (m+2))
      (((m:ℝ)+2)*alpha u x*normalizedRow u (m+1) x +
       ((m:ℝ)+2)*((m:ℝ)+1)*beta u x*normalizedRow u m x -
       normalizedRow u (m+3) x) x := by
  have h := (transport u x (m+2)).mul_const ((m+2).factorial:ℝ)
  have eval (y : ℝ) : coeff (m+2) (flow u y)*((m+2).factorial:ℝ)=normalizedRow u (m+2) y := by
    rw [coeff_flow];field_simp
  simp_rw [eval] at h
  apply h.congr_deriv
  rw [add_mul,map_sub,map_add,coeff_derivative,
    show C (alpha u x)*X*flow u x=C (alpha u x)*(flow u x*X) by ring,
    show C (beta u x)*X^2*flow u x=C (beta u x)*(flow u x*X^2) by ring,
    coeff_C_mul,coeff_C_mul,coeff_succ_mul_X,coeff_mul_X_pow]
  simp only [coeff_flow]
  rw [Nat.factorial_succ (m+2),Nat.cast_mul,Nat.factorial_succ (m+1),Nat.cast_mul,
    Nat.factorial_succ m,Nat.cast_mul]
  simp only [Nat.cast_succ]
  field_simp
  ring

#print axioms normalizedRow_hasDerivAt
end LongCycleBounds.MarkedTwo
