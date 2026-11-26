import LongCycleBounds.MarkedLabelBias
import LongCycleBounds.EulerianSeries

/-! The normalized source EGF as a linear and quadratic exponential times
the formal logistic series. The last identity is proved from the permutation
Eulerian power sums and the finite anchored-cycle differential equation. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open PowerSeries Finset Real
open scoped Classical

def logisticMoment (t : ℝ) (j : ℕ) : ℝ :=
  if j=0 then 1/(1-t) else t*(LongCycles.eulerian j).eval t/(1-t)^(j+1)

def logistic (t : ℝ) : PowerSeries ℝ :=
  mk fun j ↦ logisticMoment t j / j.factorial

private theorem logisticMoment_sum {t : ℝ} (ht : ‖t‖<1) (j : ℕ) :
    logisticMoment t j = ∑' h : ℕ, (h:ℝ)^j*t^h := by
  by_cases zero : j=0
  · subst j
    simp [logisticMoment,tsum_geometric_of_norm_lt_one ht,one_div]
  · simpa [logisticMoment,zero] using eulerian_eq_powerSeries j (by omega) t ht

private theorem logistic_step {t : ℝ} (ht : ‖t‖<1) (n : ℕ) :
    t*(∑ d ∈ range (n+1), (n.choose d:ℝ)*logisticMoment t d) =
      logisticMoment t n - (0:ℝ)^n := by
  have summ (d : ℕ) (_ : d∈range (n+1)) :
      Summable (fun h : ℕ ↦ (n.choose d:ℝ)*((h:ℝ)^d*t^h)) :=
    (summable_pow_mul_geometric_of_norm_lt_one d ht).mul_left _
  simp_rw [logisticMoment_sum ht,←tsum_mul_left]
  rw [←Summable.tsum_finsetSum summ,←tsum_mul_left]
  have move (h : ℕ) : t*(∑ d ∈ range (n+1), (n.choose d:ℝ)*((h:ℝ)^d*t^h)) =
      ((h+1:ℕ):ℝ)^n*t^(h+1) := by
    rw [Nat.cast_succ,add_pow,pow_succ,Finset.sum_mul]
    simp only [one_pow,mul_one]
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  simp_rw [move]
  have s := (summable_pow_mul_geometric_of_norm_lt_one n ht).tsum_eq_zero_add
  simpa using (eq_sub_of_add_eq' s.symm)

private theorem linear_derivative (a : ℝ) :
    PowerSeries.derivative ℝ (linearExp a)=C a*linearExp a := by
  apply PowerSeries.ext
  intro n
  rw [coeff_derivative,coeff_C_mul]
  simp only [linearExp,coeff_mk,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  field_simp

private theorem coeff_product_exp (t : ℝ) (n : ℕ) :
    coeff n (logistic t*linearExp 1) =
      (∑ d ∈ range (n+1), (n.choose d:ℝ)*logisticMoment t d)/n.factorial := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,sum_div]
  apply sum_congr rfl
  intro d hd
  have le : d≤n := by have := mem_range.mp hd;omega
  have comb : (n.choose d:ℝ)*d.factorial*(n-d).factorial=n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial le
  simp [logistic,linearExp,coeff_mk]
  field_simp
  linear_combination -(logisticMoment t d)*comb

theorem logistic_resolvent {t : ℝ} (ht : ‖t‖<1) :
    logistic t*(1-C t*linearExp 1)=1 := by
  apply PowerSeries.ext
  intro n
  rw [mul_sub,mul_one,show logistic t*(C t*linearExp 1)=C t*(logistic t*linearExp 1) by ring,
    map_sub,coeff_C_mul,coeff_product_exp,←mul_div_assoc,logistic_step ht,coeff_one]
  simp only [logistic,coeff_mk]
  by_cases e : n=0 <;> simp [e,logisticMoment]

private theorem logistic_derivative_of_resolvent {t : ℝ}
    (hi : logistic t*(1-C t*linearExp 1)=1) :
    PowerSeries.derivative ℝ (logistic t) = (logistic t-1)*(logistic t) := by
  let L := logistic t
  let A := C t*linearExp 1
  have inv : L*(1-A)=1 := hi
  have dd := congrArg (PowerSeries.derivative ℝ) inv
  have da : PowerSeries.derivative ℝ A=A := by
    dsimp [A]
    rw [Derivation.leibniz,derivative_C,linear_derivative]
    simp
  change PowerSeries.derivative ℝ (L*(1-A))=PowerSeries.derivative ℝ 1 at dd
  rw [Derivation.leibniz,map_sub,derivative_one,da] at dd
  simp only [smul_eq_mul,sub_eq_add_neg] at dd
  have ea : L*A=L-1 := by linear_combination -inv
  change PowerSeries.derivative ℝ L=(L-1)*L
  calc
    _ = (PowerSeries.derivative ℝ L*(1-A))*L := by rw [mul_right_comm, mul_assoc,inv,mul_one]
    _ = (L*A)*L := by congr 1;linear_combination dd
    _ = _ := by rw [ea]


private theorem moment_continuous (j : ℕ) (t : ℝ) (ht : t≠1) :
    ContinuousAt (fun y ↦ logisticMoment y j) t := by
  by_cases z : j=0
  · simp only [logisticMoment,z,if_true]
    exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simpa using sub_ne_zero.mpr ht.symm)
  · simp only [logisticMoment,z,if_false]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ (sub_ne_zero.mpr ht.symm)

/-- Includes t=-1 via continuity of each finite rational coefficient. -/
theorem logistic_resolvent_closed {t : ℝ} (lo : -1≤t) (hi : t≤0) :
    logistic t*(1-C t*linearExp 1)=1 := by
  apply PowerSeries.ext
  intro n
  let f (y : ℝ) := logisticMoment y n/n.factorial -
    y*((∑ d ∈ range (n+1), (n.choose d:ℝ)*logisticMoment y d)/n.factorial)
  have form (y : ℝ) : coeff n (logistic y*(1-C y*linearExp 1)) = f y := by
    rw [mul_sub,mul_one,show logistic y*(C y*linearExp 1)=C y*(logistic y*linearExp 1) by ring,
      map_sub,coeff_C_mul,coeff_product_exp]
    simp only [logistic,coeff_mk,f]
  rw [form]
  let I := Set.Icc (-1:ℝ) 0
  have cf : ContinuousOn f I := by
    intro y hy
    have yhi : y ≤ 0 := hy.2
    have sm (d : ℕ) : ContinuousAt (fun z ↦ logisticMoment z d) y :=
      moment_continuous d y (by linarith)
    apply ContinuousAt.continuousWithinAt
    unfold f
    fun_prop (disch := assumption)
  have closed := isClosed_Icc.isClosed_eq cf (continuousOn_const (c:=coeff n (1:PowerSeries ℝ)))
  have sub : Set.Ioo (-1:ℝ) 0 ⊆ {y ∈ I | f y=coeff n (1:PowerSeries ℝ)} := by
    intro y hy
    refine ⟨⟨hy.1.le,hy.2.le⟩,?_⟩
    rw [←form,logistic_resolvent (t:=y) (by rw [Real.norm_eq_abs,abs_lt];exact ⟨hy.1,by linarith [hy.2]⟩)]
  have ext := closure_minimal sub closed
  rw [closure_Ioo (by norm_num : (-1:ℝ)≠0)] at ext
  exact (ext ⟨lo,hi⟩).2

theorem logistic_derivative_closed {t : ℝ} (lo : -1≤t) (hi : t≤0) :
    PowerSeries.derivative ℝ (logistic t)=(logistic t-1)*logistic t :=
  logistic_derivative_of_resolvent (logistic_resolvent_closed lo hi)

private theorem rescale_derivative (q : ℝ) (f : PowerSeries ℝ) :
    PowerSeries.derivative ℝ (rescale q f) = C q * rescale q (PowerSeries.derivative ℝ f) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_derivative,coeff_rescale,coeff_C_mul,coeff_rescale,coeff_derivative,pow_succ]
  ring

private theorem derangement_driver (t : ℝ) (ht : t≠1) :
    C (1/(1-t))*rescale (1/(1-t)) (cycleDriver 1 t) = logistic t-C (1/(1-t)) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_C_mul,coeff_rescale,map_sub,coeff_C]
  by_cases hn : n=0
  · simp [hn,logistic,logisticMoment,cycleDriver,cycleDerivativeCoeff,coeff_mk]
  · simp only [logistic,logisticMoment,cycleDriver,cycleDerivativeCoeff,coeff_mk,hn,if_false,
      ite_self,one_mul,sub_zero,pow_succ]
    have ne := sub_ne_zero.mpr ht.symm
    rw [div_pow]
    simp only [one_pow]
    field_simp

private theorem derangement_normalized {t : ℝ} (lo : -1≤t) (hi : t≤0) :
    rescale (1/(1-t)) (egf 1 t) = C (1-t)*(linearExp (-t/(1-t))*logistic t) := by
  let q := 1/(1-t)
  let a := -t/(1-t)
  have ht : t≠1 := by linarith
  have hp : 1-t≠0 := sub_ne_zero.mpr ht.symm
  have aid : C a - (1:PowerSeries ℝ) = -C q := by
    rw [←map_one (PowerSeries.C : ℝ →+* PowerSeries ℝ),←map_sub,←map_neg]
    congr 1
    dsimp [a,q]
    field_simp
    ring
  change rescale q (egf 1 t) = C (1-t)*(linearExp a*logistic t)
  apply driver_unique (A:=logistic t-C q)
  · rw [coeff_rescale,egf_constant,coeff_C_mul,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [linearExp,logistic,logisticMoment,coeff_mk,hp]
  · rw [rescale_derivative,egf_derivative,map_mul,←mul_assoc,derangement_driver t ht]
  · rw [Derivation.leibniz,derivative_C,Derivation.leibniz,linear_derivative,logistic_derivative_closed lo hi]
    simp only [smul_eq_mul,mul_zero,add_zero]
    linear_combination C (1-t)*linearExp a*logistic t*aid

private theorem quadratic_rescale (q v : ℝ) :
    rescale q (quadraticExp v) = quadraticExp (v*q^2) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_rescale]
  simp only [quadraticExp,coeff_mk]
  by_cases h : n%2=0
  · simp only [h,if_true,mul_pow,←pow_mul,show 2*(n/2)=n by omega]
    ring
  · simp [h]

def normalizedEGF (u t : ℝ) : PowerSeries ℝ := rescale (1/(1-t)) (egf u t)

/-- The original weighted permutations in normalized coordinates, including
the alternating endpoint t=-1. The logistic factor multiplies 1-t exp(z) to 1. -/
theorem normalizedEGF_logistic (u t : ℝ) (lo : -1≤t) (hi : t≤0) :
    normalizedEGF u t =
      C (1-t)*(linearExp (-t/(1-t))*(quadraticExp ((u-1)*t/(2*(1-t)^2))*logistic t)) := by
  rw [normalizedEGF,egf_two_cycle_deformation,map_mul,derangement_normalized lo hi,quadratic_rescale]
  rw [show (u-1)*t/2*(1/(1-t))^2=(u-1)*t/(2*(1-t)^2) by
    have hn : 1-t≠0 := by linarith
    field_simp [hn]]
  ring


/-- The dimensionless true permutation coefficient after removal of the
prefactor 1-t, as used in the three-region analytic argument. -/
def scaledRow (u t ρ : ℝ) (j : ℕ) :=
  ρ^(j+1) * (row j u).eval t / ((1-t)^(j+1)*j.factorial)

theorem scaledRow_exact (u t ρ : ℝ) (lo : -1≤t) (hi : t≤0) (j : ℕ) :
    scaledRow u t ρ j = scaledCoeff
      (linearExp (-t/(1-t))*(quadraticExp ((u-1)*t/(2*(1-t)^2))*logistic t)) ρ j := by
  have eq := congrArg (coeff j) (normalizedEGF_logistic u t lo hi)
  simp only [normalizedEGF,coeff_rescale,egf,coeff_mk,coeff_C_mul,div_pow,one_pow] at eq
  have ne : 1-t≠0 := by linarith
  unfold scaledRow scaledCoeff
  rw [pow_succ (1-t)]
  field_simp [ne] at eq ⊢
  linear_combination ρ^(j+1)*eq

/-- Comparison of a genuine marked permutation row with the pure logistic
coefficient at any order, also at t=-1. The bound on the preceding pure
coefficients is the sole analytic input. -/
theorem scaledRow_logistic_bias {u t ρ M : ℝ} (hu : u≤1) (lo : -1≤t) (hi : t≤0)
    (hr : 0≤ρ) (hm : 0≤M) (j : ℕ) (mass : ∀ i≤j, |scaledCoeff (logistic t) ρ i|≤M) :
    |scaledRow u t ρ j-scaledCoeff (logistic t) ρ j| ≤
      M*(exp ((-t/(1-t))*ρ+((u-1)*t/(2*(1-t)^2))*ρ^2)-1) := by
  rw [scaledRow_exact u t ρ lo hi j]
  apply exponential_bias _ _ hr hm _ j mass
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) hi) (by positivity)

#print axioms logistic_resolvent_closed
#print axioms normalizedEGF_logistic
#print axioms scaledRow_logistic_bias
end LongCycleBounds.MarkedTwo
