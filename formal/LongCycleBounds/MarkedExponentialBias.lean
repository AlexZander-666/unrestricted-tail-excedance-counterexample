import LongCycleBounds.MarkedTwoEGF
import Mathlib.Analysis.Complex.Exponential

/-! Uniform coefficient perturbation by a linear and quadratic exponential.
The order is arbitrary, and the input series can have either sign. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Finset Real PowerSeries
open scoped Classical

def linearExp (a : ℝ) : PowerSeries ℝ := PowerSeries.mk fun n ↦ a^n/n.factorial

def scaledCoeff (f : PowerSeries ℝ) (ρ : ℝ) (j : ℕ) := ρ^(j+1)*coeff j f

/-- Dimensionless transfer for an exponential in a single power of the size variable. -/
def shiftExp (d : ℕ) (v : ℝ) (F : ℕ → ℝ) (j : ℕ) :=
  ∑ i ∈ range (j/d+1), (v^i/i.factorial)*F (j-d*i)

theorem shiftExp_abs {M v : ℝ} (hv : 0 ≤ v) (hM : 0 ≤ M)
    (d j : ℕ) (F : ℕ → ℝ) (hF : ∀ i ≤ j, |F i| ≤ M) :
    |shiftExp d v F j| ≤ M*exp v := by
  unfold shiftExp
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ i ∈ range (j/d+1), (v^i/i.factorial)*M := by
      apply sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ v^i/i.factorial)]
      exact mul_le_mul_of_nonneg_left (hF _ (Nat.sub_le ..)) (by positivity)
    _ ≤ _ := by
      rw [←sum_mul,mul_comm M]
      exact mul_le_mul_of_nonneg_right (sum_le_exp_of_nonneg hv _) hM

theorem shiftExp_bias {M v : ℝ} (hv : 0 ≤ v) (hM : 0 ≤ M)
    (d j : ℕ) (F : ℕ → ℝ) (hF : ∀ i ≤ j, |F i| ≤ M) :
    |shiftExp d v F j-F j| ≤ M*(exp v-1) := by
  unfold shiftExp
  rw [sum_range_succ']
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,Nat.mul_zero,Nat.sub_zero,one_mul,
    add_sub_cancel_right]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ i ∈ range (j/d), (v^(i+1)/(i+1).factorial)*M := by
      apply sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ v^(i+1)/(i+1).factorial)]
      exact mul_le_mul_of_nonneg_left (hF _ (Nat.sub_le ..)) (by positivity)
    _ ≤ _ := by
      rw [←sum_mul,mul_comm M]
      apply mul_le_mul_of_nonneg_right _ hM
      have h := sum_le_exp_of_nonneg hv (j/d+1)
      rw [sum_range_succ'] at h
      simpa using (le_sub_iff_add_le.mpr (by simpa using h) :
        (∑ i ∈ range (j/d), v^(i+1)/(i+1).factorial) ≤ exp v-1)

theorem linearExp_scaled (a ρ : ℝ) (f : PowerSeries ℝ) (j : ℕ) :
    scaledCoeff (linearExp a*f) ρ j = shiftExp 1 (a*ρ) (scaledCoeff f ρ) j := by
  unfold scaledCoeff shiftExp
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,mul_sum,Nat.div_one]
  apply sum_congr rfl
  intro d hd
  have le := mem_range.mp hd
  rw [show j+1=d+(j-d+1) by omega,pow_add]
  simp only [linearExp,coeff_mk,one_mul,mul_pow]
  ring

theorem quadraticExp_scaled (b ρ : ℝ) (f : PowerSeries ℝ) (j : ℕ) :
    scaledCoeff (quadraticExp b*f) ρ j = shiftExp 2 (b*ρ^2) (scaledCoeff f ρ) j := by
  unfold scaledCoeff shiftExp
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,mul_sum]
  simp only [quadraticExp,coeff_mk]
  let F (d : ℕ) := ρ^(j+1)*((b^(d/2)/(d/2).factorial)*coeff (j-d) f)
  have cut : (∑ x ∈ range (j+1), ρ^(j+1)*
    ((if x%2=0 then b^(x/2)/(x/2).factorial else 0)*coeff (j-x) f)) =
      ∑ d ∈ (range (j+1)).filter (fun d ↦ d%2=0), F d := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp [F]
  rw [cut]
  refine sum_bij' (fun d _ ↦ d/2) (fun i _ ↦ 2*i) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨h,z⟩ := mem_filter.mp hd
    have := mem_range.mp h
    exact mem_range.mpr (by omega)
  · intro i hi
    have := mem_range.mp hi
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩
  · intro d hd
    have := (mem_filter.mp hd).2
    omega
  · intro i _
    omega
  · intro d hd
    obtain ⟨h,z⟩ := mem_filter.mp hd
    have := mem_range.mp h
    have de : 2*(d/2)=d := by omega
    simp only [F,mul_pow,←pow_mul,de]
    rw [show j+1=d+(j-d+1) by omega,pow_add]
    ring

/-- Coefficients of the full bias times an arbitrary input series, in the
same scaling and with the same uniform error as the middle region of the proof. -/
theorem exponential_bias {a b ρ M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ ρ) (hm : 0 ≤ M)
    (f : PowerSeries ℝ) (j : ℕ) (h : ∀ i≤j, |scaledCoeff f ρ i| ≤ M) :
    |scaledCoeff (linearExp a*(quadraticExp b*f)) ρ j-scaledCoeff f ρ j| ≤
      M*(exp (a*ρ+b*ρ^2)-1) := by
  have m (i : ℕ) (hi : i≤j) : |scaledCoeff (quadraticExp b*f) ρ i| ≤ M*exp (b*ρ^2) := by
    rw [quadraticExp_scaled]
    exact shiftExp_abs (by positivity) hm _ _ _ (fun v hv ↦ h v (hv.trans hi))
  have first := shiftExp_bias (by positivity : 0≤a*ρ) (mul_nonneg hm (exp_pos _).le)
    1 j (scaledCoeff (quadraticExp b*f) ρ) m
  have second := shiftExp_bias (by positivity : 0≤b*ρ^2) hm 2 j (scaledCoeff f ρ) h
  rw [←linearExp_scaled] at first
  rw [←quadraticExp_scaled] at second
  apply (abs_sub_le _ (scaledCoeff (quadraticExp b*f) ρ j) _).trans
  calc _ ≤ _ := add_le_add first second
       _ = _ := by rw [exp_add]; ring

#print axioms exponential_bias
end LongCycleBounds.MarkedTwo
