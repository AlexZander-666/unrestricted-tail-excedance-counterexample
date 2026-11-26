import LongCycleBounds.MarkedExponentialBias

/-! Positive and zero label estimates for the deformed derangement series. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Finset PowerSeries Real
open scoped Classical

def labelCoefficient (a b h : ℝ) (j : ℕ) : ℝ :=
  j.factorial * coeff j (linearExp a*(quadraticExp b*linearExp h))

private theorem shiftExp_lower {v : ℝ} (hv : 0 ≤ v) (d j : ℕ)
    (F : ℕ → ℝ) (hF : ∀ i, 0 ≤ F i) : F j ≤ shiftExp d v F j := by
  rw [shiftExp,sum_range_succ']
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,Nat.mul_zero,Nat.sub_zero,one_mul,
    le_add_iff_nonneg_left]
  exact sum_nonneg fun i _ ↦ mul_nonneg (by positivity) (hF _)

/-- The tilted radius j/h makes the j-th coefficient of exp(hz) maximal among
all preceding scaled coefficients. This converts the common bias estimate into a
relative bound with no prefactor and no large parameter restriction. -/
theorem label_bounds {a b h : ℝ} (ha : 0≤a) (hb : 0≤b) (hh : 0<h)
    (j : ℕ) (hj : 0<j) : h^j ≤ labelCoefficient a b h j ∧
    labelCoefficient a b h j ≤ h^j*exp (a*(j/h)+b*(j/h)^2) := by
  let ρ : ℝ := j/h
  have rpos : 0<ρ := by dsimp [ρ]; positivity
  have rj : ρ*h=(j:ℝ) := by dsimp [ρ];field_simp
  let F := scaledCoeff (linearExp h) ρ
  have form (i : ℕ) : F i=ρ^(i+1)*(h^i/i.factorial) := by simp [F,scaledCoeff,linearExp,coeff_mk]
  have nn (i : ℕ) : 0≤F i := by rw [form];positivity
  have inc (i : ℕ) (hi : i<j) : F i ≤ F (i+1) := by
    have rel : F (i+1)*((i:ℝ)+1) = F i * (ρ*h) := by
      rw [form,form,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,pow_succ h,pow_succ ρ (i+1)]
      field_simp
    have pos : 0<(i:ℝ)+1 := by positivity
    apply le_of_mul_le_mul_right (a:=(i:ℝ)+1) _ pos
    rw [rel,rj]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi) (nn i)
  have mono (i m : ℕ) (hi : i ≤ m) : m ≤ j → F i≤F m := by
    induction m,hi using Nat.le_induction with
    | base => exact fun _ ↦ le_rfl
    | succ m _ ih => exact fun hm ↦ (ih (by omega)).trans (inc m (by omega))
  let Q := scaledCoeff (quadraticExp b*linearExp h) ρ
  let Y := scaledCoeff (linearExp a*(quadraticExp b*linearExp h)) ρ j
  have lower (i : ℕ) : F i ≤ Q i := by
    dsimp [Q]
    rw [quadraticExp_scaled]
    exact shiftExp_lower (by positivity) 2 i F nn
  have low : F j ≤ Y := by
    apply (lower j).trans
    dsimp [Y]
    rw [linearExp_scaled]
    exact shiftExp_lower (by positivity) _ _ Q (fun i ↦ (nn i).trans (lower i))
  have bias := exponential_bias ha hb rpos.le (nn j) (linearExp h) j
    (fun i le ↦ (abs_of_nonneg (nn i)).trans_le (mono i j le le_rfl))
  change |Y-F j| ≤ _ at bias
  have high : Y ≤ F j*exp (a*ρ+b*ρ^2) := by linarith [le_abs_self (Y-F j)]
  have resc : (ρ^(j+1)/j.factorial)*labelCoefficient a b h j = Y := by
    dsimp [Y,labelCoefficient,scaledCoeff]
    field_simp
  have baseline : (ρ^(j+1)/j.factorial)*h^j=F j := by rw [form];ring
  have z : 0<ρ^(j+1)/j.factorial := by positivity
  refine ⟨le_of_mul_le_mul_left (a:=ρ^(j+1)/j.factorial) (by rw [resc,baseline];exact low) z,
    le_of_mul_le_mul_left (a:=ρ^(j+1)/j.factorial) ?_ z⟩
  rw [resc,←mul_assoc,baseline]
  exact high

/-- Cauchy's positive-coefficient estimate at a real radius. -/
theorem coeff_bias_zero_label {a b ρ : ℝ} (ha : 0≤a) (hb : 0≤b) (hr : 0<ρ) (j : ℕ) :
    |labelCoefficient a b 0 j| ≤ j.factorial*exp (a*ρ+b*ρ^2)/ρ^j := by
  have form (i : ℕ) : scaledCoeff (linearExp 0) ρ i =
      if i=0 then ρ else 0 := by
    by_cases hi : i=0 <;> simp [scaledCoeff,linearExp,coeff_mk,hi]
  have bound (i : ℕ) : |scaledCoeff (linearExp 0) ρ i| ≤ ρ := by
    rw [form]; split <;> simp [abs_of_pos hr,hr.le]
  have s := exponential_bias ha hb hr.le hr.le (linearExp 0) j (fun i _ ↦ bound i)
  let Y := scaledCoeff (linearExp a*(quadraticExp b*linearExp 0)) ρ j
  have y : |Y| ≤ ρ*exp (a*ρ+b*ρ^2) := by
    have t := abs_sub_le Y (scaledCoeff (linearExp 0) ρ j) 0
    simp only [sub_zero] at t
    linarith [bound j]
  dsimp [Y,scaledCoeff] at y
  rw [abs_mul,abs_of_pos (pow_pos hr _),pow_succ] at y
  have c : ρ^j*|coeff j (linearExp a*(quadraticExp b*linearExp 0))| ≤ exp (a*ρ+b*ρ^2) :=
    le_of_mul_le_mul_left (a:=ρ) (by nlinarith only [y]) hr
  rw [labelCoefficient,abs_mul,abs_of_nonneg (by positivity : 0≤(j.factorial:ℝ)),le_div_iff₀ (pow_pos hr j)]
  nlinarith only [mul_le_mul_of_nonneg_left c (by positivity : (0:ℝ)≤j.factorial)]

#print axioms label_bounds
#print axioms coeff_bias_zero_label
end LongCycleBounds.MarkedTwo
