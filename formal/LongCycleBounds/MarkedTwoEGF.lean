import LongCycleBounds.MarkedTwoCycles
import LongCycleBounds.DescentRows
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp

/-! The EGF of the genuine two-cycle-marked rows. All identities are formal
power series in the size variable, at arbitrary real excedance parameter. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open LongCycles Finset Polynomial
open scoped Classical

private theorem row_empty (u : ℝ) : row 0 u = 1 := by
  unfold row
  rw [Fintype.sum_unique]
  have e : (default : Equiv.Perm (Fin 0))=1 := Subsingleton.elim _ _
  simp [e,term,twos,excedances,Allowed]

/-- The derivative of the single-cycle EGF, before factorial normalization. -/
def cycleDerivativeCoeff (u t : ℝ) (d : ℕ) : ℝ :=
  if d=0 then 0 else (if d=1 then u else 1)*t*(eulerian d).eval t

theorem row_succ_eval (n : ℕ) (u t : ℝ) :
    (row (n+1) u).eval t = ∑ d ∈ range (n+1),
      ((n.choose d : ℕ):ℝ)*cycleDerivativeCoeff u t d*(row (n-d) u).eval t := by
  rw [row_anchored (Fin.last n) u, eval_finsetSum]
  simp only [eval_mul,eval_C,eval_X,Nat.add_sub_cancel]
  let w (d : ℕ) := ((n.choose d : ℕ):ℝ)*cycleDerivativeCoeff u t d*(row (n-d) u).eval t
  change _ = ∑ d ∈ range (n+1), w d
  have skip : ∑ d ∈ Icc 1 n, w d = ∑ d ∈ range (n+1), w d := by
    apply sum_subset
    · intro d h
      exact mem_range.mpr (by have := (mem_Icc.mp h).2;omega)
    · intro d h miss
      have eq : d=0 := by
        have := mem_range.mp h
        by_contra! ne
        exact miss (mem_Icc.mpr ⟨by omega,by omega⟩)
      simp [w,eq,cycleDerivativeCoeff]
  rw [←skip]
  refine sum_bij' (fun a _ ↦ a-1) (fun d _ ↦ d+1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro d hd
    have := mem_Icc.mp hd
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro a ha
    have := mem_Icc.mp ha
    omega
  · intro d _
    omega
  · intro a ha
    have := mem_Icc.mp ha
    have pos : a-1 ≠ 0 := by omega
    have sw : a-1=1 ↔ a=2 := by omega
    have tail : n+1-a = n-(a-1) := by omega
    simp [w,cycleDerivativeCoeff,pos,sw,tail,mul_assoc]

def egf (u t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ (row n u).eval t / n.factorial

def cycleDriver (u t : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ cycleDerivativeCoeff u t n / n.factorial

theorem egf_constant (u t : ℝ) : PowerSeries.coeff 0 (egf u t) = 1 := by
  simp [egf,PowerSeries.coeff_mk,row_empty]

theorem egf_derivative (u t : ℝ) :
    PowerSeries.derivative ℝ (egf u t) = cycleDriver u t * egf u t := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [egf,cycleDriver,PowerSeries.coeff_mk]
  rw [row_succ_eval,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have nz : (n:ℝ)+1≠0 := by positivity
  have fac : (n.factorial:ℝ)≠0 := by positivity
  rw [show ∀ a : ℝ, a/(((n:ℝ)+1)*n.factorial)*((n:ℝ)+1)=a/n.factorial by intro a;field_simp]
  rw [sum_div]
  apply sum_congr rfl
  intro d hd
  have le : d≤n := by have := mem_range.mp hd;omega
  have comb : (n.choose d:ℝ)*d.factorial*(n-d).factorial=n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial le
  have nf : (d.factorial:ℝ)≠0 := by positivity
  have mf : ((n-d).factorial:ℝ)≠0 := by positivity
  field_simp
  linear_combination (cycleDerivativeCoeff u t d * (row (n-d) u).eval t) * comb


open PowerSeries in
theorem cycleDriver_mark (u t : ℝ) :
    cycleDriver u t = cycleDriver 1 t + PowerSeries.C ((u-1)*t)*PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  rw [map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_X]
  by_cases hn : n=1
  · subst n
    simp [cycleDriver,cycleDerivativeCoeff,coeff_mk,LongCycleBounds.longEulerian_one]
    ring
  · by_cases h0 : n=0 <;> simp [cycleDriver,cycleDerivativeCoeff,coeff_mk,hn,h0]

/-- The exponential of v z², given directly by all its Taylor coefficients. -/
def quadraticExp (v : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ if n % 2 = 0 then v^(n/2)/(n/2).factorial else 0

private theorem quadratic_derivative (v : ℝ) :
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

/-- Coefficientwise uniqueness of the first-order formal EGF equation. -/
theorem driver_unique {A f g : PowerSeries ℝ}
    (f0 : PowerSeries.coeff 0 f = PowerSeries.coeff 0 g)
    (df : PowerSeries.derivative ℝ f = A*f)
    (dg : PowerSeries.derivative ℝ g = A*g) : f=g := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact f0
    | succ n =>
      have same : PowerSeries.coeff n (A*f)=PowerSeries.coeff n (A*g) := by
        rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
        apply sum_congr rfl
        intro ij hi
        obtain ⟨i,j⟩ := ij
        have eq : i+j=n := by simpa using hi
        rw [ih j (by omega)]
      rw [←df,←dg,PowerSeries.coeff_derivative,PowerSeries.coeff_derivative] at same
      exact mul_right_cancel₀ (by positivity : (n:ℝ)+1≠0) same

/-- The exact deformation of the derangement EGF by exp((u-1)t z²/2). -/
theorem egf_two_cycle_deformation (u t : ℝ) :
    egf u t = egf 1 t * quadraticExp ((u-1)*t/2) := by
  refine driver_unique (A:=cycleDriver u t) ?_ (egf_derivative u t) ?_
  · rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,egf_constant]
    simpa [quadraticExp,PowerSeries.coeff_mk] using (egf_constant 1 t).symm
  · rw [Derivation.leibniz,egf_derivative,quadratic_derivative,cycleDriver_mark u t]
    rw [show 2*((u-1)*t/2)=(u-1)*t by ring]
    simp only [smul_eq_mul]
    ring

#print axioms egf_derivative
#print axioms egf_two_cycle_deformation
end LongCycleBounds.MarkedTwo
