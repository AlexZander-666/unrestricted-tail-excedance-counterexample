import LongCycleBounds.MarkedTwoCycles
import LongCycleBounds.GeneralCycleQuotient
import LongCycleBounds.RootHomotopy

noncomputable section
namespace LongCycleBounds.MarkedTwo
open Finset Polynomial Insertion LongCycles Band LongCycleFinite
open scoped Classical

def markedQuotient (n : ℕ) (u : ℝ) : ℝ[X] := (row n u).divX

private theorem coeff_row (n m : ℕ) (u : ℝ) :
    (row n u).coeff m = ∑ a : Admissible n 2, u^(twos a.val)*(X^(excedances a.val):ℝ[X]).coeff m := by
  rw [row_admissible,finsetSum_coeff]
  simp only [term,coeff_C_mul]

private theorem coeff_mono (n m : ℕ) {u v : ℝ} (u0 : 0≤u) (uv : u≤v) :
    (row n u).coeff m≤(row n v).coeff m := by
  rw [coeff_row,coeff_row]
  apply sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ u0 uv _)
  simp only [coeff_X_pow]
  split <;> norm_num

theorem continuous_marked_coeff (n m : ℕ) : Continuous fun u ↦ (markedQuotient n u).coeff m := by
  simp only [markedQuotient,coeff_divX,coeff_row]
  fun_prop

theorem markedQuotient_endpoints {n : ℕ} (hn : 3≤n) :
    markedQuotient n 0=generalCycleQuotient n 3 ∧ markedQuotient n 1=generalCycleQuotient n 2 := by
  have drop (p : ℝ[X]) : (X*p).divX=p := by ext j;simp
  simp [markedQuotient,row_zero,row_one,actual_general_cycle_row (n:=n) (k:=2) (by decide) (by omega),
    actual_general_cycle_row (n:=n) (k:=3) (by decide) (by omega),drop]

theorem markedQuotient_shape {n : ℕ} (hn : 3≤n) {u : ℝ} (hu : u∈Set.Icc 0 1) :
    (markedQuotient n u).natDegree=n-2 ∧ (markedQuotient n u).Monic ∧
      (markedQuotient n u).eval 0=1 ∧ row n u=X*markedQuotient n u := by
  have part := markedQuotient_endpoints hn
  have ends (i : ℕ) :
      (generalCycleQuotient n 3).coeff i≤(markedQuotient n u).coeff i ∧
      (markedQuotient n u).coeff i≤(generalCycleQuotient n 2).coeff i := by
    rw [←part.1,←part.2]
    exact ⟨by simpa [markedQuotient] using coeff_mono n (i+1) le_rfl hu.1,
      by simpa [markedQuotient] using coeff_mono n (i+1) hu.1 hu.2⟩
  have s2 := generalCycleQuotient_shape (n:=n) (k:=2) (by decide) (by omega)
  have s3 := generalCycleQuotient_shape (n:=n) (k:=3) (by decide) (by omega)
  have top := ends (n-2)
  have lead : (markedQuotient n u).coeff (n-2)=1 := by
    rw [←s3.1,s3.2.1.coeff_natDegree,s3.1,←s2.1,s2.2.1.coeff_natDegree,s2.1] at top
    exact le_antisymm top.2 top.1
  have degree : (markedQuotient n u).natDegree≤n-2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have bound := ends i
    rw [coeff_eq_zero_of_natDegree_lt (s2.1.trans_lt hi),coeff_eq_zero_of_natDegree_lt (s3.1.trans_lt hi)] at bound
    exact le_antisymm bound.2 bound.1
  have z := ends 0
  simp only [coeff_zero_eq_eval_zero,s2.2.2,s3.2.2] at z
  have bot : (row n u).coeff 0=0 := by
    have a := coeff_mono n 0 le_rfl hu.1
    have b := coeff_mono n 0 hu.1 hu.2
    rw [row_zero,actual_general_cycle_row (by decide : 2≤3) (by omega : 0<n)] at a
    rw [row_one,actual_general_cycle_row (by decide : 2≤2) (by omega : 0<n)] at b
    simp only [coeff_X_mul_zero] at a b
    exact le_antisymm b a
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero degree (by simp [lead]),
    monic_of_natDegree_le_of_coeff_eq_one _ degree lead,le_antisymm z.2 z.1,
    by simpa [markedQuotient,bot] using (X_mul_divX_add (row n u)).symm⟩

theorem marked_coeff_nonneg (n m : ℕ) {u : ℝ} (hu : 0≤u) : 0≤(markedQuotient n u).coeff m := by
  rw [markedQuotient,coeff_divX,coeff_row]
  apply sum_nonneg
  intro a _
  apply mul_nonneg (pow_nonneg hu _)
  simp only [coeff_X_pow]
  split <;> norm_num

theorem marked_neg_roots {n : ℕ} (hn : 3≤n) {u : ℝ} (hu : u∈Set.Icc 0 1) (t : ℝ)
    (root : (markedQuotient n u).IsRoot t) : t<0 := by
  by_contra! pos
  let p := markedQuotient n u
  have z : p.coeff 0=1 := (coeff_zero_eq_eval_zero _).trans (markedQuotient_shape hn hu).2.2.1
  have one := single_le_sum (s:=range (p.natDegree+1)) (f:=fun i ↦ p.coeff i*t^i)
    (fun i _ ↦ mul_nonneg (marked_coeff_nonneg n i hu.1) (pow_nonneg pos _)) (a:=0) (by simp)
  rw [←eval_eq_sum_range,z,pow_zero,mul_one] at one
  exact (not_lt_of_ge one) (by rw [show p.eval t=0 from root];norm_num)

theorem continuous_marked_eval {n : ℕ} (hn : 3≤n) (x : ℝ) :
    Continuous fun u : Set.Icc (0:ℝ) 1 ↦ (markedQuotient n u).eval x := by
  have eq (u : Set.Icc (0:ℝ) 1) := eval_eq_sum_range' (p:=markedQuotient n u) (n:=n)
    (by rw [(markedQuotient_shape hn u.2).1];omega) x
  simp_rw [eq]
  exact continuous_finsetSum _ (fun i _ ↦ ((continuous_marked_coeff n i).comp continuous_subtype_val).mul continuous_const)

theorem continuous_marked_aeval {n : ℕ} (hn : 3≤n) (x : ℂ) :
    Continuous fun u : Set.Icc (0:ℝ) 1 ↦ (markedQuotient n u).aeval x := by
  have eq (u : Set.Icc (0:ℝ) 1) : (markedQuotient n u).aeval x =
      ∑ i∈range n, ((markedQuotient n u).coeff i:ℂ)*x^i := by
    exact eval₂_eq_sum_range' (algebraMap ℝ ℂ) (by rw [(markedQuotient_shape hn u.2).1];omega) x
  simp_rw [eq]
  exact continuous_finsetSum _ (fun i _ ↦ (Complex.continuous_ofReal.comp ((continuous_marked_coeff n i).comp continuous_subtype_val)).mul continuous_const)

/-- The actual parameter-weighted rows inherit strict interlacing from the derivative sign. -/
theorem marked_interlacing_of_sign {n : ℕ} (hn : 4≤n)
    (seed : (generalCycleQuotient (n-1) 2).Splits)
    (sign : ∀ u∈Set.Icc (0:ℝ) 1, ∀ t<0, (markedQuotient (n-1) u).eval t=0 →
      (markedQuotient n u).eval t*(markedQuotient (n-1) u).derivative.eval t<0) :
    ∀ u∈Set.Icc (0:ℝ) 1,
      StrictNegativeInterlacing (markedQuotient (n-1) u) (markedQuotient n u) (n-3) ∧
        WeakRealInterlacing (row (n-1) u) (row n u) := by
  let P (u : Set.Icc (0:ℝ) 1) := markedQuotient (n-1) u
  let Q (u : Set.Icc (0:ℝ) 1) := markedQuotient n u
  have hp := fun u : Set.Icc (0:ℝ) 1 ↦ markedQuotient_shape (n:=n-1) (by omega) u.2
  have hq := fun u : Set.Icc (0:ℝ) 1 ↦ markedQuotient_shape (n:=n) (by omega) u.2
  have all := RootHomotopy.interlacing_of_connected_sign (d:=n-3) P Q
    (fun u ↦ (hp u).2.1) (fun u ↦ (hp u).1.trans (by omega))
    (continuous_marked_aeval (by omega)) (continuous_marked_eval (by omega))
    (fun u t ↦ marked_neg_roots (by omega) u.2 t) (fun u ↦ (hq u).2.1)
    (fun u ↦ (hq u).1.trans (by omega)) (fun u ↦ by change 0<(markedQuotient n u).eval 0;rw [(hq u).2.2.1];norm_num)
    (fun u ↦ sign u u.2) (by
      refine ⟨⟨1,by norm_num⟩,?_⟩
      change (markedQuotient (n-1) 1).Splits
      rwa [(markedQuotient_endpoints (by omega : 3≤n-1)).2])
  intro u hu
  have st := all ⟨u,hu⟩
  refine ⟨st,?_⟩
  rw [(markedQuotient_shape (by omega : 3≤n-1) hu).2.2.2,(markedQuotient_shape (by omega : 3≤n) hu).2.2.2]
  exact weak_mul_X_of_strict st

#print axioms marked_interlacing_of_sign

#print axioms markedQuotient_shape
end LongCycleBounds.MarkedTwo
