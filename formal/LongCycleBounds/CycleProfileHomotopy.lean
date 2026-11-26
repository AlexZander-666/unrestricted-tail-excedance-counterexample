import LongCycleBounds.CycleProfile
import LongCycleBounds.DerangementAnchor

/-! The interval of common short-cycle weights and its unweighted derangement anchor. -/

noncomputable section

namespace LongCycleBounds.CycleProfile

open Finset Polynomial Insertion LongCycles Band LongCycleFinite
open scoped Classical

/-- Remove the common zero root from a genuine row with common short-cycle weight \(u\). -/
def quotient (n k : ℕ) (u : ℝ) : ℝ[X] := (row n (profile k u)).divX

private theorem product_profile (m : Multiset ℕ) (k : ℕ) (u : ℝ) :
    (m.map (profile k u)).prod = u ^ (m.filter (· < k)).card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases h : a < k <;> simp [profile, h, ih, pow_succ, mul_comm]

private theorem coeff_row (n k m : ℕ) (u : ℝ) :
    (row n (profile k u)).coeff m =
      ∑ a : Admissible n 2, u ^ (a.val.cycleType.filter (· < k)).card *
        (X ^ (excedances a.val) : ℝ[X]).coeff m := by
  rw [row_admissible, finsetSum_coeff]
  simp only [term, coeff_C_mul, cycleWeight, product_profile]

private theorem coeff_mono (n k m : ℕ) {u v : ℝ} (u0 : 0 ≤ u) (uv : u ≤ v) :
    (row n (profile k u)).coeff m ≤ (row n (profile k v)).coeff m := by
  rw [coeff_row, coeff_row]
  apply sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ u0 uv _)
  simp only [coeff_X_pow]
  split <;> norm_num

theorem continuous_quotient_coeff (n k m : ℕ) :
    Continuous fun u ↦ (quotient n k u).coeff m := by
  simp only [quotient, coeff_divX, coeff_row]
  fun_prop

/-- The values at the endpoints are the original quotients for cutoffs \(k\) and \(2\). -/
theorem quotient_endpoints {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    quotient n k 0 = generalCycleQuotient n k ∧
      quotient n k 1 = generalCycleQuotient n 2 := by
  have drop (p : ℝ[X]) : (X * p).divX = p := by ext j; simp
  simp only [quotient, row_zero n hk, row_one,
    actual_general_cycle_row hk hn, actual_general_cycle_row (by decide : 2 ≤ 2) hn, drop,
    and_self]

/-- Both endpoints determine the degree, leading coefficient, constant coefficient and
common zero factor throughout the closed interval of weights. -/
theorem quotient_shape {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) :
    (quotient n k u).natDegree = n - 2 ∧ (quotient n k u).Monic ∧
      (quotient n k u).eval 0 = 1 ∧ row n (profile k u) = X * quotient n k u := by
  have part := quotient_endpoints hk (by omega : 0 < n)
  have ends (i : ℕ) :
      (generalCycleQuotient n k).coeff i ≤ (quotient n k u).coeff i ∧
        (quotient n k u).coeff i ≤ (generalCycleQuotient n 2).coeff i := by
    rw [← part.1, ← part.2]
    exact ⟨by simpa [quotient] using coeff_mono n k (i + 1) le_rfl hu.1,
      by simpa [quotient] using coeff_mono n k (i + 1) hu.1 hu.2⟩
  have s2 := generalCycleQuotient_shape (n := n) (k := 2) (by decide) (by omega)
  have sk := generalCycleQuotient_shape hk hn
  have top := ends (n - 2)
  have lead : (quotient n k u).coeff (n - 2) = 1 := by
    rw [← sk.1, sk.2.1.coeff_natDegree, sk.1, ← s2.1, s2.2.1.coeff_natDegree, s2.1] at top
    exact le_antisymm top.2 top.1
  have degree : (quotient n k u).natDegree ≤ n - 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have bound := ends i
    rw [coeff_eq_zero_of_natDegree_lt (s2.1.trans_lt hi),
      coeff_eq_zero_of_natDegree_lt (sk.1.trans_lt hi)] at bound
    exact le_antisymm bound.2 bound.1
  have z := ends 0
  simp only [coeff_zero_eq_eval_zero, s2.2.2, sk.2.2] at z
  have bot : (row n (profile k u)).coeff 0 = 0 := by
    have a := coeff_mono n k 0 le_rfl hu.1
    have b := coeff_mono n k 0 hu.1 hu.2
    rw [row_zero n hk, actual_general_cycle_row hk (by omega : 0 < n)] at a
    rw [row_one, actual_general_cycle_row (by decide : 2 ≤ 2) (by omega : 0 < n)] at b
    simp only [coeff_X_mul_zero] at a b
    exact le_antisymm b a
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero degree (by simp [lead]),
    monic_of_natDegree_le_of_coeff_eq_one _ degree lead, le_antisymm z.2 z.1,
    by simpa [quotient, bot] using (X_mul_divX_add (row n (profile k u))).symm⟩

theorem quotient_coeff_nonneg (n k m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (quotient n k u).coeff m := by
  rw [quotient, coeff_divX, coeff_row]
  apply sum_nonneg
  intro a _
  apply mul_nonneg (pow_nonneg hu _)
  simp only [coeff_X_pow]
  split <;> norm_num

/-- There are no nonnegative real roots, including at endpoints of the weight interval. -/
theorem quotient_neg_roots {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {t : ℝ} (root : (quotient n k u).IsRoot t) : t < 0 := by
  by_contra! pos
  let p := quotient n k u
  have z : p.coeff 0 = 1 := (coeff_zero_eq_eval_zero _).trans (quotient_shape hk hn hu).2.2.1
  have one := single_le_sum (s := range (p.natDegree + 1)) (f := fun i ↦ p.coeff i * t ^ i)
    (fun i _ ↦ mul_nonneg (quotient_coeff_nonneg n k i hu.1) (pow_nonneg pos _)) (a := 0)
    (by simp)
  rw [← eval_eq_sum_range, z, pow_zero, mul_one] at one
  exact (not_lt_of_ge one) (by rw [show p.eval t = 0 from root]; norm_num)

private theorem continuous_quotient_eval {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) (x : ℝ) :
    Continuous fun u : Set.Icc (0 : ℝ) 1 ↦ (quotient n k u).eval x := by
  have eq (u : Set.Icc (0 : ℝ) 1) := eval_eq_sum_range' (p := quotient n k u) (n := n)
    (by rw [(quotient_shape hk hn u.2).1]; omega) x
  simp_rw [eq]
  exact continuous_finsetSum _ (fun i _ ↦
    ((continuous_quotient_coeff n k i).comp continuous_subtype_val).mul continuous_const)

private theorem continuous_quotient_aeval {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) (x : ℂ) :
    Continuous fun u : Set.Icc (0 : ℝ) 1 ↦ (quotient n k u).aeval x := by
  have eq (u : Set.Icc (0 : ℝ) 1) : (quotient n k u).aeval x =
      ∑ i ∈ range n, ((quotient n k u).coeff i : ℂ) * x ^ i := by
    exact eval₂_eq_sum_range' (algebraMap ℝ ℂ) (by rw [(quotient_shape hk hn u.2).1]; omega) x
  simp_rw [eq]
  exact continuous_finsetSum _ (fun i _ ↦
    (Complex.continuous_ofReal.comp
      ((continuous_quotient_coeff n k i).comp continuous_subtype_val)).mul continuous_const)

/-- The polynomial sign at each negative predecessor root transports interlacing across
the entire closed interval of weights, starting at the derangement endpoint \(u=1\). -/
theorem interlacing_of_sign {n k : ℕ} (hk : 3 ≤ k) (hkn : k < n)
    (sign : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t < 0, (quotient (n - 1) k u).eval t = 0 →
      (quotient n k u).eval t * (quotient (n - 1) k u).derivative.eval t < 0) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      StrictNegativeInterlacing (quotient (n - 1) k u) (quotient n k u) (n - 3) ∧
        WeakRealInterlacing (row (n - 1) (profile k u)) (row n (profile k u)) := by
  have hk2 : 2 ≤ k := by omega
  have hp := fun u : Set.Icc (0 : ℝ) 1 ↦ quotient_shape (n := n - 1) hk2 (by omega) u.2
  have hq := fun u : Set.Icc (0 : ℝ) 1 ↦ quotient_shape (n := n) hk2 hkn.le u.2
  let P (u : Set.Icc (0 : ℝ) 1) := quotient (n - 1) k u
  let Q (u : Set.Icc (0 : ℝ) 1) := quotient n k u
  have seed : (generalCycleQuotient (n - 1) 2).Splits := by
    obtain ⟨_, _, _, _, _, fac, _, _, _, _, _⟩ := MarkedTwo.derangement_strict (n - 4)
    rw [show n - 4 + 3 = n - 1 by omega] at fac
    rw [fac]
    exact Splits.mul (Splits.C _) (Splits.prod (fun _ _ ↦ Splits.X_sub_C _))
  have all := RootHomotopy.interlacing_of_connected_sign (d := n - 3) P Q
    (fun u ↦ (hp u).2.1) (fun u ↦ (hp u).1.trans (by omega))
    (continuous_quotient_aeval hk2 (by omega)) (continuous_quotient_eval hk2 (by omega))
    (fun u _ ↦ quotient_neg_roots hk2 (by omega) u.2) (fun u ↦ (hq u).2.1)
    (fun u ↦ (hq u).1.trans (by omega))
    (fun u ↦ by change 0 < (quotient n k u).eval 0; rw [(hq u).2.2.1]; norm_num)
    (fun u ↦ sign u u.2) (by
      refine ⟨⟨1, by norm_num⟩, ?_⟩
      change (quotient (n - 1) k 1).Splits
      rwa [(quotient_endpoints hk2 (by omega : 0 < n - 1)).2])
  intro u hu
  have st := all ⟨u, hu⟩
  refine ⟨st, ?_⟩
  rw [(hp ⟨u, hu⟩).2.2.2, (hq ⟨u, hu⟩).2.2.2]
  exact weak_mul_X_of_strict st

#print axioms quotient_endpoints
#print axioms quotient_shape
#print axioms quotient_neg_roots
#print axioms interlacing_of_sign

end LongCycleBounds.CycleProfile
