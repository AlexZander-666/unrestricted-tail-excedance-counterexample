import LongCycleBounds.BandSturm
import LongCycleBounds.BandMoments
import LongCycleFinite.Assembly

/-! The square-root-band claim reduced to a single explicit scalar analytic estimate. -/
namespace LongCycleBounds.Band
noncomputable section
open LongCycles LongCycleFinite Polynomial

/-- Only the two legs (u,0) and (1,v) of the deformation square are used. -/
def SeparatedOnLegs (n k : ℕ) : Prop :=
  ∀ u∈Set.Icc (0:ℝ) 1, ∀ v∈Set.Icc (0:ℝ) 1, (v=0 ∨ u=1) →
    ∀ x : ℝ, 0≤x →
      ¬((deformedRow (n-1) k u).eval (-Real.exp (-x))=0 ∧
        (deformedRow n k v).eval (-Real.exp (-x))=0)

private theorem whole_negative {n k : ℕ} (hk : 2≤k) (hkn : k≤n-1) (h : SeparatedOnLegs n k)
    (u v : ℝ) (hu : u∈Set.Icc 0 1) (hv : v∈Set.Icc 0 1) (hc : v=0 ∨ u=1)
    (t : ℝ) (ht : t<0) :
    ¬((deformedRow (n-1) k u).eval t=0 ∧ (deformedRow n k v).eval t=0) := by
  have unit (w : ℝ) (hw : w<0) (hlo : -1≤w) :
      ¬((deformedRow (n-1) k u).eval w=0 ∧ (deformedRow n k v).eval w=0) := by
    let x := -Real.log (-w)
    have hp : 0 < -w := by linarith
    have hx : 0≤x := neg_nonneg.mpr (Real.log_nonpos hp.le (by linarith))
    have he : -Real.exp (-x) = w := by dsimp only [x]; rw [neg_neg,Real.exp_log hp,neg_neg]
    simpa only [he] using h u hu v hv hc x hx
  by_cases hlo : -1≤t
  · exact unit t ht hlo
  · rintro ⟨hP,hQ⟩
    apply unit t⁻¹ (inv_lt_zero.mpr ht) (by rw [inv_eq_one_div,le_div_iff_of_neg ht];linarith)
    have h1 := deformed_reciprocity hk hkn u ht.ne
    have h2 := deformed_reciprocity hk (show k≤n by omega) v ht.ne
    rw [hP] at h1
    rw [hQ] at h2
    exact ⟨(mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ ht.ne),
      (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ ht.ne)⟩

private theorem eval_continuous (n k : ℕ) (t : ℝ) :
    ContinuousOn (fun τ : ℝ ↦ (deformedRow n k τ).eval t) (Set.Icc 0 1) := by
  simp only [deformedRow,eval_add,eval_mul,eval_C]
  fun_prop

/-- This is a conditional reduction of the positive-width band. SeparatedOnLegs is the
analytic exclusion that remains to be proved. Both permutation endpoints are exact. -/
theorem actual_adjacent_of_separated {n k d : ℕ} (hn : n=2*k+d) (hN : 402≤n)
    (hband : (d:ℝ)+1 ≤ Real.sqrt n / 400) (h : SeparatedOnLegs n k) :
    StrictNegativeInterlacing (deformedRow (n-1) k 1) (deformedRow n k 1) (n-3) ∧
    WeakRealInterlacing (enumerator (n-1) k) (enumerator n k) := by
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr (show 1 ≤ (n:ℝ) by exact_mod_cast (by omega : 1≤n)))
  have hd : 400*(d+1) ≤ n := by exact_mod_cast (show 400*((d:ℝ)+1)≤n by linarith)
  have hk : 2≤k := by omega
  have hkn : k≤n-1 := by omega
  have shP := deformed_shape hk hkn (by omega) (1:ℝ)
  have shQ := deformed_shape hk (show k≤n by omega) (by omega) (1:ℝ)
  have start : StrictNegativeInterlacing (deformedRow (n-1) k 0) (deformedRow n k 0) (n-3) := by
    simpa only [deformedRow_zero,show n-3+1=n-1-1 by omega,show n-1-1+1=n-1 by omega] using
      eulerian_consecutive_strict (n-3)
  have hz : (0:ℝ)∈Set.Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have ho : (1:ℝ)∈Set.Icc 0 1 := ⟨zero_le_one,le_rfl⟩
  have hi := interlace_two_legs (deformedRow (n-1) k) (deformedRow n k) start
    (deformed_shape hk hkn (by omega) 0).2.1 (deformed_shape hk (by omega : k≤n) (by omega) 0).2.1
    shP.2.1 (shP.1.trans (by omega)) shQ.2.1 (shQ.1.trans (by omega)) (by rw [shQ.2.2]; exact zero_lt_one)
    (eval_continuous _ _) (eval_continuous _ _)
    (fun u hu t ht hQ hP ↦ whole_negative hk hkn h u 0 hu hz (Or.inl rfl) t ht ⟨hP,hQ⟩)
    (fun v hv t ht hP hQ ↦ whole_negative hk hkn h 1 v ho hv (Or.inr rfl) t ht ⟨hP,hQ⟩)
  refine ⟨hi,?_⟩
  obtain ⟨hP,hQ⟩ := actual_adjacent hn hN hband
  rw [hP,hQ]
  exact weak_mul_X_of_strict hi

#print axioms actual_adjacent_of_separated
end
end LongCycleBounds.Band
