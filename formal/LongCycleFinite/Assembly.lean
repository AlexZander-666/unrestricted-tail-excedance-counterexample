import LongCycleFinite.CoefficientRows
import LongCycleFinite.LiftRoots

namespace LongCycleFinite

open Polynomial

theorem weak_mul_X_of_strict {p q : Polynomial ℝ} {d : ℕ}
    (h : StrictNegativeInterlacing p q d) : LongCycles.WeakRealInterlacing (X * p) (X * q) := by
  obtain ⟨r, s, hp, hq, hpf, hqf, hr, hs, hnr, hns, hi⟩ := h
  let re : Fin (d + 1) → ℝ := Fin.lastCases 0 r
  let se : Fin (d + 1 + 1) → ℝ := Fin.lastCases 0 s
  have monoAppend {n : ℕ} {f : Fin n → ℝ} (hf : StrictMono f) (hn : ∀ i, f i < 0) :
      Monotone (Fin.lastCases 0 f) := by
    intro i j hij
    revert hij
    refine Fin.lastCases ?_ (fun b ↦ ?_) j
    · intro _
      refine Fin.lastCases ?_ (fun a ↦ ?_) i
      · simp
      · simpa using (hn a).le
    · refine Fin.lastCases ?_ (fun a ↦ ?_) i
      · intro hh
        have hab := b.isLt
        have hh' : n ≤ b.val := by simpa only [Fin.le_def, Fin.val_last, Fin.val_castSucc] using hh
        exact (by omega : False).elim
      · intro hab
        simpa using hf.monotone (Fin.castSucc_le_castSucc_iff.mp hab)
  refine ⟨d + 1, re, se, p.leadingCoeff, q.leadingCoeff, hp, hq, ?_, ?_,
    monoAppend hr hnr, monoAppend hs hns, ?_⟩
  · conv_lhs => rw [hpf]
    conv_rhs => rw [LongCycles.linearFactors, Fin.prod_univ_castSucc]
    simp only [re, Fin.lastCases_castSucc, Fin.lastCases_last, C_0, sub_zero]
    ring
  · conv_lhs => rw [hqf]
    conv_rhs => rw [LongCycles.linearFactors, Fin.prod_univ_castSucc]
    simp only [se, Fin.lastCases_castSucc, Fin.lastCases_last, C_0, sub_zero]
    ring
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have he : (Fin.last d).succ = Fin.last (d + 1) := rfl
      simpa only [re, se, Fin.lastCases_castSucc, Fin.lastCases_last, he, le_refl, and_true]
        using (hns (Fin.last d)).le
    · have he : j.castSucc.succ = j.succ.castSucc := rfl
      simpa only [re, se, Fin.lastCases_castSucc, he] using ⟨(hi j).1.le, (hi j).2.le⟩

/-- A checked gamma certificate and two integer coefficient identities give
strict negative interlacing of the quotients of the original rows. -/
theorem firstSplitStrict_of_checked {k : ℕ} (hk : 3 ≤ k) {p q : List ℤ} {outer : Dyadic}
    {ws : List Window} (hw : ws.length = k - 2) (hcheck : caseOK p q outer ws = true)
    (hp : expandCoeffs (2 * k - 3) p = descentCoeffs (2 * k - 2))
    (hq : expandCoeffs (2 * k - 2) q = qCoeffs k) :
    StrictNegativeInterlacing (firstP k) (firstQ k) (2 * k - 3) := by
  have hpart : (boundaryOK p q outer ws.length = true ∧ orderOK outer ws = true) ∧
      signsOK p q ws.length ws = true := by
    simpa only [caseOK, Bool.and_eq_true_iff] using hcheck
  have hlength : p.length = ws.length + 1 ∧ q.length = ws.length + 2 := by
    have hb := hpart.1.1
    simp only [boundaryOK, Bool.and_eq_true_iff, decide_eq_true_eq] at hb
    exact hb.1.1.1
  have hs := caseOK_sound (show 0 < ws.length by omega) hcheck
  have hexp := expandGamma_interlacing hlength.1 hlength.2 hs
  have hdp : ws.length + ws.length + 1 = 2 * k - 3 := by omega
  have hdq : ws.length + ws.length + 1 + 1 = 2 * k - 2 := by omega
  have hfp : expandGamma (2 * k - 3) p = firstP k := by
    rw [← ofCoeffs_expandCoeffs, hp, ofCoeffs_descentCoeffs]
    rfl
  have hfq : expandGamma (2 * k - 2) q = firstQ k := by
    rw [← ofCoeffs_expandCoeffs, hq, ofCoeffs_qCoeffs]
  rw [hdq, hdp, hfp, hfq] at hexp
  exact hexp

theorem firstSplit_of_checked {k : ℕ} (hk : 3 ≤ k) {p q : List ℤ} {outer : Dyadic}
    {ws : List Window} (hw : ws.length = k - 2) (hcheck : caseOK p q outer ws = true)
    (hp : expandCoeffs (2 * k - 3) p = descentCoeffs (2 * k - 2))
    (hq : expandCoeffs (2 * k - 2) q = qCoeffs k) :
    LongCycles.WeakRealInterlacing (LongCycles.enumerator (2 * k - 1) k)
      (LongCycles.enumerator (2 * k) k) := by
  obtain ⟨ha, hb⟩ := firstSplit_quotients k (by omega)
  rw [ha, hb]
  exact weak_mul_X_of_strict (firstSplitStrict_of_checked hk hw hcheck hp hq)

#print axioms weak_mul_X_of_strict
#print axioms firstSplitStrict_of_checked
#print axioms firstSplit_of_checked

end LongCycleFinite
