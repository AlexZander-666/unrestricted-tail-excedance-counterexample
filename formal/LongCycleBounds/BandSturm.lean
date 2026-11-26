import LongCycleBounds.BandShape

/-! Independent bounds on the two perturbations allow a two-leg deformation.
Each leg uses only signs at fixed negative points and the intermediate value theorem. -/

noncomputable section
namespace LongCycleBounds.Band
open Finset Polynomial LongCycles LongCycleFinite

private theorem gap_sign {d : ℕ} (r : Fin d → ℝ) (m : ℕ) (hm : m≤d) (t : ℝ)
    (hleft : ∀ j : Fin d, j.val < m → r j<t) (hright : ∀ j : Fin d, m≤j.val → t<r j) :
    0 < (-1:ℝ)^(d-m) * (∏ j, (X-C (r j))).eval t := by
  classical
  have hcard : (univ.filter (fun j : Fin d ↦ m≤j.val)).card=d-m := by
    by_cases h : m<d
    · have hf : (univ.filter (fun j : Fin d ↦ m≤j.val)) = Finset.Ici (⟨m,h⟩ : Fin d) := by
        ext j; simp; rfl
      rw [hf,Fin.card_Ici]
    · have hf : (univ.filter (fun j : Fin d ↦ m≤j.val)) = ∅ := by
        ext j; simp; omega
      rw [hf,card_empty]; omega
  have he : (∏ j : Fin d, (if m≤j.val then (-1:ℝ) else 1)) = (-1:ℝ)^(d-m) := by
    rw [← prod_filter,prod_const,hcard]
  rw [← he,eval_prod]
  simp only [eval_sub,eval_X,eval_C,← prod_mul_distrib]
  apply prod_pos
  intro j _
  by_cases h : m≤j.val
  · simpa [h] using hright j h
  · simp [h,sub_pos.mpr (hleft j (by omega))]

private theorem positive_transfer {a b c : ℝ} (hab : 0<a*b) (hbc : 0<b*c) : 0<a*c := by
  rcases mul_pos_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    rcases mul_pos_iff.mp hbc with ⟨hb',hc⟩ | ⟨hb',hc⟩ <;>
    first | exact mul_pos ha hc | exact mul_pos_of_neg_of_neg ha hc | linarith

private theorem opposite_sign (j : ℕ) {x y : ℝ} (hx : 0<(-1:ℝ)^(j+1)*x)
    (hy : 0<(-1:ℝ)^j*y) : x*y<0 := by
  have h := mul_pos hx hy
  have hsq : (-1:ℝ)^j*(-1)^j=1 := by rw [← mul_pow]; simp
  rw [pow_succ] at h
  calc
    x*y = -(((-1:ℝ)^j*(-1)*x)*((-1)^j*y)) := by
      calc
        x*y = (((-1:ℝ)^j*(-1)^j)*(x*y)) := by rw [hsq,one_mul]
        _ = _ := by ring
    _ < 0 := neg_neg_of_pos h

private theorem same_sign_on_path (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 1))
    (h : ∀ τ∈Set.Icc 0 1, f τ≠0) : 0<f 0*f 1 := by
  have h0 := h 0 ⟨le_rfl,zero_le_one⟩
  have h1 := h 1 ⟨zero_le_one,le_rfl⟩
  rcases lt_or_gt_of_ne h0 with h0'|h0' <;> rcases lt_or_gt_of_ne h1 with h1'|h1'
  · exact mul_pos_of_neg_of_neg h0' h1'
  · obtain ⟨u,hu,hz⟩ := intermediate_value_Icc zero_le_one hc
      (show 0∈Set.Icc (f 0) (f 1) from ⟨h0'.le,h1'.le⟩)
    exact (h u hu hz).elim
  · obtain ⟨u,hu,hz⟩ := intermediate_value_Icc' zero_le_one hc
      (show 0∈Set.Icc (f 1) (f 0) from ⟨h1'.le,h0'.le⟩)
    exact (h u hu hz).elim
  · exact mul_pos h0' h1'

/-- First keep the upper row fixed; then keep the final lower row fixed. Only the two legs
of the square require exclusion of common negative roots. -/
theorem interlace_two_legs {d : ℕ} (P Q : ℝ → ℝ[X])
    (hstart : StrictNegativeInterlacing (P 0) (Q 0) d)
    (hp0 : (P 0).Monic) (hq0 : (Q 0).Monic)
    (hp1 : (P 1).Monic) (hpd : (P 1).natDegree=d)
    (hq1 : (Q 1).Monic) (hqd : (Q 1).natDegree=d+1) (hqz : 0<(Q 1).eval 0)
    (hpc : ∀ t : ℝ, ContinuousOn (fun τ ↦ (P τ).eval t) (Set.Icc 0 1))
    (hqc : ∀ t : ℝ, ContinuousOn (fun τ ↦ (Q τ).eval t) (Set.Icc 0 1))
    (hfirst : ∀ τ∈Set.Icc 0 1, ∀ t<0, (Q 0).eval t=0 → (P τ).eval t≠0)
    (hsecond : ∀ τ∈Set.Icc 0 1, ∀ t<0, (P 1).eval t=0 → (Q τ).eval t≠0) :
    StrictNegativeInterlacing (P 1) (Q 1) d := by
  classical
  obtain ⟨r,s,_,_,hpr,hqs,hrm,hsm,hrn,hsn,hinter⟩ := hstart
  simp only [hp0.leadingCoeff,hq0.leadingCoeff,C_1,one_mul] at hpr hqs
  have hz (i : Fin (d+1)) : (Q 0).eval (s i)=0 := by
    rw [hqs]
    exact Lagrange.eval_nodal_at_node (s := univ) (v := s) (mem_univ i)
  have hsg (i : Fin (d+1)) : 0 < (-1:ℝ)^(d-i.val)*(P 1).eval (s i) := by
    apply positive_transfer (b := (P 0).eval (s i))
    · rw [hpr]
      apply gap_sign r i.val (by omega)
      · intro j hj
        exact (hinter j).2.trans_le (hsm.monotone (show j.succ ≤ i from hj))
      · intro j hj
        exact (hsm.monotone (show i ≤ j.castSucc from hj)).trans_lt (hinter j).1
    · exact same_sign_on_path _ (hpc _) (fun τ hτ ↦ hfirst τ hτ _ (hsn i) (hz i))
  have hroot (i : Fin d) : ∃ u, s i.castSucc<u ∧ u<s i.succ ∧ (P 1).eval u=0 := by
    apply root_between _ (hsm Fin.castSucc_lt_succ)
    apply opposite_sign (d-i.val-1)
    · simpa only [Fin.val_castSucc,show d-i.val-1+1=d-i.val by have := i.isLt;omega] using hsg i.castSucc
    · simpa [Nat.sub_sub] using hsg i.succ
  choose u hu using hroot
  have um : StrictMono u := fun i j hij ↦
    ((hu i).2.1.trans_le (hsm.monotone (show i.succ ≤ j.castSucc from hij))).trans (hu j).1
  have un (i : Fin d) : u i < 0 := (hu i).2.1.trans (hsn i.succ)
  have hfu := factor_of_degree_bound u hp1.ne_zero hpd.le um.injective fun i ↦ (hu i).2.2
  simp only [hp1.leadingCoeff,C_1,one_mul] at hfu
  apply Sturm.strict_of_signs u hfu um un (by rw [hq1.leadingCoeff]; exact zero_lt_one) hqd hqz
  intro i
  apply positive_transfer (b := (Q 0).eval (u i))
  · rw [hqs]
    have he : d-i.val = d+1-(i.val+1) := by omega
    rw [he]
    apply gap_sign s (i.val+1) (by omega)
    · intro j hj
      exact (hsm.monotone (show j ≤ i.castSucc from by change j.val ≤ i.val;omega)).trans_lt (hu i).1
    · intro j hj
      exact (hu i).2.1.trans_le (hsm.monotone (show i.succ≤j from hj))
  · exact same_sign_on_path _ (hqc _) (fun τ hτ ↦ hsecond τ hτ _ (un i) (hu i).2.2)

#print axioms interlace_two_legs
end LongCycleBounds.Band
