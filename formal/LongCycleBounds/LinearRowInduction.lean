import LongCycleBounds.BandEndpoint

namespace LongCycleBounds.Band
open Polynomial Finset LongCycles LongCycleFinite
noncomputable section

/-- An exact sign condition at every lower root propagates strict negative interlacing. -/
theorem linear_sturm_step {P Q : ℝ[X]} {e : ℕ} (r : Fin e → ℝ)
    (hf : P=∏ i, (X-C (r i))) (hm : StrictMono r) (hr : ∀ i, r i < 0)
    (hQ : Q.Monic) (hd : Q.natDegree=e+1) (hc : 0 < Q.eval 0)
    (test : ∀ t < 0, P.eval t=0 → Q.eval t*P.derivative.eval t < 0) :
    StrictNegativeInterlacing P Q e := by
  apply Sturm.strict_of_signs r hf hm hr (by rw [hQ.leadingCoeff]; norm_num) hd hc
  intro i
  have z : P.eval (r i)=0 := by
    rw [hf]
    exact Lagrange.eval_nodal_at_node (s:=univ) (v:=r) (mem_univ i)
  have nd := Sturm.node_derivative_sign r hm i
  rw [← hf] at nd
  have hp := mul_pos nd (neg_pos.mpr (test _ (hr i) z))
  have he : e-i.val=e-1-i.val+1 := by have := i.isLt; omega
  rw [he,pow_succ]
  by_contra! h
  nlinarith only [hp,mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg (P.derivative.eval (r i)))]

/-- Global induction from the one-cycle row; only admissible preceding rows are used. -/
theorem linear_induction {k : ℕ} (hk : 500000 ≤ k)
    (test : ∀ d : ℕ, 10000*d ≤ 2*k+d → ∀ t < (0:ℝ),
      (deformedRow (2*k+d-1) k 1).eval t = 0 →
      (deformedRow (2*k+d) k 1).eval t * (deformedRow (2*k+d-1) k 1).derivative.eval t < 0)
    (d : ℕ) (hw : 10000*d ≤ 2*k+d) :
    StrictNegativeInterlacing (deformedRow (2*k+d-1) k 1) (deformedRow (2*k+d) k 1) (2*k+d-3) := by
  induction d with
  | zero =>
    let e := 2*k-3
    have hP : deformedRow (2*k+0-1) k 1 = eulerian (e+1) := by
      have empty : Icc k (2*k-1-k) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      simp [deformedRow,empty,show 2*k-1-1=e+1 by dsimp [e]; omega]
    obtain ⟨r,hf,hm,hr⟩ := eulerian_simple_negative e
    have sq := deformed_shape (k:=k) (n:=2*k+0) (by omega) (by omega) (by omega) 1
    exact linear_sturm_step r (hP.trans hf) hm hr sq.2.1 (sq.1.trans (by dsimp [e]; omega))
      (by rw [sq.2.2]; norm_num) (test 0 hw)
  | succ d ih =>
    have prev := ih (by omega)
    let m := 2*k+d
    obtain ⟨_,v,_,_,_,fv,_,mv,_,nv,_⟩ := prev
    have sm := deformed_shape (k:=k) (n:=m) (by omega) (by dsimp [m]; omega) (by dsimp [m]; omega) 1
    change deformedRow m k 1 = C (deformedRow m k 1).leadingCoeff * _ at fv
    rw [sm.2.1.leadingCoeff, map_one,one_mul] at fv
    have sq := deformed_shape (k:=k) (n:=m+1) (by omega) (by dsimp [m];omega) (by dsimp [m];omega) 1
    have st := linear_sturm_step v fv mv nv sq.2.1 (sq.1.trans (by dsimp [m];omega))
      (by rw [sq.2.2]; norm_num) (by
        simpa only [Nat.add_succ,Nat.add_one_sub_one,m] using test (d+1) hw)
    simpa only [Nat.add_succ,Nat.add_one_sub_one,m,show 2*k+d+1-3=2*k+d-3+1 by omega] using st

#print axioms linear_induction

end
end LongCycleBounds.Band
