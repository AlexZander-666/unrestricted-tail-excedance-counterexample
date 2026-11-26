import LongCycleBounds.MarkedQuotientHomotopy
import LongCycleBounds.InitialRows
import LongCycleBounds.UniversalRecurrence

noncomputable section
namespace LongCycleBounds.MarkedTwo
open Polynomial LongCycles LongCycleFinite Band Finset
open scoped Classical

private theorem preceding_product {d : ℕ} (a : Fin d → ℝ) (r : Fin (d+1) → ℝ)
    (inc : StrictMono r) (inter : ∀ j : Fin d,r j.castSucc<a j ∧ a j<r j.succ)
    (i : Fin (d+1)) :
    0<(∏ j,(X-C (a j) : ℝ[X])).eval (r i)*(∏ j,(X-C (r j) : ℝ[X])).derivative.eval (r i) := by
  rw [i.prod_univ_succAbove (fun j ↦ X-C (r j) : Fin (d+1) → ℝ[X]),derivative_mul]
  simp only [derivative_X_sub_C,one_mul,eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero,eval_prod]
  rw [←prod_mul_distrib]
  apply prod_pos
  intro j _
  by_cases h : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    exact mul_pos (sub_pos.mpr ((inter j).2.trans_le (inc.monotone (show j.succ ≤ i by change j.val < i.val at h;change j.val+1 ≤ i.val;omega)))) (sub_pos.mpr (inc h))
  · have hh : i≤j.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hh]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr ((inc.monotone hh).trans_lt (inter j).1))
      (sub_neg.mpr (inc (hh.trans_lt j.castSucc_lt_succ)))

private theorem quotient_one_cycle {j : ℕ} (lo : 2≤j) (hi : j<4) :
    generalCycleQuotient j 2=eulerian (j-1) := by
  apply mul_left_cancel₀ (X_ne_zero : (X:ℝ[X])≠0)
  rw [←actual_general_cycle_row (by decide : 2≤2) (by omega : 0<j),beforeSplitRow (by decide) lo (by omega)]

/-- Direct derangement anchor at the unit end of the two-cycle marking. -/
theorem derangement_strict (d : ℕ) :
    StrictNegativeInterlacing (generalCycleQuotient (d+2) 2) (generalCycleQuotient (d+3) 2) d := by
  induction d with
  | zero =>
    rw [quotient_one_cycle (by decide) (by decide),quotient_one_cycle (by decide) (by decide)]
    exact eulerian_consecutive_strict 0
  | succ d ih =>
    let A := generalCycleQuotient (d+2) 2
    let P := generalCycleQuotient (d+3) 2
    let Q := generalCycleQuotient (d+4) 2
    change StrictNegativeInterlacing A P d at ih
    change StrictNegativeInterlacing P Q (d+1)
    have mA := generalCycleQuotient_shape (n:=d+2) (k:=2) (by decide) (by omega)
    have mP := generalCycleQuotient_shape (n:=d+3) (k:=2) (by decide) (by omega)
    have mQ := generalCycleQuotient_shape (n:=d+4) (k:=2) (by decide) (by omega)
    obtain ⟨a,r,_,_,fa,fp,_,inc,_,neg,inter⟩ := ih
    rw [show A.leadingCoeff=1 from mA.2.1.leadingCoeff,map_one,one_mul] at fa
    rw [show P.leadingCoeff=1 from mP.2.1.leadingCoeff,map_one,one_mul] at fp
    apply linear_sturm_step r fp inc neg mQ.2.1 (mQ.1.trans (by omega))
      (by rw [mQ.2.2];norm_num)
    intro t ht rt
    have find : ∃ i,r i=t := by
      have z := rt
      simp only [fp,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,mem_univ,true_and,sub_eq_zero] at z
      obtain ⟨j,h⟩ := z
      exact ⟨j,h.symm⟩
    obtain ⟨i,ri⟩ := find
    have pos : 0<A.eval t*P.derivative.eval t := by
      rw [←ri,fa,fp]
      exact preceding_product a r inc inter i
    have hp : enumerator (d+3) 2=X*P := actual_general_cycle_row (by decide) (by omega)
    have hq : enumerator (d+4) 2=X*Q := actual_general_cycle_row (by decide) (by omega)
    have ha : enumerator (d+2) 2=X*A := actual_general_cycle_row (by decide) (by omega)
    have eq := congrArg (fun p : ℝ[X] ↦ p.eval t) (Insertion.enumerator_succ (n:=d+3) (k:=2) (by decide))
    change (enumerator (d+4) 2).eval t=_ at eq
    rw [hp,hq,show d+3+1-2=d+2 by omega,ha] at eq
    simp only [show 2-1=1 by decide,longEulerian_one,Nat.choose_one_right,derivative_mul,derivative_X,one_mul,mul_one,
      eval_add,eval_mul,eval_sub,eval_one,eval_C,eval_X,rt,mul_zero,zero_add] at eq
    have atRoot : Q.eval t=t*(1-t)*P.derivative.eval t+((d+3:ℕ):ℝ)*t*A.eval t := by
      apply mul_left_cancel₀ ht.ne
      linear_combination eq
    rw [atRoot,add_mul]
    have x : t*(1-t)<0 := mul_neg_of_neg_of_pos ht (sub_pos.mpr (by linarith))
    have first : (t*(1-t)*P.derivative.eval t)*P.derivative.eval t≤0 := by
      rw [mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg x.le (mul_self_nonneg _)
    have last : (((d+3:ℕ):ℝ)*t*A.eval t)*P.derivative.eval t<0 := by
      rw [mul_assoc]
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) ht) pos
    linarith only [first,last]

#print axioms derangement_strict
end LongCycleBounds.MarkedTwo
