import LongCycleBounds.Sturm
import LongCycleBounds.OriginalRoots

/-! Strict interlacing of the ordinary Eulerian rows and of the perturbed first-split row. -/

namespace LongCycleBounds
noncomputable section
open Polynomial Finset LongCycles LongCycleFinite

theorem eulerian_at_zero (n : ℕ) : (eulerian n).eval 0 = 1 := by
  induction n with
  | zero => simp [longEulerian_zero]
  | succ n ih => simp [longEulerian_succ n, ih]

/-- Complement of the permutation identifies the top and constant coefficients. -/
theorem eulerian_degree_monic (n : ℕ) :
    (eulerian (n+1)).natDegree = n ∧ (eulerian (n+1)).Monic := by
  classical
  have hd : (eulerian (n+1)).natDegree ≤ n := by
    unfold eulerian
    apply natDegree_sum_le_of_forall_le
    intro σ _
    apply (natDegree_X_pow_le _).trans
    have := complement_descents σ
    omega
  let e : Equiv.Perm (Equiv.Perm (Fin (n+1))) :=
    ⟨fun σ ↦ σ.trans Fin.revPerm, fun σ ↦ σ.trans Fin.revPerm,
     fun σ ↦ by apply Equiv.ext; intro i; exact Fin.rev_rev _,
     fun σ ↦ by apply Equiv.ext; intro i; exact Fin.rev_rev _⟩
  have hc : (eulerian (n+1)).coeff n = (eulerian (n+1)).coeff 0 := by
    unfold eulerian
    simp only [finsetSum_coeff]
    rw [← Equiv.sum_comp e (fun σ ↦ ((X : ℝ[X])^descents σ).coeff 0)]
    apply sum_congr rfl
    intro σ _
    change ((X : ℝ[X])^descents σ).coeff n =
      ((X : ℝ[X])^descents (σ.trans Fin.revPerm)).coeff 0
    have h := complement_descents σ
    simp only [coeff_X_pow]
    split_ifs <;> first | rfl | omega
  rw [coeff_zero_eq_eval_zero, eulerian_at_zero] at hc
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero hd (hc ▸ one_ne_zero),
    monic_of_natDegree_le_of_coeff_eq_one n hd hc⟩

private theorem eval_node {d : ℕ} (r : Fin d → ℝ) {p : ℝ[X]}
    (hf : p = ∏ j, (X - C (r j))) (i : Fin d) : p.eval (r i) = 0 := by
  rw [hf]
  exact Lagrange.eval_nodal_at_node (s := univ) (v := r) (mem_univ i)

private theorem successor_sign {d : ℕ} (r : Fin d → ℝ)
    (hf : eulerian (d+1) = ∏ j, (X-C (r j))) (hm : StrictMono r) (hn : ∀ i, r i < 0)
    (i : Fin d) : 0 < (-1 : ℝ)^(d-i.val)*(eulerian (d+1+1)).eval (r i) := by
  have hz := eval_node r hf i
  have hder := Sturm.node_derivative_sign r hm i
  rw [← hf] at hder
  have he : d-i.val = (d-1-i.val)+1 := by have := i.isLt; omega
  rw [longEulerian_succ (d+1),eval_add,eval_mul,eval_mul,eval_mul,hz,mul_zero,zero_add,
    eval_X,eval_sub,eval_X,eval_one,he,pow_succ]
  calc
    0 < (-(r i) * (1 - r i)) * ((-1 : ℝ)^(d-1-i.val) *
        (eulerian (d+1)).derivative.eval (r i)) :=
      mul_pos (mul_pos (neg_pos.mpr (hn i)) (by linarith [hn i])) hder
    _ = _ := by ring

private theorem eulerian_step {d : ℕ} (r : Fin d → ℝ)
    (hf : eulerian (d+1) = ∏ j, (X-C (r j))) (hm : StrictMono r) (hn : ∀ i, r i < 0) :
    StrictNegativeInterlacing (eulerian (d+1)) (eulerian (d+1+1)) d := by
  obtain ⟨hd,hmon⟩ := eulerian_degree_monic (d+1)
  apply Sturm.strict_of_signs r hf hm hn (hmon.leadingCoeff ▸ zero_lt_one) hd
    ((eulerian_at_zero _).symm ▸ zero_lt_one)
  exact successor_sign r hf hm hn

/-- Complete monic factorization with an increasing list of strictly negative distinct roots. -/
theorem eulerian_simple_negative (d : ℕ) : ∃ r : Fin d → ℝ,
    eulerian (d+1) = ∏ j, (X-C (r j)) ∧ StrictMono r ∧ ∀ i, r i < 0 := by
  induction d with
  | zero =>
    refine ⟨Fin.elim0, ?_, fun ⦃i⦄ ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
    simp [longEulerian_one]
  | succ d ih =>
    obtain ⟨r,hf,hm,hn⟩ := ih
    obtain ⟨_,s,_,_,_,hs,_,hm',_,hn',_⟩ := eulerian_step r hf hm hn
    refine ⟨s,?_,hm',hn'⟩
    simpa [(eulerian_degree_monic (d+1)).2.leadingCoeff] using hs

theorem eulerian_consecutive_strict (d : ℕ) :
    StrictNegativeInterlacing (eulerian (d+1)) (eulerian (d+1+1)) d := by
  obtain ⟨r,hf,hm,hn⟩ := eulerian_simple_negative d
  exact eulerian_step r hf hm hn

private theorem firstQ_shape (k : ℕ) (hk : 3 ≤ k) :
    (firstQ k).natDegree = 2*k-2 ∧ (firstQ k).Monic ∧ (firstQ k).eval 0 = 1 := by
  let d := 2*k-2
  have hb : d+1 = 2*k-1 := by dsimp [d]; omega
  obtain ⟨hbd,hbm⟩ := eulerian_degree_monic d
  rw [hb] at hbd hbm
  have ha := (eulerian_degree_monic (k-2)).1
  rw [show k-2+1 = k-1 by omega] at ha
  let c : ℝ := (((2*k).choose k / 2 : ℕ) : ℝ)
  have hsmall : (C c*X*(eulerian (k-1))^2).natDegree < (eulerian (2*k-1)).natDegree := by
    calc
      _ ≤ (C c*X).natDegree + ((eulerian (k-1))^2).natDegree := natDegree_mul_le
      _ ≤ ((C c).natDegree+X.natDegree) + 2*(eulerian (k-1)).natDegree :=
        Nat.add_le_add natDegree_mul_le (natDegree_pow_le)
      _ < _ := by rw [natDegree_C,natDegree_X,ha,hbd]; dsimp [d]; omega
  exact ⟨(natDegree_add_eq_left_of_natDegree_lt hsmall).trans hbd,
    hbm.add_of_left (degree_lt_degree hsmall),
    by simp [firstQ,eulerian_at_zero]⟩

theorem firstSplit55_strict (k : ℕ) (hk : 55 ≤ k) :
    StrictNegativeInterlacing (firstP k) (firstQ k) (2*k-3) := by
  let d := 2*k-3
  have hp : d+1 = 2*k-2 := by dsimp [d]; omega
  have hb : d+1+1 = 2*k-1 := by dsimp [d]; omega
  obtain ⟨r,hf,hm,hn⟩ := eulerian_simple_negative d
  have hfp : firstP k = ∏ j, (X-C (r j)) := by simpa only [firstP,← hp] using hf
  obtain ⟨hqd,hqm,hq0⟩ := firstQ_shape k (by omega)
  apply Sturm.strict_of_signs r hfp hm hn (hqm.leadingCoeff ▸ zero_lt_one) (hqd.trans hp.symm)
    (hq0.symm ▸ zero_lt_one)
  intro i
  have hs := successor_sign r hf hm hn i
  rw [hb] at hs
  have hBQ := firstQ_sameSign55 k hk (hn i) (eval_node r hfp i)
  rcases mul_pos_iff.mp hs with ⟨hs,hb⟩ | ⟨hs,hb⟩ <;>
    rcases mul_pos_iff.mp hBQ with ⟨hb',hq⟩ | ⟨hb',hq⟩ <;>
    first | exact mul_pos hs hq | exact mul_pos_of_neg_of_neg hs hq | linarith

theorem large_firstSplit_strict (k : ℕ) (hk : 201 ≤ k) :
    StrictNegativeInterlacing (firstP k) (firstQ k) (2*k-3) := by
  exact firstSplit55_strict k (by omega)

#print axioms eulerian_simple_negative
#print axioms eulerian_consecutive_strict
#print axioms firstSplit55_strict
#print axioms large_firstSplit_strict
end
end LongCycleBounds
