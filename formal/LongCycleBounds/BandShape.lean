import LongCycleBounds.BandFormula
import LongCycleBounds.EulerianSturm

/-! Degree, endpoint and reciprocity are uniform over the entire real deformation. -/
namespace LongCycleBounds.Band
noncomputable section
open Finset Polynomial LongCycles

private theorem eulerian_shape {m : ℕ} (hm : 2 ≤ m) :
    (eulerian (m-1)).natDegree=m-2 ∧ (eulerian (m-1)).Monic := by
  simpa only [show m-2+1=m-1 by omega] using eulerian_degree_monic (m-2)

theorem deformed_shape {n k : ℕ} (hk : 2≤k) (hkn : k≤n) (hn : 3≤n) (τ : ℝ) :
    (deformedRow n k τ).natDegree = n-2 ∧ (deformedRow n k τ).Monic ∧
      (deformedRow n k τ).eval 0=1 := by
  have small : (C (τ/2)*∑ a ∈ Icc k (n-k),
      C (n.choose a : ℝ)*X*eulerian (a-1)*eulerian (n-a-1)).natDegree ≤ n-3 := by
    apply (natDegree_C_mul_le ..).trans
    apply natDegree_sum_le_of_forall_le
    intro a ha
    obtain ⟨hal,har⟩ := mem_Icc.mp ha
    calc
      _ ≤ (C (n.choose a : ℝ)*X*eulerian (a-1)).natDegree + (eulerian (n-a-1)).natDegree :=
        natDegree_mul_le
      _ ≤ ((C (n.choose a:ℝ)*X).natDegree+(eulerian (a-1)).natDegree) +
          (eulerian (n-a-1)).natDegree := Nat.add_le_add_right natDegree_mul_le _
      _ ≤ 1+(a-2)+(n-a-2) := by
        rw [(eulerian_shape (m := a) (by omega)).1,(eulerian_shape (m := n-a) (by omega)).1]
        exact Nat.add_le_add_right (Nat.add_le_add_right
          ((natDegree_C_mul_le ..).trans natDegree_X_le) _) _
      _ ≤ _ := by omega
  have ⟨deg,hmon⟩ := eulerian_shape (m := n) (by omega)
  have hd := small.trans_lt (show n-3<(eulerian (n-1)).natDegree by rw [deg]; omega)
  exact ⟨(natDegree_add_eq_left_of_natDegree_lt hd).trans deg,
    hmon.add_of_left (degree_lt_degree hd),by simp [deformedRow,eval_finsetSum,eulerian_at_zero]⟩

private theorem eulerian_inverse {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : t≠0) :
    t^(m-2)*(eulerian (m-1)).eval t⁻¹ = (eulerian (m-1)).eval t := by
  simpa only [show m-2+1=m-1 by omega] using eulerian_reciprocity (m-2) ht

theorem deformed_reciprocity {n k : ℕ} (hk : 2≤k) (hkn : k≤n) (τ : ℝ) {t : ℝ} (ht : t≠0) :
    t^(n-2)*(deformedRow n k τ).eval t⁻¹ = (deformedRow n k τ).eval t := by
  simp only [deformedRow,eval_add,eval_mul,eval_C,eval_finsetSum,eval_X,mul_add]
  rw [eulerian_inverse (m := n) (by omega) ht, mul_left_comm (t^_) (τ/2), mul_sum]
  congr 2
  apply sum_congr rfl
  intro a ha
  obtain ⟨hal,har⟩ := mem_Icc.mp ha
  let b := n-a
  have hb : 2≤b := by dsimp [b]; omega
  have he : n-2 = (a-2)+(b-2)+2 := by dsimp [b]; omega
  change t^(n-2)*((n.choose a:ℝ)*t⁻¹*(eulerian (a-1)).eval t⁻¹*(eulerian (b-1)).eval t⁻¹) =
      (n.choose a : ℝ)*t*(eulerian (a-1)).eval t*(eulerian (b-1)).eval t
  rw [he,pow_add,pow_add,← eulerian_inverse (m:=a) (by omega) ht,
    ← eulerian_inverse (m:=b) hb ht]
  field_simp

#print axioms deformed_shape
#print axioms deformed_reciprocity
end
end LongCycleBounds.Band
