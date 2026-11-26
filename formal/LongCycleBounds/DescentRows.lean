import LongCycles.Statement
import Cluster.EulerianInsertion

/-! Standardize the coefficient ring of the existing maximum-insertion theorem. -/

noncomputable section
namespace LongCycleBounds

open Polynomial
open ClusterGraphAudit.EulerianInsertion

/-- The two independent permutation definitions use the same adjacent-descent predicate. -/
theorem longEulerian_eq_map_row (n : ℕ) :
    LongCycles.eulerian n = (row n).map (Int.castRingHom ℝ) := by
  unfold LongCycles.eulerian row
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_pow, Polynomial.map_X]
  rfl

theorem longEulerian_zero : LongCycles.eulerian 0 = 1 := by
  rw [longEulerian_eq_map_row, row_zero, Polynomial.map_one]

theorem longEulerian_one : LongCycles.eulerian 1 = 1 := by
  rw [longEulerian_eq_map_row, row_one, Polynomial.map_one]

theorem longEulerian_succ (n : ℕ) :
    LongCycles.eulerian (n+1) =
      (1 + C (n : ℝ) * X) * LongCycles.eulerian n +
        X * (1-X) * derivative (LongCycles.eulerian n) := by
  rw [longEulerian_eq_map_row (n+1), ← row_succ, step, longEulerian_eq_map_row n]
  simp [Polynomial.derivative_map]

#print axioms longEulerian_succ
end LongCycleBounds
