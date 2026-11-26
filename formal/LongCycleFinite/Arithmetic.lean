import Mathlib

namespace LongCycleFinite

open Polynomial

/-- An exact rational with a denominator that is a power of two. -/
structure Dyadic where
  numer : ℤ
  shift : ℕ
  deriving Inhabited

namespace Dyadic

def zero : Dyadic := ⟨0, 0⟩

noncomputable def value (x : Dyadic) : ℝ := (x.numer : ℝ) / (2 : ℝ) ^ x.shift

@[simp] theorem value_zero : zero.value = 0 := by simp [zero, value]

def less (a b : Dyadic) : Bool :=
  decide ((a.numer <<< b.shift) < (b.numer <<< a.shift))

theorem less_iff (a b : Dyadic) : a.less b = true ↔ a.value < b.value := by
  simp only [less, decide_eq_true_eq, value, lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ b.shift)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ a.shift)]
  simp only [Int.shiftLeft_eq]
  exact_mod_cast (Iff.rfl :
    (a.numer : ℝ) * (2 : ℝ) ^ b.shift < (b.numer : ℝ) * (2 : ℝ) ^ a.shift ↔ _)

end Dyadic

/-- Interpret an ascending coefficient list as a real polynomial. -/
noncomputable def ofCoeffs : List ℤ → Polynomial ℝ
  | [] => 0
  | a :: as => C (a : ℝ) + X * ofCoeffs as

private def homogeneousAux (x : Dyadic) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | n, a :: as => (a <<< (x.shift * n)) + x.numer * homogeneousAux x (n - 1) as

/-- Integer Horner evaluation with denominator `2 ^ (x.shift * cs.length)`. -/
def homogeneous (x : Dyadic) (cs : List ℤ) : ℤ := homogeneousAux x cs.length cs

theorem homogeneous_eq_eval (x : Dyadic) (cs : List ℤ) :
    (homogeneous x cs : ℝ) = (2 : ℝ) ^ (x.shift * cs.length) * (ofCoeffs cs).eval x.value := by
  induction cs with
  | nil => simp [homogeneous, homogeneousAux, ofCoeffs]
  | cons a as ih =>
    change (↑((a <<< (x.shift * (as.length + 1))) + x.numer * homogeneous x as) : ℝ) = _
    rw [Int.shiftLeft_eq]
    push_cast
    rw [ih]
    simp only [List.length_cons, ofCoeffs, eval_add, eval_C, eval_mul, eval_X, Dyadic.value]
    rw [Nat.mul_succ, pow_add]
    have hd : (2 : ℝ) ^ x.shift ≠ 0 := by positivity
    field_simp

def positiveAt (negative : Bool) (cs : List ℤ) (x : Dyadic) : Bool :=
  if negative then decide (homogeneous x cs < 0) else decide (0 < homogeneous x cs)

theorem positiveAt_iff (negative : Bool) (cs : List ℤ) (x : Dyadic) :
    positiveAt negative cs x = true ↔
      if negative then (ofCoeffs cs).eval x.value < 0 else 0 < (ofCoeffs cs).eval x.value := by
  have hp : 0 < (2 : ℝ) ^ (x.shift * cs.length) := by positivity
  cases negative <;> simp only [positiveAt, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
  · rw [← Int.cast_pos (R := ℝ), homogeneous_eq_eval]
    exact mul_pos_iff_of_pos_left hp
  · rw [← Int.cast_lt (R := ℝ), Int.cast_zero, homogeneous_eq_eval]
    exact ⟨fun h ↦ (mul_neg_iff.mp h).elim (fun H ↦ H.2)
      (fun H ↦ ((not_lt_of_ge hp.le) H.1).elim), mul_neg_of_pos_of_neg hp⟩

#print axioms Dyadic.less_iff
#print axioms homogeneous_eq_eval
#print axioms positiveAt_iff

end LongCycleFinite
