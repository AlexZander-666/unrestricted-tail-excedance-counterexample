import LongCycleFinite.Interlacing

namespace LongCycleFinite

open Polynomial

noncomputable section

def gammaArgument (t : ℝ) : ℝ := t / (1 + t) ^ 2

/-- Expand an ascending gamma row in the basis `X^i (1+X)^(d-2i)`. -/
def expandGamma (degree : ℕ) : List ℤ → Polynomial ℝ
  | [] => 0
  | a :: as => C (a : ℝ) * (1 + X) ^ degree + X * expandGamma (degree - 2) as

theorem eval_expandGamma (d : ℕ) (cs : List ℤ) (hd : 2 * (cs.length - 1) ≤ d)
    {t : ℝ} (ht : t ≠ -1) :
    (expandGamma d cs).eval t = (1 + t) ^ d * (ofCoeffs cs).eval (gammaArgument t) := by
  induction cs generalizing d with
  | nil => simp [expandGamma, ofCoeffs]
  | cons a as ih =>
    cases as with
    | nil => simp [expandGamma, ofCoeffs, mul_comm]
    | cons b bs =>
      have hd' : 2 * ((b :: bs).length - 1) ≤ d - 2 := by
        simp only [List.length_cons] at hd ⊢
        omega
      have h2 : 2 ≤ d := by simp only [List.length_cons] at hd; omega
      have ht' : 1 + t ≠ 0 := by intro hz; apply ht; linarith
      rw [expandGamma, ofCoeffs]
      simp only [eval_add, eval_C, eval_mul, eval_pow, eval_one, eval_X]
      rw [ih (d - 2) hd', mul_add, gammaArgument]
      generalize (ofCoeffs (b :: bs)).eval (t / (1 + t)^2) = v
      have he : (1 + t)^d = (1 + t)^(d - 2) * (1 + t)^2 := by
        rw [← pow_add, Nat.sub_add_cancel h2]
      rw [he]
      field_simp

/-- The inverse of the gamma argument on the negative half adjacent to zero. -/
def negLift (x : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * x)) / (1 + Real.sqrt (1 - 4 * x))

theorem negLift_range {x : ℝ} (hx : x < 0) : -1 < negLift x ∧ negLift x < 0 := by
  have hs : 1 < Real.sqrt (1 - 4 * x) := by
    have harg : (1 : ℝ) < 1 - 4 * x := by linarith
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (1 : ℝ)) harg
  have hd : 0 < 1 + Real.sqrt (1 - 4 * x) := by positivity
  rw [negLift, lt_div_iff₀ hd, div_lt_iff₀ hd]
  constructor <;> linarith

theorem negLift_strictMono : StrictMonoOn negLift (Set.Iio 0) := by
  intro x hx y hy hxy
  have hy' : y < 0 := hy
  have h : Real.sqrt (1 - 4 * y) < Real.sqrt (1 - 4 * x) := by
    apply Real.sqrt_lt_sqrt <;> linarith
  unfold negLift
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem gammaArgument_negLift {x : ℝ} (hx : x < 0) : gammaArgument (negLift x) = x := by
  have hs : 0 ≤ 1 - 4 * x := by linarith
  have he := Real.sq_sqrt hs
  have hn : 1 + Real.sqrt (1 - 4 * x) ≠ 0 := by positivity
  unfold gammaArgument negLift
  have hplus : 1 + (1 - Real.sqrt (1 - 4 * x)) / (1 + Real.sqrt (1 - 4 * x)) =
      2 / (1 + Real.sqrt (1 - 4 * x)) := by field_simp; ring
  rw [hplus]
  field_simp
  nlinarith

theorem gammaArgument_inv {t : ℝ} (ht0 : t ≠ 0) (ht : t ≠ -1) :
    gammaArgument t⁻¹ = gammaArgument t := by
  have hs : 1 + t ≠ 0 := by intro he; apply ht; linarith
  have he : 1 + t⁻¹ = (1 + t) / t := by field_simp; ring
  rw [gammaArgument, he, div_pow]
  unfold gammaArgument
  field_simp

#print axioms eval_expandGamma
#print axioms negLift_range
#print axioms negLift_strictMono
#print axioms gammaArgument_negLift
#print axioms gammaArgument_inv

end

end LongCycleFinite
