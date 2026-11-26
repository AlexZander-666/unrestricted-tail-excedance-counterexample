import LongCycleFinite.Arithmetic

namespace LongCycleFinite

open Polynomial

private def mulDown (x : Dyadic) (a : ℤ) : ℤ := (x.numer * a) >>> x.shift

private def mulUp (x : Dyadic) (a : ℤ) : ℤ := -((- (x.numer * a)) >>> x.shift)

private theorem mulDown_le (x : Dyadic) (a : ℤ) : (mulDown x a : ℝ) ≤ x.value * (a : ℝ) := by
  have hd : 0 < (2 : ℝ) ^ x.shift := by positivity
  rw [Dyadic.value, div_mul_eq_mul_div, le_div_iff₀ hd]
  have hn := Int.ediv_mul_le (x.numer * a) (b := (2 : ℤ) ^ x.shift) (by positivity)
  rw [mulDown, Int.shiftRight_eq_div_pow]
  exact_mod_cast hn

private theorem le_mulUp (x : Dyadic) (a : ℤ) : x.value * (a : ℝ) ≤ (mulUp x a : ℝ) := by
  have h := mulDown_le x (-a)
  rw [mulDown, mul_neg, Int.cast_neg, mul_neg] at h
  simpa only [mulUp, Int.cast_neg, neg_neg] using neg_le_neg h

private theorem cast_shift (a : ℤ) (n : ℕ) : ((a <<< n : ℤ) : ℝ) = (a : ℝ) * 2^n := by
  rw [Int.shiftLeft_eq]
  push_cast
  rfl

/-- A directed bound on `2^256` times the Horner value at a nonpositive point.
At a negative point the required direction alternates in the recursion. -/
def rounded (x : Dyadic) : Bool → List ℤ → ℤ
  | _, [] => 0
  | upper, a :: as => (a <<< (256 : ℕ)) +
      if upper then mulUp x (rounded x false as) else mulDown x (rounded x true as)

theorem rounded_sound (x : Dyadic) (hx : x.numer ≤ 0) (up : Bool) (cs : List ℤ) :
    if up then (2 : ℝ)^256 * (ofCoeffs cs).eval x.value ≤ (rounded x up cs : ℝ)
    else (rounded x up cs : ℝ) ≤ (2 : ℝ)^256 * (ofCoeffs cs).eval x.value := by
  have hv : x.value ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hx) (by positivity)
  induction cs generalizing up with
  | nil => simp [rounded, ofCoeffs]
  | cons a as ih =>
    have hlo : (rounded x false as : ℝ) ≤ (2 : ℝ)^256 * (ofCoeffs as).eval x.value := ih false
    have hhi : (2 : ℝ)^256 * (ofCoeffs as).eval x.value ≤ (rounded x true as : ℝ) := ih true
    cases up
    · simp only [rounded, Bool.false_eq_true, ↓reduceIte, Int.cast_add, cast_shift,
        ofCoeffs, eval_add, eval_C, eval_mul, eval_X]
      rw [mul_add, mul_left_comm ((2 : ℝ)^256), mul_comm ((2 : ℝ)^256) (a : ℝ)]
      apply add_le_add_right
      exact (mulDown_le x _).trans (mul_le_mul_of_nonpos_left hhi hv)
    · simp only [rounded, ↓reduceIte, Int.cast_add, cast_shift,
        ofCoeffs, eval_add, eval_C, eval_mul, eval_X]
      rw [mul_add, mul_left_comm ((2 : ℝ)^256), mul_comm ((2 : ℝ)^256) (a : ℝ)]
      apply add_le_add_right
      exact (mul_le_mul_of_nonpos_left hlo hv).trans (le_mulUp x _)

def roundedSign (negative : Bool) (cs : List ℤ) (x : Dyadic) : Bool :=
  decide (x.numer ≤ 0) &&
    if negative then decide (rounded x true cs < 0) else decide (0 < rounded x false cs)

theorem roundedSign_sound (negative : Bool) (cs : List ℤ) (x : Dyadic)
    (h : roundedSign negative cs x = true) :
    if negative then (ofCoeffs cs).eval x.value < 0 else 0 < (ofCoeffs cs).eval x.value := by
  rcases Bool.and_eq_true_iff.mp h with ⟨hx, hy⟩
  have hn : x.numer ≤ 0 := of_decide_eq_true hx
  have hp : 0 < (2 : ℝ)^256 := by positivity
  cases negative
  · have hl : (rounded x false cs : ℝ) ≤ (2 : ℝ)^256 * (ofCoeffs cs).eval x.value :=
      rounded_sound x hn false cs
    have hy' : 0 < (rounded x false cs : ℝ) := by exact_mod_cast (of_decide_eq_true hy)
    exact (mul_pos_iff_of_pos_left hp).mp (hy'.trans_le hl)
  · have hl : (2 : ℝ)^256 * (ofCoeffs cs).eval x.value ≤ (rounded x true cs : ℝ) :=
      rounded_sound x hn true cs
    have hy' : (rounded x true cs : ℝ) < 0 := by exact_mod_cast (of_decide_eq_true hy)
    exact ((mul_neg_iff.mp (hl.trans_lt hy')).resolve_right (fun hh ↦ hp.not_gt hh.1)).2

#print axioms rounded_sound
#print axioms roundedSign_sound

end LongCycleFinite
