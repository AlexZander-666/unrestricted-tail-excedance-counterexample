import LongCycleBounds.PoleBridge
import LongCycleBounds.EulerianSeries

namespace LongCycleBounds
noncomputable section

private theorem factorial_split (k : ℕ) (hk : 1 ≤ k) :
    ((2*k).choose k : ℝ) * ((k-1).factorial : ℝ)^2 * k =
      2 * ((2*k-1).factorial : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 2*k) (k := k) (by omega)
  have sub : 2*k-k=k := by omega
  rw [sub] at h
  have fac (n : ℕ) (hn : 1 ≤ n) : n.factorial = n*(n-1).factorial := by
    cases n with
    | zero => omega
    | succ n => exact Nat.factorial_succ n
  rw [fac k hk, fac (2*k) (by omega)] at h
  have h' : ((2*k).choose k:ℝ) * (k*((k-1).factorial:ℝ)) *
      (k*((k-1).factorial:ℝ)) = 2*k*((2*k-1).factorial:ℝ) := by exact_mod_cast h
  apply mul_right_cancel₀ (show (k:ℝ) ≠ 0 by exact_mod_cast (by omega : k ≠ 0))
  linarith only [show ((2*k).choose k:ℝ) * ((k-1).factorial:ℝ)^2*k*k =
    2*((2*k-1).factorial:ℝ)*k by linear_combination h']

/-- The central-region perturbation bound, for the original descent polynomials. -/
theorem firstSplitBulkBound55 (k : ℕ) (hk : 55 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (upper : x ≤ 5/2*Real.sqrt (2*k-2 : ℕ))
    (zero : (LongCycles.eulerian (2*k-2)).eval (-Real.exp (-x)) = 0) :
    ((2*k).choose k : ℝ)/2 * Real.exp (-x) *
        ((LongCycles.eulerian (k-1)).eval (-Real.exp (-x)))^2 <
      |(LongCycles.eulerian (2*k-1)).eval (-Real.exp (-x))| := by
  let u := Real.exp (-x)
  have hu : 0 < u := Real.exp_pos _
  have hh : 0 < 1+u := by linarith
  have jp : 2*k-2+1=2*k-1 := by omega
  have jk : k-1+1=k := by omega
  have jd : 2*k-1+1=2*k := by omega
  have orig := eulerian_eq_oddPoleSum (2*k-2) (by omega) x hx
  rw [zero, mul_zero, zero_div, Complex.ofReal_zero, jp] at orig
  have hz : oddPoleSum (2*k-1) x = 0 := by
    exact (mul_eq_zero.mp orig.symm).resolve_left (by exact_mod_cast (Nat.factorial_ne_zero _))
  have main := PoleBridge.raw_bulk55 k hk x hx upper hz
  have eval (m : ℕ) (hm : 1 ≤ m) :
      (LongCycles.eulerian m).eval (-u) =
      -((m.factorial:ℝ) * (oddPoleSum (m+1) x).re * (1+u)^(m+1)/u) := by
    have id := congrArg Complex.re (eulerian_eq_oddPoleSum m hm x hx)
    change -u * _ / (1+u)^(m+1) = _ at id
    simp [Complex.mul_re] at id
    field_simp [hu.ne', hh.ne'] at id ⊢
    linarith only [id]
  rw [eval (k-1) (by omega), eval (2*k-1) (by omega), jk, jd,
    abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos hu,
    abs_of_pos (pow_pos hh _), abs_of_pos (by exact_mod_cast Nat.factorial_pos (2*k-1) :
      0 < ((2*k-1).factorial:ℝ))]
  have pw : ((1+u)^k)^2=(1+u)^(2*k) := by rw [← pow_mul, Nat.mul_comm]
  have f := factorial_split k (by omega)
  have bound := mul_lt_mul_of_pos_left main (show 0 < ((2*k).choose k:ℝ)*((k-1).factorial:ℝ)^2 by
    exact mul_pos (by exact_mod_cast Nat.choose_pos (show k ≤ 2*k by omega))
      (pow_pos (by exact_mod_cast Nat.factorial_pos _) _))
  rw [mul_assoc, ← mul_assoc _ (k:ℝ), f] at bound
  rw [neg_sq, div_pow, mul_pow, mul_pow, pw]
  field_simp [hu.ne']
  dsimp only [u] at bound hu ⊢
  nlinarith only [mul_lt_mul_of_pos_right bound hu]

theorem firstSplitBulkBound (k : ℕ) (hk : 201 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (upper : x ≤ 5/2*Real.sqrt (2*k-2 : ℕ))
    (zero : (LongCycles.eulerian (2*k-2)).eval (-Real.exp (-x)) = 0) :
    ((2*k).choose k : ℝ)/2 * Real.exp (-x) *
        ((LongCycles.eulerian (k-1)).eval (-Real.exp (-x)))^2 <
      |(LongCycles.eulerian (2*k-1)).eval (-Real.exp (-x))| := by
  exact firstSplitBulkBound55 k (by omega) x hx upper zero

#print axioms firstSplitBulkBound
end
end LongCycleBounds
