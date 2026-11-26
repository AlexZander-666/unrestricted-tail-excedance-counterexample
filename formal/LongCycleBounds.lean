import Mathlib

/-! Numerical and group-independent bounds in the first-split argument. -/
namespace LongCycleBounds

/-- The quotient of the central binomial coefficient by 4^k is decreasing. -/
theorem binomial_ratio_step (k : ℕ) :
    ((k+1).centralBinom : ℚ) / 4^(k+1) ≤ (k.centralBinom : ℚ) / 4^k := by
  have step : ((k : ℚ)+1) * ((k+1).centralBinom : ℚ) =
      2 * (2*(k:ℚ)+1) * (k.centralBinom : ℚ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have h : ((k+1).centralBinom : ℚ) ≤ 4 * (k.centralBinom : ℚ) := by
    apply le_of_mul_le_mul_left (a := (k:ℚ)+1) _ (by positivity)
    nlinarith [show (0 : ℚ) ≤ (k.centralBinom : ℚ) by positivity]
  rw [pow_succ]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith [mul_le_mul_of_nonneg_right h (by positivity : (0:ℚ) ≤ 4^k)])

theorem tail_normalization (k : ℕ) (hk : 5 ≤ k) :
    4 * ((k.centralBinom : ℚ) / 4^k) < 1 := by
  have anti : Antitone (fun j : ℕ => (j.centralBinom : ℚ)/4^j) := antitone_nat_of_succ_le binomial_ratio_step
  have h : (k.centralBinom : ℚ)/4^k ≤ ((5:ℕ).centralBinom : ℚ)/4^5 := anti hk
  have init : 4 * (((5:ℕ).centralBinom : ℚ) / 4^5) < 1 := by decide +kernel
  linarith

/-- Tail and bulk estimates use the same positive factors as the two normalized pole sums. -/
theorem bulk_ratio (k s : ℝ) (hk : 201 ≤ k) (hs : 0 < s) (hangle : 1 ≤ (2*k-1)*s^2) :
    81/(10*k*s) < 1 := by
  apply (div_lt_iff₀ (by positivity : 0 < 10*k*s)).mpr
  by_contra! bad
  have hb : 0 ≤ k*s := by positivity
  have sq : (k*s)^2 ≤ (81/10 : ℝ)^2 := by
    apply sq_le_sq' (by linarith) (by linarith)
  have h₁ := mul_le_mul_of_nonneg_left hangle (sq_nonneg k)
  have h₂ := mul_le_mul_of_nonneg_left sq (by linarith : 0 ≤ 2*k-1)
  nlinarith [sq_nonneg (k-201)]

theorem odd_tail_constants :
    3/16 + 4096 * ((1:ℚ)/5^7 + 1/(12*5^6)) < 1/3 ∧
    1+1/4 + 64 * ((1:ℚ)/5^4 + 1/(6*5^3)) < 3/2 ∧
    (1:ℚ)-2*(1/50)/(1-1/50)-2/7-2*((1-1/50)⁻¹^2-1) > 1/2 := by
  norm_num

/-- The phase subtraction leaves the tail bounded by the first power of the pole index. -/
theorem phase_error_squared (l s c : ℝ) (hl : 1 ≤ l) (hc : c^2+s^2=1) :
    (c*(l^2-1)*s)^2 + l^2 ≤ l^2*(1+(l^2-1)*s^2)^2 := by
  have h : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have key : l^2*(1+(l^2-1)*s^2)^2-((c*(l^2-1)*s)^2+l^2) =
      (l^2-1)*s^2*((l^2+1)+(l^2+1)*(l^2-1)*s^2) := by
    linear_combination -(l^2-1)^2*s^2*hc
  rw [← sub_nonneg,key]
  positivity

#print axioms tail_normalization
#print axioms bulk_ratio
#print axioms phase_error_squared

def alternating : List ℝ → ℝ
  | [] => 0
  | a :: l => a - alternating l

theorem alternating_bounds (l : List ℝ) (M : ℝ) (hM : 0 ≤ M)
    (sorted : (M::l).Pairwise (· ≥ ·)) (nonneg : ∀ x ∈ l, 0 ≤ x) :
    0 ≤ alternating l ∧ alternating l ≤ M := by
  induction l generalizing M with
  | nil => simpa [alternating] using hM
  | cons a l ih =>
    obtain ⟨top,rest⟩ := List.pairwise_cons.mp sorted
    have ham : a ≤ M := top a (by simp)
    obtain ⟨lb,ub⟩ := ih a (nonneg a (by simp)) rest (fun x hx => nonneg x (by simp [hx]))
    simp only [alternating]
    constructor <;> linarith

/-- Any finite interval of a nonnegative unimodal sequence has its signed
alternating sum bounded by the mode. Here the two tails are listed outwards. -/
theorem alternation_at_mode (left right : List ℝ) (M : ℝ) (hM : 0 ≤ M)
    (ls : (M::left).Pairwise (· ≥ ·)) (rs : (M::right).Pairwise (· ≥ ·))
    (ln : ∀ x ∈ left, 0 ≤ x) (rn : ∀ x ∈ right, 0 ≤ x) :
    |M - alternating left - alternating right| ≤ M := by
  obtain ⟨l₁,l₂⟩ := alternating_bounds left M hM ls ln
  obtain ⟨r₁,r₂⟩ := alternating_bounds right M hM rs rn
  rw [abs_le]
  constructor <;> linarith

#print axioms alternation_at_mode

end LongCycleBounds
