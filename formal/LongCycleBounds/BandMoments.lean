import LongCycleBounds.BandFormula
import LongCycleBounds.EulerianSeries

/-! Normalize the actual band rows to Eulerian moments, uniformly along the homotopy. -/

noncomputable section
namespace LongCycleBounds.Band
open LongCycles Polynomial Finset

/-- F with the order indexed by cycle size: moment a represents F_{a-1}. -/
def moment (a : ℕ) (t : ℝ) : ℝ := t*(eulerian (a-1)).eval t / (1-t)^a

/-- Multiplying the deformed row by the paper's signed prefactor gives exactly the
product of the two Eulerian moments in each ordered-support term. -/
theorem deformed_eval (n k : ℕ) (τ t : ℝ) (ht : t≠1) :
    t*(deformedRow n k τ).eval t / (1-t)^n =
    moment n t + τ/2 * ∑ a ∈ Icc k (n-k),
       (n.choose a : ℝ)*moment a t*moment (n-a) t := by
  simp only [deformedRow,eval_add,eval_mul,eval_C,eval_X,eval_finsetSum,mul_add,add_div]
  congr 1
  rw [show t*(τ/2 * ∑ a ∈ Icc k (n-k), (n.choose a : ℝ)*t*
        (eulerian (a-1)).eval t*(eulerian (n-a-1)).eval t) / (1-t)^n =
      τ/2*(∑ a ∈ Icc k (n-k), t / (1-t)^n * ((n.choose a : ℝ)*t*
        (eulerian (a-1)).eval t*(eulerian (n-a-1)).eval t)) by rw [← mul_sum]; ring]
  congr 1
  apply sum_congr rfl
  intro a ha
  have hab : a+(n-a)=n := by have := (mem_Icc.mp ha).2; omega
  have hp : (1-t)^n = (1-t)^a*(1-t)^(n-a) := by rw [← pow_add,hab]
  unfold moment
  rw [hp]
  field_simp [sub_ne_zero.mpr (Ne.symm ht)]
  
theorem moment_discrete (a : ℕ) (ha : 2≤a) (x : ℝ) (hx : 0<x) :
    moment a (-Real.exp (-x)) =
      ∑' h : ℕ, (-1 : ℝ)^h*h^(a-1)*Real.exp (-(x*(h : ℝ))) := by
  simpa only [moment,sub_neg_eq_add,show a-1+1=a by omega] using
    eulerian_eq_alternatingMoment (a-1) (by omega) x hx

theorem moment_poles (a : ℕ) (ha : 2≤a) (x : ℝ) (hx : 0≤x) :
    (moment a (-Real.exp (-x)) : ℂ) = (a-1).factorial * oddPoleSum a x := by
  simpa only [moment,sub_neg_eq_add,show a-1+1=a by omega] using
    eulerian_eq_oddPoleSum (a-1) (by omega) x hx

/-- The binomial support factor cancels exactly against both factorials. -/
theorem binomial_factorial_ratio {n a b : ℕ} (hn : a+b=n) (ha : 0<a) (hb : 0<b) :
    (n.choose a : ℝ)*(a-1).factorial*(b-1).factorial / (n-1).factorial =
      (n:ℝ)/((a:ℝ)*(b:ℝ)) := by
  have fac (j : ℕ) (hj : 0<j) : j.factorial = j*(j-1).factorial := by
    cases j with
    | zero => omega
    | succ j => simp [Nat.factorial_succ]
  have hc := Nat.choose_mul_factorial_mul_factorial (show a≤n by omega)
  rw [show n-a=b by omega,fac a ha,fac b hb,fac n (by omega)] at hc
  have he : (n.choose a : ℝ) * (a*(a-1).factorial) * (b*(b-1).factorial) =
      (n:ℝ)*(n-1).factorial := by exact_mod_cast hc
  field_simp
  linarith only [he]

/-- A real normalized moment. For the pole scale ρ this will be the real
part of the sum over the positive odd half-lattice. -/
def scaledMoment (r t : ℝ) (a : ℕ) : ℝ :=
  r^a*moment a t / (2*(a-1).factorial)

/-- For any real scale and x≥0 the normalized moment equals the real part of
the complete, symmetrically paired odd-pole expression, including x=0. -/
theorem scaledMoment_poles (a : ℕ) (ha : 2≤a) (x r : ℝ) (hx : 0≤x) :
    scaledMoment r (-Real.exp (-x)) a = r^a*(oddPoleSum a x).re/2 := by
  have h := congrArg Complex.re (moment_poles a ha x hx)
  simp [Complex.mul_re] at h
  rw [scaledMoment,h]
  field_simp

theorem scaled_deformed_eval {n k : ℕ} (hk : 2≤k) (hkn : k≤n) (τ r t : ℝ) (ht : t≠1) :
    r^n*(t*(deformedRow n k τ).eval t/(1-t)^n)/(2*(n-1).factorial) =
      scaledMoment r t n + τ*∑ a ∈ Icc k (n-k),
        (n:ℝ)/((a:ℝ)*((n-a:ℕ):ℝ)) * scaledMoment r t a * scaledMoment r t (n-a) := by
  rw [deformed_eval n k τ t ht,mul_add,add_div]
  congr 1
  rw [show r^n*(τ/2*∑ a ∈ Icc k (n-k), (n.choose a : ℝ)*moment a t*moment (n-a) t) /
        (2*(n-1).factorial) =
      τ*(∑ a ∈ Icc k (n-k), r^n/(4*(n-1).factorial)*
        ((n.choose a : ℝ)*moment a t*moment (n-a) t)) by rw [← mul_sum]; ring]
  congr 1
  apply sum_congr rfl
  intro a ha
  obtain ⟨hal,har⟩ := mem_Icc.mp ha
  let b := n-a
  have hab : a+b=n := by dsimp [b]; omega
  have fac := binomial_factorial_ratio hab (by omega) (by dsimp [b]; omega)
  change r^n / (4*(n-1).factorial) * ((n.choose a:ℝ)*moment a t*moment b t) =
      (n:ℝ)/((a:ℝ)*(b:ℝ))*scaledMoment r t a*scaledMoment r t b
  rw [← fac,scaledMoment,scaledMoment,show r^n = r^a*r^b by rw [← pow_add,hab]]
  field_simp
  ring

/-- The same parameterized family has the correct endpoint for both sizes in the
square-root band, including its left boundary d=0. -/
theorem actual_adjacent {n k d : ℕ} (hn : n=2*k+d) (hN : 402≤n)
    (hband : (d:ℝ)+1 ≤ Real.sqrt n / 400) :
    enumerator (n-1) k = X*deformedRow (n-1) k 1 ∧
      enumerator n k = X*deformedRow n k 1 := by
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr (show 1 ≤ (n:ℝ) by exact_mod_cast (by omega : 1≤n)))
  have hd : 400*(d+1) ≤ n := by exact_mod_cast (show 400*((d:ℝ)+1)≤n by linarith)
  exact ⟨actual_band_row (by omega) (by omega) (by omega),
    actual_band_row (by omega) (by omega) (by omega)⟩

#print axioms deformed_eval
#print axioms moment_discrete
#print axioms binomial_factorial_ratio
#print axioms scaledMoment_poles
#print axioms scaled_deformed_eval
#print axioms moment_poles
#print axioms actual_adjacent
end LongCycleBounds.Band
