import LongCycleBounds.BandBinomial
import LongCycleBounds.Outer

/-! Uniform estimates for the individual ordered terms and the entire lower/current
row at an actual zero of its own deformation. -/
noncomputable section
namespace LongCycleBounds.Band
open Finset Real

private theorem moment_match (a : ℕ) (ha : 1≤a) (x : ℝ) (hx : 0<x) :
    moment a (-exp (-x)) = -Outer.moment (a-1) x := by
  rw [moment,outerMoment_eq_evaluation _ _ hx,show a-1+1=a by omega,sub_neg_eq_add]
  ring

theorem mode_product {A B j : ℕ} (hj : A+B+2=j) (hA : 2*j≤5*A) (hB : 2*j≤5*B)
    (x : ℝ) (hx : 0<x) :
    (j.choose (A+1):ℝ)*(|Outer.moment A x| *|Outer.moment B x|)*√(j:ℝ) ≤
      8*Outer.weight (j-2) x (Outer.mode (j-2) x hx) := by
  let i := Outer.mode A x hx
  let l := Outer.mode B x hx
  have hw := shifted_binomial_bound hj hA hB (u := (i:ℝ)+1) (v := (l:ℝ)+1)
    (by positivity) (by positivity)
  have hc := mul_le_mul_of_nonneg_right hw (pow_nonneg (exp_pos (-x)).le (i+1+(l+1)))
  have hshift : i+1+(l+1) = i+l+1+1 := by omega
  have hterm : (j.choose (A+1):ℝ)*(Outer.weight A x i*Outer.weight B x l)*√(j:ℝ) ≤
      8*Outer.weight (j-2) x (i+l+1) := by
    simp only [Outer.weight]
    rw [show j-2=A+B by omega]
    push_cast
    rw [show (i:ℝ)+l+1+1=(i+1)+(l+1) by ring,← hshift,pow_add (exp (-x)) (i+1) (l+1)]
    rw [pow_add (exp (-x)) (i+1) (l+1)] at hc
    linarith only [hc]
  apply le_trans _ (hterm.trans (mul_le_mul_of_nonneg_left (Outer.weight_le_mode ..) (by norm_num)))
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg j)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact mul_le_mul (Outer.signed_weight_bound A x hx) (Outer.signed_weight_bound B x hx)
    (abs_nonneg _) (Outer.weight_pos ..).le

/-- At a zero of a deformed row the single-cycle term is bounded by the
entire correction. The coefficient 4 includes the orientation division by two. -/
theorem row_outer_bound {j k : ℕ} (hk : 2≤k) (hkj : k≤j)
    (hbal : 2*j≤5*(k-1)) (x : ℝ) (hx : 0<x) {τ : ℝ} (hτ : |τ|≤1)
    (hz : (deformedRow j k τ).eval (-exp (-x))=0) :
    |Outer.moment (j-1) x| *√(j:ℝ) ≤
      4*((Icc k (j-k)).card:ℝ)*Outer.weight (j-2) x (Outer.mode (j-2) x hx) := by
  let t := -exp (-x)
  let W := Outer.weight (j-2) x (Outer.mode (j-2) x hx)
  let H (a : ℕ) := (j.choose a:ℝ)*moment a t*moment (j-a) t
  have eval := deformed_eval j k τ t (by dsimp [t]; linarith [exp_pos (-x)])
  rw [hz,mul_zero,zero_div] at eval
  change 0=moment j t + τ/2*∑ a ∈ Icc k (j-k), H a at eval
  have he : -(moment j t) = τ/2*∑ a ∈ Icc k (j-k), H a := by linarith only [eval]
  have ha (a : ℕ) (hm : a∈Icc k (j-k)) : |H a| *√(j:ℝ) ≤ 8*W := by
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hm
    have hb : k≤j-a := by omega
    dsimp only [H,t]
    rw [moment_match a (by omega) x hx,moment_match (j-a) (by omega) x hx,
      abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_neg,abs_neg]
    simpa only [show a-1+1=a by omega,mul_assoc] using
      mode_product (A := a-1) (B := j-a-1) (j := j) (by omega) (by omega) (by omega) x hx
  have hsum : |∑ a ∈ Icc k (j-k), H a| *√(j:ℝ) ≤ ((Icc k (j-k)).card:ℝ)*(8*W) := by
    calc
      _ ≤ (∑ a ∈ Icc k (j-k), |H a|)*√(j:ℝ) :=
        mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs ..) (sqrt_nonneg _)
      _ = _ := by rw [sum_mul]
      _ ≤ ∑ _a ∈ Icc k (j-k), 8*W := sum_le_sum ha
      _ = _ := by simp [nsmul_eq_mul]
  have he' := congrArg abs he
  rw [abs_neg,moment_match j (by omega) x hx,abs_neg,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at he'
  rw [he']
  have hcoef := mul_le_mul_of_nonneg_right (show |τ|/2 ≤ 1/2 by linarith)
    (mul_nonneg (abs_nonneg (∑ a ∈ Icc k (j-k), H a)) (sqrt_nonneg j))
  dsimp only [W] at *
  linarith only [hcoef,hsum]

/-- The exponent M mode gives an independent lower estimate for x. -/
private theorem mode_lower {M : ℕ} (x : ℝ) (hx : 0<x) :
    (M:ℝ) ≤ x*((Outer.mode M x hx:ℝ)+2) := by
  let i := Outer.mode M x hx
  let q : ℝ := 1+1/((i:ℝ)+1)
  have hq : 0<q := by dsimp [q]; positivity
  have hi := Outer.ratio_mode_le M x hx
  change q^M * exp (-x) ≤ 1 at hi
  have hl := log_le_log (mul_pos (pow_pos hq M) (exp_pos (-x))) hi
  rw [log_mul (pow_ne_zero _ hq.ne') (exp_ne_zero _),log_pow,log_exp,log_one] at hl
  have hlog := one_sub_inv_le_log_of_pos hq
  have eq : 1-q⁻¹ = 1/((i:ℝ)+2) := by dsimp [q];field_simp;ring
  rw [eq] at hlog
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M : (0:ℝ)≤_)
  change _ ≤ x*((i:ℝ)+2)
  apply (div_le_iff₀ (show 0<(i:ℝ)+2 by positivity)).mp
  linarith only [hl,hh,show (M:ℝ)/((i:ℝ)+2)=M*(1/((i:ℝ)+2)) by ring]

/-- For x>1 the positive-label peak moves by at most two when increasing the moment degree.
This gives the factor three needed to compare adjacent rows whose modes differ. -/
theorem adjacent_peak (M : ℕ) (x : ℝ) (hx : 1<x) :
    ((Outer.mode (M+1) x (by linarith):ℝ)+1)*
        Outer.weight M x (Outer.mode M x (by linarith)) ≤
      3*Outer.weight (M+1) x (Outer.mode (M+1) x (by linarith)) := by
  have xpos : 0<x := by linarith
  let i := Outer.mode M x xpos
  let j := Outer.mode (M+1) x xpos
  have h1 := mode_lower (M := M) x xpos
  have h2 := Outer.mode_index_mul_le (M+1) x xpos
  change (M:ℝ)≤x*((i:ℝ)+2) at h1
  change (j:ℝ)*x≤((M+1:ℕ):ℝ) at h2
  push_cast at h2
  have hij : j≤ i+2 := by
    by_contra! h
    have hnat : i+3≤j := by omega
    have hr : (i:ℝ)+3≤j := by exact_mod_cast hnat
    nlinarith only [h1,h2,mul_le_mul_of_nonneg_right hr xpos.le,hx]
  have hj : (j:ℝ)+1≤3*((i:ℝ)+1) := by
    have hr : (j:ℝ)≤ i+2 := by exact_mod_cast hij
    linarith [Nat.cast_nonneg i (α := ℝ)]
  have hg := Outer.weight_le_mode (M+1) x xpos i
  have he : Outer.weight (M+1) x i = ((i:ℝ)+1)*Outer.weight M x i := by
    simp only [Outer.weight,pow_succ ((i:ℝ)+1)]
    ring
  rw [he] at hg
  change ((j:ℝ)+1)*Outer.weight M x i ≤ _
  linarith only [hg,mul_le_mul_of_nonneg_right hj (Outer.weight_pos M x i).le]

#print axioms mode_product
#print axioms row_outer_bound
#print axioms adjacent_peak
end LongCycleBounds.Band
