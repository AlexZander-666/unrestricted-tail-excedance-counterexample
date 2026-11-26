import LongCycleBounds.BulkComplex
import LongCycleBounds.PartialFractions

namespace LongCycleBounds.PoleBridge
open ComplexConjugate PoleTails Bulk
open scoped Real

noncomputable section
def radius (x : ℝ) := Real.sqrt (x^2+π^2)
def c (x : ℝ) := x/radius x
def s (x : ℝ) := π/radius x

theorem radius_pos (x : ℝ) : 0 < radius x := by
  unfold radius
  positivity

theorem circle (x : ℝ) : c x ^2+s x ^2=1 := by
  have hr : radius x ^2 = x^2+π^2 := Real.sq_sqrt (by positivity)
  unfold c s
  field_simp [ne_of_gt (radius_pos x)]
  linarith

theorem angle_bound (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (upper : x ≤ 5/2*Real.sqrt N) :
    1 ≤ ((N:ℝ)+1)*s x^2 := by
  have hr : radius x ^2 = x^2+π^2 := Real.sq_sqrt (by positivity)
  have sq := mul_self_le_mul_self hx upper
  have hn : (Real.sqrt (N:ℝ))^2 = (N:ℝ) := Real.sq_sqrt (by positivity)
  have pi2 : 25/4 ≤ π^2 := by nlinarith [Real.pi_gt_three, sq_nonneg (π-3)]
  unfold s
  rw [div_pow]
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos (radius_pos x)), one_mul]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ N by positivity) (sub_nonneg.mpr pi2)]

private theorem polar (c s l : ℝ) (hu : c^2+s^2=1) (hl : 1 ≤ l) :
    pole c s l * ((c:ℂ)+ ((l*s:ℝ):ℂ)*Complex.I) = 1 := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have hd : 0 < 1+(l^2-1)*s^2 := by positivity
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pole] <;> field_simp <;> nlinarith [hu]

def den (x l : ℝ) : ℂ := (x:ℂ)+(l*π:ℝ)*Complex.I

theorem pole_den (x l : ℝ) (hl : 1 ≤ l) : pole (c x) (s x) l = (radius x : ℂ)/den x l := by
  have r : (radius x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (radius_pos x)
  have h0 := polar (c x) (s x) l (circle x) hl
  have h : den x l / (radius x : ℂ) = ((c x:ℝ):ℂ) + ((l*s x:ℝ):ℂ)*Complex.I := by
    unfold c s den
    push_cast
    ring
  rw [← h] at h0
  have hd : den x l ≠ 0 := by
    intro h
    simp [h] at h0
  apply (eq_div_iff hd).mpr
  field_simp [r] at h0
  exact h0

private theorem pair_conjugates (f : ℤ → ℂ) (hf : Summable (fun n : ℕ => f n))
    (pair : ∀ n : ℕ, f (-(n+1:ℤ)) = conj (f n)) :
    ∑' i : ℤ, f i = (2:ℂ)*(((∑' n : ℕ, f n).re : ℝ) : ℂ) := by
  have hc := Complex.summable_conj.mpr hf
  have hneg : Summable (fun n : ℕ => f (-(n+1:ℤ))) := by simpa only [pair] using hc
  have both := Summable.of_nat_of_neg_add_one hf hneg
  rw [← tsum_nat_add_neg_add_one both]
  simp only [pair, hf.tsum_add hc, ← Complex.conj_tsum]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.add_conj (∑' n : ℕ, f n)

private theorem conj_den (x l : ℝ) : conj (den x l) = den x (-l) := by
  apply Complex.ext <;> simp [den, Complex.add_re, Complex.add_im]

/-- The complete odd-lattice series, including both conjugate half-lattices. -/
theorem complete_normalization (x : ℝ) (p q : ℕ) (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s x^2)
    (hq : (p:ℝ) ≤ 2*(q:ℝ)) :
    ((radius x : ℂ)^q)*oddPoleSum q x = (2:ℂ)*((total (c x) (s x) q).re:ℂ) := by
  let f (i : ℤ) := ((radius x : ℂ)/den x (2*(i:ℝ)+1))^q
  have positive (n : ℕ) : f n = pole (c x) (s x) (2*n+1)^q := by
    dsimp only [f]
    push_cast
    have nonneg : 0 ≤ (n:ℝ) := by positivity
    rw [pole_den _ _ (by linarith)]
  have pair (n : ℕ) : f (-(n+1:ℤ)) = conj (f n) := by
    dsimp only [f]
    rw [map_pow, map_div₀, Complex.conj_ofReal, conj_den]
    congr 3
    push_cast
    ring
  obtain ⟨sp,he⟩ := positive_half _ _ p q (circle x) hp ha hq
  have sf : Summable (fun n : ℕ => f n) := by simpa only [positive] using sp
  have paired := pair_conjugates f sf pair
  simp only [positive, he] at paired
  rw [← paired]
  unfold oddPoleSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  dsimp only [f,den]
  push_cast
  rw [div_pow]
  ring

theorem scale55 (k : ℕ) (hk : 55≤k) (x : ℝ) (hx : 0≤x)
    (upper : x≤5/2*Real.sqrt (2*k-2:ℕ)) : 25/4 ≤ (k:ℝ)*s x := by
  have kr : (55:ℝ)≤k := by exact_mod_cast hk
  have hn : ((2*k-2:ℕ):ℝ)=2*(k:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2≤2*k)]
    push_cast;ring
  have sq := Real.sq_sqrt (show 0≤((2*k-2:ℕ):ℝ) by positivity)
  rw [hn] at sq upper
  have ux := sq_le_sq' (by linarith [Real.sqrt_nonneg (2*(k:ℝ)-2)] :
      -(5/2*Real.sqrt (2*(k:ℝ)-2))≤x) upper
  have hp : 9≤Real.pi^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have hpoly : 625*(x^2+Real.pi^2) ≤ 16*(k:ℝ)^2*Real.pi^2 := by
    have lower : 0≤16*(k:ℝ)^2-625 := by nlinarith [sq_nonneg ((k:ℝ)-55)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp) lower,
      mul_nonneg (sub_nonneg.mpr kr) (Nat.cast_nonneg k : (0:ℝ)≤_),kr,ux,sq]
  have hrad : (radius x)^2=x^2+Real.pi^2 := Real.sq_sqrt (by positivity)
  unfold s
  rw [← mul_div_assoc,le_div_iff₀ (radius_pos x)]
  by_contra! bad
  have cmp := mul_self_lt_mul_self (show 0≤(k:ℝ)*Real.pi by positivity) bad
  nlinarith only [cmp,hpoly,hrad]

theorem raw_bulk55 (k : ℕ) (hk : 55 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (upper : x ≤ 5/2*Real.sqrt (2*k-2 : ℕ))
    (hzero : oddPoleSum (2*k-1) x = 0) :
    ((oddPoleSum k x).re)^2 < (k:ℝ)*|(oddPoleSum (2*k) x).re| := by
  let p := 2*k-1
  have pe : p+1=2*k := by dsimp [p]; omega
  have hp : 8 ≤ (p:ℝ) := by exact_mod_cast (by dsimp [p]; omega : 8 ≤ p)
  have pre : (p:ℝ)+1=2*(k:ℝ) := by exact_mod_cast pe
  have ha : 1 ≤ (p:ℝ)*s x^2 := by
    have add : (2*k-2)+1=p := by dsimp [p]; omega
    have h := angle_bound x (2*k-2) hx upper
    simpa only [← Nat.cast_add_one, add] using h
  have real_norm (q : ℕ) (hq : (p:ℝ) ≤ 2*(q:ℝ)) :
      radius x ^ q * (oddPoleSum q x).re = 2*(total (c x) (s x) q).re := by
    have eq := congrArg Complex.re (complete_normalization x p q hp ha hq)
    simpa [Complex.mul_re, ← Complex.ofReal_pow] using eq
  have hz := real_norm p (by linarith)
  change oddPoleSum p x = 0 at hzero
  rw [hzero] at hz
  have z : (total (c x) (s x) p).re = 0 := by simpa using hz.symm
  have main := bulk_first_split_sharp (c x) (s x) k p pe hp (circle x) (by unfold s; exact div_pos Real.pi_pos (radius_pos _)) ha (scale55 k hk x hx upper) z
  rw [pe] at main
  have a := real_norm k (by linarith)
  have a2 := congrArg (fun t : ℝ => t^2) a
  change (radius x ^ k * (oddPoleSum k x).re)^2 = (2*(total (c x) (s x) k).re)^2 at a2
  have b := real_norm (2*k) (by push_cast; linarith)
  have b2 := congrArg abs b
  change |radius x ^ (2*k) * (oddPoleSum (2*k) x).re| = |2*(total (c x) (s x) (2*k)).re| at b2
  rw [abs_mul, abs_of_pos (pow_pos (radius_pos _) _), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at b2
  have id : (radius x ^ k)^2 = radius x^(2*k) := by rw [← pow_mul, Nat.mul_comm]
  rw [mul_pow,id] at a2
  apply lt_of_mul_lt_mul_left (a := radius x^(2*k)) _ (pow_pos (radius_pos x) _).le
  nlinarith [congrArg (fun t : ℝ => (k:ℝ)*t) b2]

theorem raw_bulk (k : ℕ) (hk : 201 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (upper : x ≤ 5/2*Real.sqrt (2*k-2 : ℕ))
    (hzero : oddPoleSum (2*k-1) x = 0) :
    ((oddPoleSum k x).re)^2 < (k:ℝ)*|(oddPoleSum (2*k) x).re| := by
  exact raw_bulk55 k (by omega) x hx upper hzero

#print axioms raw_bulk
#print axioms complete_normalization
end
end LongCycleBounds.PoleBridge
