import LongCycleBounds

/-! A discrete telescope controls the non-leading odd poles. -/
namespace LongCycleBounds.PoleTails

noncomputable def envelope (l : ℝ) : ℝ := 8/(l^2+7)

private theorem odd_step (y : ℝ) (hy : 0 ≤ y) :
    (y+5) * envelope (y+5)^4 ≤ 2/(y+3)^3 - 2/(y+5)^3 ∧
    envelope (y+5)^2 ≤ 1/(2*(y+3)) - 1/(2*(y+5)) := by
  have h₁ : 0 < (y+5)^2+7 := by positivity
  have h₂ : 0 < y+3 := by positivity
  have h₃ : 0 < y+5 := by positivity
  constructor <;> unfold envelope <;> field_simp <;> rw [← sub_nonneg] <;> ring_nf <;> positivity

private theorem telescope (f g : ℕ → ℝ) (step : ∀ i, f i ≤ g i - g (i+1)) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i ≤ g 0 - g n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; linarith [step n]

theorem two_tails (n : ℕ) :
    (∑ j ∈ Finset.range n, (2*(j:ℝ)+5)*envelope (2*j+5)^4) ≤ 2/27 ∧
    (∑ j ∈ Finset.range n, envelope (2*(j:ℝ)+5)^2) ≤ 1/6 := by
  have h₁ (i : ℕ) := (odd_step (2*(i:ℝ)) (by positivity)).1
  have h₂ (i : ℕ) := (odd_step (2*(i:ℝ)) (by positivity)).2
  constructor
  · let g (j : ℕ) := 2/(2*(j:ℝ)+3)^3
    have step (i : ℕ) : (2*(i:ℝ)+5)*envelope (2*i+5)^4 ≤ g i - g (i+1) := by
      have shift : 2*((i+1 : ℕ) : ℝ)+3 = 2*(i:ℝ)+5 := by push_cast; ring
      simpa only [g,shift] using h₁ i
    have bound := telescope _ g step n
    have hn : 0 ≤ g n := by dsimp [g]; positivity
    have h0 : g 0 = 2/27 := by norm_num [g]
    exact bound.trans (by rw [h0]; linarith)
  · let g (j : ℕ) := 1/(2*(2*(j:ℝ)+3))
    have step (i : ℕ) : envelope (2*(i:ℝ)+5)^2 ≤ g i - g (i+1) := by
      have shift : 2*((i+1 : ℕ) : ℝ)+3 = 2*(i:ℝ)+5 := by push_cast; ring
      simpa only [g,shift] using h₂ i
    have bound := telescope _ g step n
    have hn : 0 ≤ g n := by dsimp [g]; positivity
    have h0 : g 0 = 1/6 := by norm_num [g]
    exact bound.trans (by rw [h0]; linarith)

theorem odd_pole_bounds (n : ℕ) :
    3 * envelope 3^4 + (∑ j ∈ Finset.range n, (2*(j:ℝ)+5)*envelope (2*j+5)^4) < 1/3 ∧
    1 + envelope 3^2 + (∑ j ∈ Finset.range n, envelope (2*(j:ℝ)+5)^2) < 3/2 := by
  obtain ⟨h₁,h₂⟩ := two_tails n
  norm_num [envelope] at *
  constructor <;> linarith

theorem attenuation (l s p : ℝ) (hl : 1 ≤ l) (hp : 8 ≤ p) (ha : 1 ≤ p*s^2) :
    envelope l ≥ (1 + (l^2-1)*s^2) ^ (-(p/8)) := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have nonneg : 0 ≤ (l^2-1)*s^2 := mul_nonneg hL (sq_nonneg _)
  have bern := one_add_mul_self_le_rpow_one_add (by linarith : -1 ≤ (l^2-1)*s^2)
    (by linarith : 1 ≤ p/8)
  have hb : (l^2+7)/8 ≤ (1+(l^2-1)*s^2)^(p/8) := by
    apply le_trans _ bern
    nlinarith [mul_nonneg hL (sub_nonneg.mpr ha)]
  rw [Real.rpow_neg (by linarith : 0 ≤ 1+(l^2-1)*s^2)]
  have bound := one_div_le_one_div_of_le (by positivity : 0 < (l^2+7)/8) hb
  simpa [envelope, div_div_eq_mul_div, one_div_div] using bound

/-- The paper's envelope to the fourth power dominates the normalized pole at exponent p. -/
theorem decay_p (l s p : ℝ) (hl : 1 ≤ l) (hp : 8 ≤ p) (ha : 1 ≤ p*s^2) :
    (1+(l^2-1)*s^2)^(-(p/2)) ≤ envelope l ^ 4 := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have hx : 0 < 1+(l^2-1)*s^2 := by positivity
  have h := pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) (attenuation l s p hl hp ha) 4
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le] at h
  have eq : -(p/8)*((4:ℕ):ℝ) = -(p/2) := by push_cast; ring
  rwa [eq] at h

theorem decay_half (l s p k : ℝ) (hl : 1 ≤ l) (hp : 8 ≤ p) (ha : 1 ≤ p*s^2) (hk : p ≤ 2*k) :
    (1+(l^2-1)*s^2)^(-(k/2)) ≤ envelope l ^ 2 := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have hx : 1 ≤ 1+(l^2-1)*s^2 := by nlinarith [mul_nonneg hL (sq_nonneg s)]
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) (attenuation l s p hl hp ha) 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ 1+(l^2-1)*s^2)] at h
  apply le_trans _ h
  apply Real.rpow_le_rpow_of_exponent_le hx
  norm_num
  linarith

noncomputable def amplitude (l s q : ℝ) : ℝ := (1+(l^2-1)*s^2)^(-(q/2))

private theorem amplitude_nonneg (l s q : ℝ) (hl : 1 ≤ l) : 0 ≤ amplitude l s q := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  exact Real.rpow_nonneg (by positivity) _

theorem actual_series_bounds (s p k : ℝ) (hp : 8 ≤ p) (ha : 1 ≤ p*s^2) (hk : p ≤ 2*k) :
    3*amplitude 3 s p + (∑' j : ℕ, (2*(j:ℝ)+5)*amplitude (2*j+5) s p) < 1/3 ∧
    1+amplitude 3 s k + (∑' j : ℕ, amplitude (2*(j:ℝ)+5) s k) < 3/2 := by
  have lgt (j : ℕ) : 1 ≤ 2*(j:ℝ)+5 := by
    have : 0 ≤ (j:ℝ) := by positivity
    linarith
  have p_le (n : ℕ) : (∑ j ∈ Finset.range n, (2*(j:ℝ)+5)*amplitude (2*j+5) s p) ≤ 2/27 := by
    apply le_trans _ (two_tails n).1
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (decay_p _ s p (lgt j) hp ha) (by positivity)
  have k_le (n : ℕ) : (∑ j ∈ Finset.range n, amplitude (2*(j:ℝ)+5) s k) ≤ 1/6 := by
    apply le_trans _ (two_tails n).2
    exact Finset.sum_le_sum fun j _ => decay_half _ s p k (lgt j) hp ha hk
  have bp := Real.tsum_le_of_sum_range_le
    (fun j : ℕ => mul_nonneg (by positivity : 0 ≤ 2*(j:ℝ)+5) (amplitude_nonneg _ s p (lgt j))) p_le
  have bk := Real.tsum_le_of_sum_range_le (fun j : ℕ => amplitude_nonneg _ s k (lgt j)) k_le
  have a : amplitude 3 s p ≤ envelope 3^4 := decay_p _ _ _ (by norm_num) hp ha
  have c : amplitude 3 s k ≤ envelope 3^2 := decay_half _ _ _ _ (by norm_num) hp ha hk
  norm_num [envelope] at a c
  constructor <;> linarith

noncomputable def pole (c s l : ℝ) : ℂ :=
  ⟨c/(1+(l^2-1)*s^2), -(l*s)/(1+(l^2-1)*s^2)⟩

theorem norm_pole_sq (c s l : ℝ) (hu : c^2+s^2=1) (hl : 1 ≤ l) :
    ‖pole c s l‖^2 = 1/(1+(l^2-1)*s^2) := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have hd : 0 < 1+(l^2-1)*s^2 := by positivity
  rw [Complex.sq_norm, Complex.normSq_apply]
  change c/_ * (c/_) + (-(l*s)/_)* (-(l*s)/_) = _
  field_simp
  nlinarith [hu]

theorem norm_pole_pow (c s l : ℝ) (hu : c^2+s^2=1) (hl : 1 ≤ l) (n : ℕ) :
    ‖(pole c s l)^n‖ = amplitude l s n := by
  let d := 1+(l^2-1)*s^2
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : ((Real.sqrt d)⁻¹)^2 = 1/d := by rw [inv_pow, Real.sq_sqrt hd.le, one_div]
  have hn : ‖pole c s l‖ = (Real.sqrt d)⁻¹ :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ((norm_pole_sq c s l hu hl).trans hs.symm)
  rw [norm_pow, hn, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hd.le]
  change d^(-(1/2 : ℝ)*(n:ℝ)) = d^(-((n:ℝ)/2))
  congr 1
  ring

theorem norm_centered (c s l : ℝ) (hu : c^2+s^2=1) (hl : 1 ≤ l) (hs : 0 ≤ s) :
    ‖pole c s l - (c:ℂ)‖ ≤ l*s := by
  let d := 1+(l^2-1)*s^2
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have hd : 0 < d := by dsimp [d]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  change (c/d-c)*(c/d-c)+(-(l*s)/d-0)*(-(l*s)/d-0) ≤ _
  have hre : c/d-c = -(c*(l^2-1)*s^2)/d := by field_simp; dsimp [d]; ring
  rw [hre]
  simp only [sub_zero]
  have key := mul_le_mul_of_nonneg_right (phase_error_squared l s c hl hu) (sq_nonneg s)
  field_simp
  dsimp [d] at *
  nlinarith [key]

#print axioms norm_pole_pow
#print axioms norm_centered
#print axioms actual_series_bounds
#print axioms decay_p
#print axioms decay_half
#print axioms odd_pole_bounds
end LongCycleBounds.PoleTails
