import LongCycleBounds.PoleTails

namespace LongCycleBounds.Bulk
open PoleTails
noncomputable section

private def index (j : ℕ) : ℝ := 2*(j:ℝ)+5
private theorem index_ge (j : ℕ) : 3 ≤ index j := by
  dsimp [index]
  have : 0 ≤ (j:ℝ) := by positivity
  linarith

private def majorP (j : ℕ) : ℝ := index j * envelope (index j)^4
private def majorK (j : ℕ) : ℝ := envelope (index j)^2

private theorem majorP_nonneg (j) : 0 ≤ majorP j :=
  mul_nonneg (by linarith [index_ge j]) (by positivity)
private theorem majorK_nonneg (j) : 0 ≤ majorK j := sq_nonneg _

private theorem sumP : Summable majorP :=
  summable_of_sum_range_le majorP_nonneg (fun n => (two_tails n).1)
private theorem sumK : Summable majorK :=
  summable_of_sum_range_le majorK_nonneg (fun n => (two_tails n).2)

private theorem boundP : ∑' j, majorP j ≤ 2/27 :=
  Real.tsum_le_of_sum_range_le majorP_nonneg (fun n => (two_tails n).1)
private theorem boundK : ∑' j, majorK j ≤ 1/6 :=
  Real.tsum_le_of_sum_range_le majorK_nonneg (fun n => (two_tails n).2)

private theorem control {f : ℕ → ℂ} {g : ℕ → ℝ} (sg : Summable g) (h : ∀ j, ‖f j‖ ≤ g j) :
    Summable f ∧ ‖∑' j, f j‖ ≤ ∑' j, g j := by
  have sf : Summable (fun j => ‖f j‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h sg
  exact ⟨sf.of_norm, (norm_tsum_le_tsum_norm sf).trans (Summable.tsum_le_tsum h sf sg)⟩

def tail (c s : ℝ) (n : ℕ) : ℂ := pole c s 3^n + ∑' j, pole c s (index j)^n

def total (c s : ℝ) (n : ℕ) : ℂ := pole c s 1^n + tail c s n

private theorem pole_norm_le (c s l : ℝ) (hu : c^2+s^2=1) (hl : 1 ≤ l) :
    ‖pole c s l‖ ≤ 1 := by
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [norm_pole_sq _ _ _ hu hl, one_pow]
  have hl' : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  exact (div_le_one (by positivity)).mpr (by nlinarith [mul_nonneg hl' (sq_nonneg s)])

private theorem summable_powers (c s : ℝ) (p : ℕ) (hu : c^2+s^2=1)
    (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s^2) :
    Summable (fun j => pole c s (index j)^p) ∧ ‖tail c s p‖ < 1/9 := by
  have nonneg (l : ℝ) : 0 ≤ envelope l := by unfold envelope; positivity
  have est (l : ℝ) (hl : 1 ≤ l) : ‖pole c s l^p‖ ≤ envelope l^4 := by
    rw [norm_pole_pow _ _ _ hu hl]
    exact decay_p _ _ _ hl hp ha
  have h (j) : ‖pole c s (index j)^p‖ ≤ majorP j * (1/3) := by
    apply (est _ (by linarith [index_ge j])).trans
    unfold majorP
    nlinarith [mul_nonneg (sub_nonneg.mpr (index_ge j)) (show 0 ≤ envelope (index j)^4 by positivity)]
  obtain ⟨summable, bound⟩ := control (sumP.mul_right (1/3)) h
  refine ⟨summable, ?_⟩
  rw [tsum_mul_right] at bound
  have b := norm_add_le (pole c s 3^p) (∑' j, pole c s (index j)^p)
  have b3 := est 3 (by norm_num)
  rw [show envelope 3^4 = 1/16 by norm_num [envelope]] at b3
  unfold tail
  linarith [boundP]

theorem numerator_bound_sharp (c s : ℝ) (p k : ℕ) (hu : c^2+s^2=1) (hp : 8 ≤ (p:ℝ))
    (ha : 1 ≤ (p:ℝ)*s^2) (hk : (p:ℝ) ≤ 2*(k:ℝ)) : ‖total c s k‖ ≤ 17/12 := by
  have est (l : ℝ) (hl : 1 ≤ l) : ‖pole c s l^k‖ ≤ envelope l^2 := by
    rw [norm_pole_pow _ _ _ hu hl]
    exact decay_half _ _ _ _ hl hp ha hk
  have b1 := est 1 (by norm_num)
  have b3 := est 3 (by norm_num)
  rw [show envelope 3^2 = 1/4 by norm_num [envelope]] at b3
  rw [show envelope 1^2 = 1 by norm_num [envelope]] at b1
  obtain ⟨_,b⟩ := control sumK (fun j => est (index j) (by linarith [index_ge j]))
  unfold total tail
  linarith [norm_add_le (pole c s 3^k) (∑' j, pole c s (index j)^k),
    norm_add_le (pole c s 1^k) (pole c s 3^k + ∑' j, pole c s (index j)^k), boundK]

theorem numerator_bound (c s : ℝ) (p k : ℕ) (hu : c^2+s^2=1) (hp : 8 ≤ (p:ℝ))
    (ha : 1 ≤ (p:ℝ)*s^2) (hk : (p:ℝ) ≤ 2*(k:ℝ)) : ‖total c s k‖ < 3/2 := by
  exact (numerator_bound_sharp c s p k hu hp ha hk).trans_lt (by norm_num)

private theorem centered_tail (c s : ℝ) (p : ℕ) (hu : c^2+s^2=1) (hs : 0 < s)
    (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s^2) :
    ∃ w : ℂ, tail c s (p+1) = (c:ℂ)*tail c s p + w ∧ ‖w‖ < s/3 := by
  let z (j : ℕ) := pole c s (index j)
  let diff (z : ℂ) := z^p*(z-(c:ℂ))
  have localBound (l : ℝ) (hl : 1 ≤ l) : ‖diff (pole c s l)‖ ≤ (l*envelope l^4)*s := by
    dsimp only [diff]
    rw [norm_mul]
    have hz : ‖pole c s l^p‖ ≤ envelope l^4 := by
      rw [norm_pole_pow _ _ _ hu hl]; exact decay_p l s p hl hp ha
    calc _ ≤ envelope l^4*(l*s) := mul_le_mul hz (norm_centered _ _ _ hu hl hs.le) (norm_nonneg _) (by positivity)
         _ = _ := by ring
  have h (j : ℕ) : ‖diff (z j)‖ ≤ majorP j*s := localBound _ (by linarith [index_ge j])
  obtain ⟨sd,bd⟩ := control (sumP.mul_right s) h
  rw [tsum_mul_right] at bd
  have sp : Summable (fun j => (z j)^p) := (summable_powers _ _ p hu hp ha).1
  have addterm : (∑' j, (z j)^(p+1)) = (c:ℂ)*(∑' j, (z j)^p) + ∑' j, diff (z j) := by
    rw [← tsum_mul_left, ← (sp.mul_left (c:ℂ)).tsum_add sd]
    apply tsum_congr
    intro j
    dsimp [diff]
    ring
  refine ⟨diff (pole c s 3) + ∑' j, diff (z j), ?_, ?_⟩
  · change pole c s 3^(p+1) + (∑' j, (z j)^(p+1)) = _
    rw [addterm]
    change _ = (c:ℂ)*(pole c s 3^p + ∑' j, (z j)^p) + _
    dsimp only [diff]
    ring
  · have b3 := localBound 3 (by norm_num)
    rw [show envelope 3^4=1/16 by norm_num [envelope]] at b3
    have bm := mul_le_mul_of_nonneg_right boundP hs.le
    linarith [norm_add_le (diff (pole c s 3)) (∑' j, diff (z j))]

theorem denominator_at_zero_sharp (c s : ℝ) (p : ℕ) (hu : c^2+s^2=1) (hs : 0 < s)
    (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s^2) (zero : (total c s p).re=0) :
    13*s/20 < |(total c s (p+1)).re| := by
  let a := pole c s 1^p
  have first : pole c s 1 = ⟨c,-s⟩ := by apply Complex.ext <;> simp [pole]
  have anorm : ‖a‖ = 1 := by
    have h : ‖pole c s 1‖ = 1 := by
      have h := norm_pole_sq c s 1 hu (by norm_num)
      norm_num at h
      rcases h with h|h
      · exact h
      · linarith [norm_nonneg (pole c s 1)]
    simp [a, h]
  have small := (summable_powers _ _ p hu hp ha).2
  have haRe : a.re = -(tail c s p).re := by
    change a.re + (tail c s p).re = 0 at zero
    linarith
  have hr : |a.re| < 1/9 := by
    rw [haRe,abs_neg]
    exact (Complex.abs_re_le_norm _).trans_lt small
  have hai : 59/60 < |a.im| := by
    have sq := Complex.sq_norm a
    rw [anorm, Complex.normSq_apply] at sq
    by_contra! fail
    have hr2 := mul_self_le_mul_self (abs_nonneg _) hr.le
    have hi2 := mul_self_le_mul_self (abs_nonneg _) fail
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at hr2 hi2
    nlinarith
  obtain ⟨w,hw,bw⟩ := centered_tail c s p hu hs hp ha
  have ident : total c s (p+1) = (c:ℂ)*total c s p + a*(pole c s 1-(c:ℂ)) + w := by
    unfold total
    rw [hw]
    dsimp [a]
    ring
  have rr : (total c s (p+1)).re = a.im*s + w.re := by
    rw [ident, Complex.add_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero]
    rw [first]
    simp [Complex.mul_re]
  have abw := (Complex.abs_re_le_norm w).trans_lt bw
  have tri := abs_sub (a.im*s+w.re) w.re
  rw [add_sub_cancel_right, abs_mul, abs_of_pos hs] at tri
  rw [rr]
  nlinarith [mul_lt_mul_of_pos_right hai hs]

theorem denominator_at_zero (c s : ℝ) (p : ℕ) (hu : c^2+s^2=1) (hs : 0 < s)
    (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s^2) (zero : (total c s p).re=0) :
    5*s/9 < |(total c s (p+1)).re| := by
  linarith [denominator_at_zero_sharp c s p hu hs hp ha zero]

/-- At a zero of the preceding Eulerian pole sum, the complete perturbation
is strictly smaller than the next unperturbed sum throughout the bulk. -/
theorem bulk_first_split (c s : ℝ) (k p : ℕ) (hk : 201 ≤ k) (pe : p+1 = 2*k)
    (hu : c^2+s^2=1) (hs : 0 < s) (ha : 1 ≤ (p:ℝ)*s^2) (zero : (total c s p).re=0) :
    2*(total c s k).re^2 < (k:ℝ)*|(total c s (p+1)).re| := by
  have hkr : (201:ℝ) ≤ k := by exact_mod_cast hk
  have pre : (p:ℝ)+1 = 2*(k:ℝ) := by exact_mod_cast pe
  have hp : 8 ≤ (p:ℝ) := by linarith
  have n := (Complex.abs_re_le_norm _).trans_lt (numerator_bound c s p k hu hp ha (by linarith))
  have ns := mul_self_lt_mul_self (abs_nonneg _) n
  rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at ns
  have d := denominator_at_zero c s p hu hs hp ha zero
  have hangle : 1 ≤ (2*(k:ℝ)-1)*s^2 := by rwa [show 2*(k:ℝ)-1 = p by linarith]
  have cross := (div_lt_iff₀ (by positivity : 0 < 10*(k:ℝ)*s)).mp (bulk_ratio k s hkr hs hangle)
  have dd := mul_lt_mul_of_pos_left d (by linarith : 0 < (k:ℝ))
  nlinarith

theorem bulk_first_split_sharp (c s : ℝ) (k p : ℕ) (pe : p+1=2*k)
    (hp : 8≤(p:ℝ)) (hu : c^2+s^2=1) (hs : 0<s) (ha : 1≤(p:ℝ)*s^2)
    (hks : 25/4 ≤ (k:ℝ)*s) (zero : (total c s p).re=0) :
    2*(total c s k).re^2 < (k:ℝ)*|(total c s (p+1)).re| := by
  have pre : (p:ℝ)+1 = 2*(k:ℝ) := by exact_mod_cast pe
  have nb := (Complex.abs_re_le_norm _).trans (numerator_bound_sharp c s p k hu hp ha (by linarith))
  have ns := mul_self_le_mul_self (abs_nonneg _) nb
  rw [← abs_mul,abs_of_nonneg (mul_self_nonneg _)] at ns
  have dd := mul_lt_mul_of_pos_left (denominator_at_zero_sharp c s p hu hs hp ha zero)
    (show (0:ℝ)<k by linarith)
  linarith only [ns,dd,hks]

/-- Represent the complete positive half of the odd lattice, with no truncation. -/
theorem positive_half (c s : ℝ) (p q : ℕ) (hu : c^2+s^2=1) (hp : 8 ≤ (p:ℝ))
    (ha : 1 ≤ (p:ℝ)*s^2) (hq : (p:ℝ) ≤ 2*(q:ℝ)) :
    Summable (fun n : ℕ => pole c s (2*n+1)^q) ∧
    (∑' n : ℕ, pole c s (2*n+1)^q) = total c s q := by
  let f (n : ℕ) := pole c s (2*n+1)^q
  have normle (j : ℕ) : ‖pole c s (index j)^q‖ ≤ majorK j := by
    rw [norm_pole_pow _ _ _ hu (by linarith [index_ge j])]
    exact decay_half _ _ p q (by linarith [index_ge j]) hp ha hq
  have sm := (control sumK normle).1
  have shift (j : ℕ) : f (j+2) = pole c s (index j)^q := by
    dsimp [f,index]
    push_cast
    ring_nf
  have sm' : Summable (fun j => f (j+2)) := by simpa only [shift] using sm
  have sf : Summable f := (summable_nat_add_iff 2).mp sm'
  refine ⟨sf, ?_⟩
  change (∑' n, f n) = _
  rw [← sf.sum_add_tsum_nat_add 2]
  simp only [shift, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change (f 0+f 1) + _ = _
  have e0 : f 0 = pole c s 1^q := by norm_num [f]
  have e1 : f 1 = pole c s 3^q := by norm_num [f]
  rw [e0,e1,add_assoc]
  rfl

/-- A controlled residual in the lower moment preserves a strict gap in the upper one. -/
theorem perturbed_denominator (c s : ℝ) (p : ℕ) (hu : c^2+s^2=1) (hs : 0 < s)
    (hp : 8 ≤ (p:ℝ)) (ha : 1 ≤ (p:ℝ)*s^2) (small : |(total c s p).re| ≤ s/8) :
    s/3 < |(total c s (p+1)).re| := by
  let a := pole c s 1^p
  have first : pole c s 1 = ⟨c,-s⟩ := by apply Complex.ext <;> simp [pole]
  have sn : s ≤ 1 := by nlinarith [sq_nonneg c, sq_nonneg (s-1)]
  have cn : |c| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg s, sq_nonneg (c-1), sq_nonneg (c+1)]
  have anorm : ‖a‖ = 1 := by
    have h := norm_pole_sq c s 1 hu (by norm_num)
    norm_num at h
    rcases h with h|h
    · simp [a,h]
    · linarith [norm_nonneg (pole c s 1)]
  have tailSmall := (Complex.abs_re_le_norm _).trans_lt (summable_powers c s p hu hp ha).2
  have sum : (total c s p).re = a.re+(tail c s p).re := rfl
  have tri := abs_sub (total c s p).re (tail c s p).re
  rw [sum,add_sub_cancel_right] at tri
  have realSmall : |a.re| < 1/4 := by rw [sum] at small; linarith
  have imLarge : 5/6 < |a.im| := by
    have sq := Complex.sq_norm a
    rw [anorm,Complex.normSq_apply] at sq
    by_contra! h
    have r := mul_self_le_mul_self (abs_nonneg _) realSmall.le
    have i := mul_self_le_mul_self (abs_nonneg _) h
    rw [← abs_mul,abs_of_nonneg (mul_self_nonneg _)] at r i
    nlinarith
  obtain ⟨w,hw,bw⟩ := centered_tail c s p hu hs hp ha
  have id : total c s (p+1) = (c:ℂ)*total c s p+a*(pole c s 1-(c:ℂ))+w := by
    unfold total
    rw [hw]
    dsimp [a]
    ring
  have rr : (total c s (p+1)).re = c*(total c s p).re+a.im*s+w.re := by
    rw [id,first]
    simp [Complex.mul_re]
  have abw := (Complex.abs_re_le_norm w).trans_lt bw
  have center : |c*(total c s p).re| ≤ s/8 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right cn (abs_nonneg _)).trans (by simpa using small)
  have diff : a.im*s = ((total c s (p+1)).re - w.re)-c*(total c s p).re := by rw [rr]; ring
  have bound := abs_sub ((total c s (p+1)).re - w.re) (c*(total c s p).re)
  rw [← diff,abs_mul,abs_of_pos hs] at bound
  linarith [abs_sub (total c s (p+1)).re w.re, mul_lt_mul_of_pos_right imLarge hs]

#print axioms perturbed_denominator

#print axioms positive_half
#print axioms bulk_first_split
#print axioms denominator_at_zero
#print axioms numerator_bound
end
end LongCycleBounds.Bulk
