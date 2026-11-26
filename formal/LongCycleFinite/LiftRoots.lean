import LongCycleFinite.Gamma

namespace LongCycleFinite

open Polynomial

noncomputable section

theorem expandGamma_degree_le (cs : List ℤ) (d : ℕ) (h : 2 * (cs.length - 1) ≤ d) :
    (expandGamma d cs).natDegree ≤ d := by
  induction cs generalizing d with
  | nil => simp [expandGamma]
  | cons a as ih =>
    rw [expandGamma]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_C_mul_le _ _).trans
      have hx : ((1 : Polynomial ℝ) + X).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (by simp)
      exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left d hx)
    · cases as with
      | nil => simp [expandGamma]
      | cons b bs =>
        have h2 : 2 ≤ d := by simp only [List.length_cons] at h; omega
        have h' : 2 * ((b :: bs).length - 1) ≤ d - 2 := by
          simp only [List.length_cons] at h ⊢
          omega
        apply natDegree_mul_le.trans
        simp only [natDegree_X]
        have hb := ih (d - 2) h'
        omega

theorem expandGamma_odd_at_center (cs : List ℤ) (n : ℕ) (h : cs.length ≤ n + 1) :
    (expandGamma (2 * n + 1) cs).eval (-1) = 0 := by
  induction cs generalizing n with
  | nil => simp [expandGamma]
  | cons a as ih =>
    rw [expandGamma]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_one, eval_X, add_neg_cancel,
      pow_succ, mul_zero, zero_add]
    cases n with
    | zero =>
      have hs : as.length = 0 := by simp only [List.length_cons] at h; omega
      rw [List.length_eq_zero_iff.mp hs]
      simp [expandGamma]
    | succ n =>
      have hn : 2 * (n + 1) + 1 - 2 = 2 * n + 1 := by omega
      have h' : as.length ≤ n + 1 := by simp only [List.length_cons] at h; omega
      rw [hn, ih n h', mul_zero]

def reciprocalLift (x : ℝ) : ℝ := (negLift x)⁻¹

theorem reciprocalLift_lt_center {x : ℝ} (hx : x < 0) : reciprocalLift x < -1 := by
  have hn := negLift_range hx
  simpa [reciprocalLift] using (inv_lt_inv_of_neg hn.2 (by norm_num : (-1 : ℝ) < 0)).2 hn.1

theorem reciprocalLift_strictAnti : StrictAntiOn reciprocalLift (Set.Iio 0) := by
  intro x hx y hy hxy
  exact (inv_lt_inv_of_neg (negLift_range hy).2 (negLift_range hx).2).2
    (negLift_strictMono hx hy hxy)

theorem expanded_lift_root {d : ℕ} {cs : List ℤ} (hlen : 2 * (cs.length - 1) ≤ d)
    {x : ℝ} (hx : x < 0) (hr : (ofCoeffs cs).eval x = 0) :
    (expandGamma d cs).eval (negLift x) = 0 ∧
      (expandGamma d cs).eval (reciprocalLift x) = 0 := by
  have hl := negLift_range hx
  constructor
  · rw [eval_expandGamma d cs hlen hl.1.ne', gammaArgument_negLift hx, hr, mul_zero]
  · rw [eval_expandGamma d cs hlen (reciprocalLift_lt_center hx).ne, reciprocalLift,
      gammaArgument_inv hl.2.ne hl.1.ne', gammaArgument_negLift hx, hr, mul_zero]

def liftRoots {n : ℕ} (c : ℕ) (r : Fin n → ℝ) (i : Fin (n + n + c)) : ℝ :=
  if hl : i.val < n then reciprocalLift (r ⟨n - 1 - i.val, by omega⟩)
  else if hm : i.val < n + c then -1
  else negLift (r ⟨i.val - (n + c), by have hi := i.isLt; omega⟩)

theorem liftRoots_negative {n c : ℕ} (r : Fin n → ℝ) (hn : ∀ i, r i < 0)
    (i : Fin (n + n + c)) : liftRoots c r i < 0 := by
  unfold liftRoots
  split_ifs
  · exact (reciprocalLift_lt_center (hn _)).trans (by norm_num)
  · norm_num
  · exact (negLift_range (hn _)).2

theorem liftRoots_strictMono {n c : ℕ} (hc : c ≤ 1) (r : Fin n → ℝ)
    (hr : StrictMono r) (hn : ∀ i, r i < 0) : StrictMono (liftRoots c r) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  unfold liftRoots
  split_ifs
  · apply reciprocalLift_strictAnti (hn _) (hn _) (hr ?_)
    show n - 1 - j.val < n - 1 - i.val
    omega
  · exact reciprocalLift_lt_center (hn _)
  · exact (reciprocalLift_lt_center (hn _)).trans (negLift_range (hn _)).1
  · omega
  · omega
  · exact (negLift_range (hn _)).1
  · omega
  · omega
  · apply negLift_strictMono (hn _) (hn _) (hr ?_)
    show i.val - (n + c) < j.val - (n + c)
    omega

theorem liftRoots_eval {n c d : ℕ} {cs : List ℤ} (hlen : 2 * (cs.length - 1) ≤ d)
    (r : Fin n → ℝ) (hn : ∀ i, r i < 0) (hr : ∀ i, (ofCoeffs cs).eval (r i) = 0)
    (hc : c ≠ 0 → (expandGamma d cs).eval (-1) = 0) (i : Fin (n + n + c)) :
    (expandGamma d cs).eval (liftRoots c r i) = 0 := by
  unfold liftRoots
  split_ifs
  · exact (expanded_lift_root hlen (hn _) (hr _)).2
  · exact hc (by omega)
  · exact (expanded_lift_root hlen (hn _) (hr _)).1

private theorem lift_left {n c : ℕ} (r : Fin n → ℝ) (i : Fin (n + n + c)) (h : i.val < n) :
    liftRoots c r i = reciprocalLift (r ⟨n - 1 - i.val, by omega⟩) := by simp [liftRoots, h]

private theorem lift_center {n c : ℕ} (r : Fin n → ℝ) (i : Fin (n + n + c))
    (h₁ : n ≤ i.val) (h₂ : i.val < n + c) : liftRoots c r i = -1 := by
  simp [liftRoots, not_lt.mpr h₁, h₂]

private theorem lift_right {n c : ℕ} (r : Fin n → ℝ) (i : Fin (n + n + c)) (h : n + c ≤ i.val) :
    liftRoots c r i = negLift (r ⟨i.val - (n + c), by have _hi := i.isLt; omega⟩) := by
  simp [liftRoots, not_lt.mpr h, not_lt.mpr (show n ≤ i.val by omega)]

private theorem eval_of_factor {p : Polynomial ℝ} {n : ℕ} {r : Fin n → ℝ}
    (h : p = C p.leadingCoeff * ∏ i, (X - C (r i))) (i : Fin n) : p.eval (r i) = 0 := by
  conv_lhs => rw [h]
  rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)]
  simp

private theorem expandGamma_ne_zero {cs : List ℤ} {d : ℕ} (hlen : 2 * (cs.length - 1) ≤ d)
    (h : ofCoeffs cs ≠ 0) : expandGamma d cs ≠ 0 := by
  intro he
  apply h (eq_zero_of_infinite_isRoot _ ((Set.Iio_infinite 0).mono ?_))
  intro x (hx : x < 0)
  have hv := negLift_range hx
  have hr := eval_expandGamma d cs hlen hv.1.ne'
  rw [he, eval_zero, gammaArgument_negLift hx] at hr
  exact (mul_eq_zero.mp hr.symm).resolve_left (pow_ne_zero _ (by linarith [hv.1]))

private def asEvenIndex {d : ℕ} (i : Fin (d + d + 1 + 1)) : Fin (d + 1 + (d + 1) + 0) :=
  ⟨i.val, by have hi := i.isLt; omega⟩

/-- Strict gamma interlacing gives strict interlacing on both reciprocal halves,
with the single intervening root at -1 in the odd-degree polynomial. -/
theorem expandGamma_interlacing {p q : List ℤ} {d : ℕ}
    (hpl : p.length = d + 1) (hql : q.length = d + 2)
    (h : StrictNegativeInterlacing (ofCoeffs p) (ofCoeffs q) d) :
    StrictNegativeInterlacing (expandGamma (d + d + 1) p) (expandGamma (d + d + 1 + 1) q)
      (d + d + 1) := by
  obtain ⟨r, s, hpn, hqn, hpf, hqf, hr, hs, hrn, hsn, hpair⟩ := h
  let P := expandGamma (d + d + 1) p
  let Q := expandGamma (d + d + 1 + 1) q
  let rl := liftRoots 1 r
  let sl (i : Fin (d + d + 1 + 1)) := liftRoots 0 s (asEvenIndex i)
  have hpLen : 2 * (p.length - 1) ≤ d + d + 1 := by omega
  have hqLen : 2 * (q.length - 1) ≤ d + d + 1 + 1 := by omega
  have hp : P ≠ 0 := expandGamma_ne_zero hpLen (leadingCoeff_ne_zero.mp hpn)
  have hq : Q ≠ 0 := expandGamma_ne_zero hqLen (leadingCoeff_ne_zero.mp hqn)
  have hrl : StrictMono rl := liftRoots_strictMono (by decide) r hr hrn
  have hsl : StrictMono sl := by
    apply (liftRoots_strictMono (by decide : 0 ≤ 1) s hs hsn).comp
    exact fun _ _ hij ↦ hij
  have hrv (i) : P.eval (rl i) = 0 :=
    liftRoots_eval hpLen r hrn (eval_of_factor hpf) (fun _ ↦ by
      simpa only [two_mul] using expandGamma_odd_at_center p d hpl.le) i
  have hsv (i) : Q.eval (sl i) = 0 :=
    liftRoots_eval hqLen s hsn (eval_of_factor hqf) (fun hn ↦ (hn rfl).elim) (asEvenIndex i)
  refine ⟨rl, sl, leadingCoeff_ne_zero.mpr hp, leadingCoeff_ne_zero.mpr hq,
    factor_of_degree_bound rl hp (expandGamma_degree_le p _ hpLen) hrl.injective hrv,
    factor_of_degree_bound sl hq (expandGamma_degree_le q _ hqLen) hsl.injective hsv,
    hrl, hsl, liftRoots_negative r hrn, fun i ↦ liftRoots_negative s hsn (asEvenIndex i), ?_⟩
  intro i
  have hi := i.isLt
  let il := asEvenIndex i.castSucc
  let iu := asEvenIndex i.succ
  have hil : il.val = i.val := rfl
  have hiu : iu.val = i.val + 1 := rfl
  change liftRoots 0 s il < liftRoots 1 r i ∧ liftRoots 1 r i < liftRoots 0 s iu
  rcases lt_trichotomy i.val d with hlt | he | hgt
  · rw [lift_left r i hlt, lift_left s il (by omega), lift_left s iu (by omega)]
    let j : Fin d := ⟨d - 1 - i.val, by omega⟩
    have e₁ : (⟨d + 1 - 1 - il.val, by omega⟩ : Fin (d + 1)) = j.succ := by
      apply Fin.ext
      change d + 1 - 1 - il.val = (d - 1 - i.val) + 1
      omega
    have e₂ : (⟨d + 1 - 1 - iu.val, by omega⟩ : Fin (d + 1)) = j.castSucc := by
      apply Fin.ext
      change d + 1 - 1 - iu.val = d - 1 - i.val
      omega
    rw [e₁, e₂]
    exact ⟨reciprocalLift_strictAnti (hrn j) (hsn j.succ) (hpair j).2,
      reciprocalLift_strictAnti (hsn j.castSucc) (hrn j) (hpair j).1⟩
  · rw [lift_center r i (by omega) (by omega), lift_left s il (by omega),
      lift_right s iu (by omega)]
    exact ⟨reciprocalLift_lt_center (hsn _), (negLift_range (hsn _)).1⟩
  · rw [lift_right r i (by omega), lift_right s il (by omega), lift_right s iu (by omega)]
    let j : Fin d := ⟨i.val - (d + 1), by omega⟩
    have e₁ : (⟨il.val - (d + 1 + 0), by omega⟩ : Fin (d + 1)) = j.castSucc := by
      apply Fin.ext
      change il.val - (d + 1 + 0) = i.val - (d + 1)
      omega
    have e₂ : (⟨iu.val - (d + 1 + 0), by omega⟩ : Fin (d + 1)) = j.succ := by
      apply Fin.ext
      change iu.val - (d + 1 + 0) = (i.val - (d + 1)) + 1
      omega
    rw [e₁, e₂]
    exact ⟨negLift_strictMono (hsn j.castSucc) (hrn j) (hpair j).1,
      negLift_strictMono (hrn j) (hsn j.succ) (hpair j).2⟩

#print axioms expandGamma_degree_le
#print axioms expandGamma_odd_at_center
#print axioms expanded_lift_root
#print axioms liftRoots_strictMono
#print axioms liftRoots_eval
#print axioms expandGamma_interlacing

end

end LongCycleFinite
