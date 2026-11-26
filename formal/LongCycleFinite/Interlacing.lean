import LongCycleFinite.Checks

namespace LongCycleFinite

open Polynomial

noncomputable section

/-- All roots are accounted for, and the two ordered negative root lists strictly interlace. -/
def StrictNegativeInterlacing (p q : Polynomial ℝ) (d : ℕ) : Prop :=
  ∃ (r : Fin d → ℝ) (s : Fin (d + 1) → ℝ), p.leadingCoeff ≠ 0 ∧ q.leadingCoeff ≠ 0 ∧
    p = C p.leadingCoeff * ∏ i, (X - C (r i)) ∧
    q = C q.leadingCoeff * ∏ i, (X - C (s i)) ∧
    StrictMono r ∧ StrictMono s ∧ (∀ i, r i < 0) ∧ (∀ i, s i < 0) ∧
    ∀ i, s i.castSucc < r i ∧ r i < s i.succ

def HasSign (negative : Bool) (x : ℝ) : Prop := if negative then x < 0 else 0 < x

private theorem HasSign.ne_zero {b : Bool} {x : ℝ} (h : HasSign b x) : x ≠ 0 := by
  cases b <;> simp [HasSign] at h
  · exact h.ne'
  · exact h.ne

private theorem HasSign.opposite_mul_neg {b : Bool} {x y : ℝ}
    (h₁ : HasSign b x) (h₂ : HasSign (!b) y) : x * y < 0 := by
  cases b <;> simp [HasSign] at h₁ h₂
  · exact mul_neg_of_pos_of_neg h₁ h₂
  · exact mul_neg_of_neg_of_pos h₁ h₂

theorem root_between (f : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (h : f.eval a * f.eval b < 0) : ∃ x : ℝ, a < x ∧ x < b ∧ f.eval x = 0 := by
  obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := mul_neg_iff.mp h
  · obtain ⟨x, ⟨hax, hxb⟩, hx⟩ :=
      intermediate_value_Icc' hab.le f.continuousOn (show 0 ∈ Set.Icc _ _ from ⟨hb.le, ha.le⟩)
    exact ⟨x, hax.lt_of_ne (fun e ↦ ha.ne' (e ▸ hx)),
      hxb.lt_of_ne (fun e ↦ hb.ne (e ▸ hx)), hx⟩
  · obtain ⟨x, ⟨hax, hxb⟩, hx⟩ :=
      intermediate_value_Icc hab.le f.continuousOn (show 0 ∈ Set.Icc _ _ from ⟨ha.le, hb.le⟩)
    exact ⟨x, hax.lt_of_ne (fun e ↦ ha.ne (e ▸ hx)),
      hxb.lt_of_ne (fun e ↦ hb.ne' (e ▸ hx)), hx⟩

theorem ofCoeffs_degree_le (cs : List ℤ) : (ofCoeffs cs).natDegree ≤ cs.length - 1 := by
  induction cs with
  | nil => simp [ofCoeffs]
  | cons a as ih =>
    cases as with
    | nil => simp [ofCoeffs]
    | cons b bs =>
      rw [ofCoeffs]
      apply (natDegree_add_le _ _).trans
      rw [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)]
      have h := natDegree_mul_le (p := (X : Polynomial ℝ)) (q := ofCoeffs (b :: bs))
      simp only [natDegree_X, List.length_cons] at h ih ⊢
      omega

theorem factor_of_degree_bound {n : ℕ} {f : Polynomial ℝ} (r : Fin n → ℝ)
    (hf : f ≠ 0) (hd : f.natDegree ≤ n) (hi : Function.Injective r)
    (hr : ∀ i, f.eval (r i) = 0) :
    f = C f.leadingCoeff * ∏ i : Fin n, (X - C (r i)) := by
  classical
  let points := Finset.univ.map (⟨r, hi⟩ : Fin n ↪ ℝ)
  have hroots : f.roots = points.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact hr i
    · simpa [points] using hd
    · exact hf
  have hcard : f.roots.card = f.natDegree := by
    apply le_antisymm f.card_roots'
    simpa [hroots, points] using hd
  calc
    f = C f.leadingCoeff * (f.roots.map (fun x ↦ X - C x)).prod :=
      (C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
    _ = C f.leadingCoeff * ∏ x ∈ points, (X - C x) := by rw [hroots, Finset.prod_map_val]
    _ = _ := by
      rw [show points = Finset.univ.map (⟨r, hi⟩ : Fin n ↪ ℝ) from rfl, Finset.prod_map]
      rfl

theorem interlacing_of_brackets {p q : Polynomial ℝ} {d : ℕ} (hp : p ≠ 0) (hq : q ≠ 0)
    (dp : p.natDegree ≤ d) (dq : q.natDegree ≤ d + 1) (outer : ℝ)
    (lo hi : Fin d → ℝ) (hout : outer < 0)
    (hwindows : ∀ i, outer < lo i ∧ lo i < hi i ∧ hi i < 0)
    (horder : ∀ i j, i < j → hi i < lo j)
    (hflip : ∀ i, p.eval (lo i) * p.eval (hi i) < 0)
    (hgaps : ∀ i : Fin (d + 1),
      q.eval (Fin.cases outer hi i) * q.eval (Fin.lastCases 0 lo i) < 0) :
    StrictNegativeInterlacing p q d := by
  let a : Fin (d + 1) → ℝ := Fin.cases outer hi
  let b : Fin (d + 1) → ℝ := Fin.lastCases 0 lo
  have ha : ∀ i, a i < 0 := by
    intro i
    refine Fin.cases hout (fun j ↦ (hwindows j).2.2) i
  have hab (i : Fin (d + 1)) : a i < b i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [b] using ha (Fin.last d)
    · simp only [b, Fin.lastCases_castSucc]
      by_cases hzero : j.val = 0
      · have he : j.castSucc = 0 := Fin.ext hzero
        simpa only [he, a, Fin.cases_zero] using (hwindows j).1
      · let j' : Fin d := ⟨j.val - 1, by omega⟩
        have he : j.castSucc = j'.succ := Fin.ext (by dsimp [j']; omega)
        have hj : j' < j := by change j.val - 1 < j.val; omega
        simpa only [he, a, Fin.cases_succ] using horder j' j hj
  choose r hr using fun i ↦ root_between p (hwindows i).2.1 (hflip i)
  choose s hs using fun i ↦ root_between q (hab i) (hgaps i)
  have hir : StrictMono r := fun i j hij ↦
    (hr i).2.1.trans ((horder i j hij).trans (hr j).1)
  have hsides (i : Fin d) : s i.castSucc < r i ∧ r i < s i.succ := by
    refine ⟨?_, ?_⟩
    · have hsi : s i.castSucc < lo i := by simpa [b] using (hs i.castSucc).2.1
      exact hsi.trans (hr i).1
    · have hsi : hi i < s i.succ := by simpa [a] using (hs i.succ).1
      exact (hr i).2.1.trans hsi
  have his : StrictMono s := Fin.strictMono_iff_lt_succ.mpr
    (fun i ↦ (hsides i).1.trans (hsides i).2)
  have hns (i : Fin (d + 1)) : s i < 0 := by
    apply (hs i).2.1.trans_le
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [b]
    · simp only [b, Fin.lastCases_castSucc]
      exact ((hwindows j).2.1.trans (hwindows j).2.2).le
  exact ⟨r, s, leadingCoeff_ne_zero.mpr hp, leadingCoeff_ne_zero.mpr hq,
    factor_of_degree_bound r hp dp hir.injective (fun i ↦ (hr i).2.2),
    factor_of_degree_bound s hq dq his.injective (fun i ↦ (hs i).2.2), hir, his,
    fun i ↦ (hr i).2.1.trans (hwindows i).2.2, hns, hsides⟩

private theorem negativeSign_succ (n : ℕ) : negativeSign (n + 1) = !negativeSign n := by
  by_cases hn : n % 2 = 0
  · have hs : (n + 1) % 2 = 1 := by omega
    simp [negativeSign, hn, hs]
  · have hs : (n + 1) % 2 = 0 := by omega
    have hn' : n % 2 = 1 := by omega
    simp [negativeSign, hn', hs]

private theorem sign_of_check {b : Bool} {cs : List ℤ} {x : Dyadic}
    (h : roundedSign b cs x = true) : HasSign b ((ofCoeffs cs).eval x.value) :=
  roundedSign_sound b cs x h

/-- A checked row pair certifies all roots and the strict order, using the
degree bound to exclude unlisted roots or multiplicities. -/
theorem caseOK_sound {p q : List ℤ} {outer : Dyadic} {ws : List Window}
    (hws : 0 < ws.length) (h : caseOK p q outer ws = true) :
    StrictNegativeInterlacing (ofCoeffs p) (ofCoeffs q) ws.length := by
  let d := ws.length
  let lo (i : Fin d) := (ws.get i).left.value
  let hi (i : Fin d) := (ws.get i).right.value
  obtain ⟨⟨hb, ho⟩, hs⟩ : (boundaryOK p q outer d = true ∧ orderOK outer ws = true) ∧
      signsOK p q d ws = true := by simpa only [caseOK, Bool.and_eq_true_iff] using h
  obtain ⟨⟨⟨⟨hpl, hql⟩, _⟩, hout⟩, hzero⟩ := show
      (((p.length = d + 1 ∧ q.length = d + 2) ∧ (0 < p.getLastD 0 ∧ 0 < q.getLastD 0)) ∧
        roundedSign (negativeSign (d + 1)) q outer = true) ∧
          roundedSign false q Dyadic.zero = true by
    simpa only [boundaryOK, Bool.and_eq_true_iff, decide_eq_true_eq] using hb
  have hx (i : Fin d) :
      HasSign (negativeSign (d - i.val)) ((ofCoeffs p).eval (lo i)) ∧
      HasSign (!negativeSign (d - i.val)) ((ofCoeffs p).eval (hi i)) ∧
      HasSign (negativeSign (d - i.val)) ((ofCoeffs q).eval (lo i)) ∧
      HasSign (negativeSign (d - i.val)) ((ofCoeffs q).eval (hi i)) := by
    have h' := signsOK_at hs i
    simp only [windowOK, Bool.and_eq_true_iff] at h'
    exact ⟨sign_of_check h'.1.1.1, sign_of_check h'.1.1.2,
      sign_of_check h'.1.2, sign_of_check h'.2⟩
  have hq0 : HasSign false ((ofCoeffs q).eval 0) := by
    simpa only [Dyadic.value_zero] using sign_of_check hzero
  have hp : ofCoeffs p ≠ 0 := by
    intro he
    have hn := (hx ⟨0, hws⟩).1.ne_zero
    apply hn
    rw [he, eval_zero]
  have hq : ofCoeffs q ≠ 0 := by
    intro he
    apply hq0.ne_zero
    rw [he, eval_zero]
  obtain ⟨ho0, how, hor⟩ := orderOK_between ho
  have hpl' : (ofCoeffs p).natDegree ≤ d := (ofCoeffs_degree_le p).trans (by rw [hpl]; omega)
  have hql' : (ofCoeffs q).natDegree ≤ d + 1 :=
    (ofCoeffs_degree_le q).trans (by rw [hql]; omega)
  apply interlacing_of_brackets hp hq hpl' hql' outer.value lo hi ho0 how hor
    (fun i ↦ (hx i).1.opposite_mul_neg (hx i).2.1)
  intro i
  have ha (i : Fin (d + 1)) : HasSign (negativeSign (d + 1 - i.val))
      ((ofCoeffs q).eval (Fin.cases outer.value hi i)) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using sign_of_check hout
    · simpa [Nat.add_sub_add_right] using (hx j).2.2.2
  have hb (i : Fin (d + 1)) : HasSign (!negativeSign (d + 1 - i.val))
      ((ofCoeffs q).eval (Fin.lastCases 0 lo i)) := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have he : d + 1 - d = 1 := by omega
      have hsign : (!negativeSign 1) = false := by decide
      simpa only [Fin.lastCases_last, Fin.val_last, he, hsign] using hq0
    · have he : d + 1 - j.val = (d - j.val) + 1 := by have hj := j.isLt; omega
      simpa only [Fin.lastCases_castSucc, Fin.val_castSucc, he, negativeSign_succ,
        Bool.not_not] using (hx j).2.2.1
  exact (ha i).opposite_mul_neg (hb i)

#print axioms root_between
#print axioms factor_of_degree_bound
#print axioms interlacing_of_brackets
#print axioms caseOK_sound

end

end LongCycleFinite
