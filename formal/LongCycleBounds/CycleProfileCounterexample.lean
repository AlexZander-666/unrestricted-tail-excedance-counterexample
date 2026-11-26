import LongCycleBounds.CycleProfileIndependentWeights
import LongCycleFinite.CoefficientRows

/-! An exact Laguerre witness for an original permutation row with independent cycle weights. -/

namespace LongCycleBounds.CycleProfile.Counterexample
open Finset Polynomial LongCycleFinite

noncomputable def laguerre (p : ℝ[X]) (t : ℝ) : ℝ :=
  p.derivative.eval t ^ 2 - p.eval t * p.derivative.derivative.eval t

theorem laguerre_mul (p q : ℝ[X]) (t : ℝ) :
    laguerre (p * q) t = q.eval t ^ 2 * laguerre p t + p.eval t ^ 2 * laguerre q t := by
  simp only [laguerre, derivative_mul, derivative_add, eval_add, eval_mul]
  ring

theorem laguerre_nonneg_of_splits {p : ℝ[X]} (hp : p.Splits) (t : ℝ) :
    0 ≤ laguerre p t := by
  unfold Splits at hp
  induction hp using Submonoid.closure_induction with
  | mem p hp =>
    rcases hp with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> simp [laguerre]
  | one => simp [laguerre]
  | mul p q _ _ hp hq =>
    rw [laguerre_mul]
    positivity

/-- Add an ascending list of coefficient lists. -/
def addRows (rows : List (List ℤ)) : List ℤ :=
  rows.foldr addCoeffs []

private theorem ofCoeffs_addRows (rows : List (List ℤ)) :
    ofCoeffs (addRows rows) = (rows.map ofCoeffs).sum := by
  induction rows with
  | nil => simp [addRows, ofCoeffs]
  | cons head tail ih =>
    change ofCoeffs (addCoeffs head (addRows tail)) = _
    rw [ofCoeffs_addCoeffs, ih]
    rfl

/-- Prepend the next row to the reverse-order table of all smaller rows. -/
def advance (w : ℕ → ℤ) (n : ℕ) (past : List (List ℤ)) : List ℤ :=
  addRows ((List.range n).map fun j =>
    scaleCoeffs ((Nat.fast_choose n (j + 1) : ℤ) * w (j + 2))
      (mulCoeffs (0 :: descentCoeffs (j + 1)) (past[j + 1]?.getD [])))

def coefficientTable (w : ℕ → ℤ) : ℕ → List (List ℤ)
  | 0 => [[1]]
  | n + 1 => let past := coefficientTable w n; advance w n past :: past

private theorem row_empty (w : ℕ → ℝ) : row 0 w = 1 := by
  classical
  unfold row
  rw [Fintype.sum_unique]
  have empty : (default : Equiv.Perm (Fin 0)) = 1 := Subsingleton.elim _ _
  simp [empty, term, cycleWeight, LongCycles.excedances, LongCycles.Allowed]

private theorem ofCoeffs_advance (w : ℕ → ℤ) (n : ℕ) (past : List (List ℤ))
    (h : ∀ j ≤ n, ofCoeffs (past[j]?.getD []) = row (n - j) (fun a => w a)) :
    ofCoeffs (advance w n past) = row (n + 1) (fun a => w a) := by
  rw [advance, ofCoeffs_addRows, List.map_map, row_anchored (Fin.last n)]
  rw [← List.sum_toFinset _ List.nodup_range]
  rw [List.toFinset_range]
  symm
  refine sum_bij' (fun a _ => a - 2) (fun j _ => j + 2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have bounds := mem_Icc.mp ha
    exact mem_range.mpr (by omega)
  · intro j hj
    have bound := mem_range.mp hj
    exact mem_Icc.mpr (by omega)
  · intro a ha
    have bounds := mem_Icc.mp ha
    omega
  · intro j _
    omega
  · intro a ha
    have bounds := mem_Icc.mp ha
    have pred : a - 2 + 1 = a - 1 := by omega
    have top : a - 2 + 2 = a := by omega
    have rest : n - (a - 1) = n + 1 - a := by omega
    simp only [Function.comp_apply, pred, top, ofCoeffs_scaleCoeffs, ofCoeffs_mulCoeffs,
      ofCoeffs, Int.cast_mul, Int.cast_natCast, Int.cast_zero, map_mul, C_0, zero_add,
      Nat.fast_choose, ← Nat.choose_eq_descFactorial_div_factorial,
      ofCoeffs_descentCoeffs, Nat.add_sub_cancel]
    rw [h (a - 1) (by omega), rest]
    ring

theorem coefficientTable_correct (w : ℕ → ℤ) (n j : ℕ) (hj : j ≤ n) :
    ofCoeffs ((coefficientTable w n)[j]?.getD []) = row (n - j) (fun a => w a) := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp [coefficientTable, ofCoeffs, row_empty]
  | succ n ih =>
    cases j with
    | zero =>
      simpa [coefficientTable] using ofCoeffs_advance w n (coefficientTable w n) ih
    | succ j =>
      simpa [coefficientTable] using ih j (by omega)

def coefficients (w : ℕ → ℤ) (n : ℕ) : List ℤ := ((coefficientTable w n)[0]?).getD []

theorem coefficients_correct (w : ℕ → ℤ) (n : ℕ) :
    ofCoeffs (coefficients w n) = row n (fun a => w a) := by
  simpa [coefficients] using coefficientTable_correct w n 0 (Nat.zero_le n)

structure Jet where
  value : ℚ
  first : ℚ
  second : ℚ

def jet (t : ℚ) : List ℤ → Jet
  | [] => ⟨0, 0, 0⟩
  | a :: as =>
    let previous := jet t as
    ⟨a + t * previous.value, previous.value + t * previous.first,
      2 * previous.first + t * previous.second⟩

theorem jet_correct (t : ℚ) (cs : List ℤ) :
    ((jet t cs).value : ℝ) = (ofCoeffs cs).eval (t : ℝ) ∧
    ((jet t cs).first : ℝ) = (ofCoeffs cs).derivative.eval (t : ℝ) ∧
    ((jet t cs).second : ℝ) = (ofCoeffs cs).derivative.derivative.eval (t : ℝ) := by
  induction cs with
  | nil => simp [jet, ofCoeffs]
  | cons a as ih =>
    obtain ⟨value, first, second⟩ := ih
    simp only [jet, Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, Rat.cast_ofNat, ofCoeffs,
      derivative_add, derivative_mul, derivative_C, derivative_X, zero_add, one_mul,
      eval_add, eval_C, eval_mul, eval_X, value, first, second]
    exact ⟨True.intro, True.intro, by ring⟩

/-- The short cycles retained by the witness. All cycles of length at least thirty-nine are retained. -/
def weightInt (a : ℕ) : ℤ :=
  if 39 ≤ a ∨ a ∈ ([2, 3, 5, 6, 8, 9, 12, 15, 18, 21, 24, 27] : List ℕ) then 1 else 0

noncomputable def weight (a : ℕ) : ℝ := weightInt a

theorem binary_weights (a : ℕ) : weight a = 0 ∨ weight a = 1 := by
  unfold weight weightInt
  split <;> simp

theorem weight_one : weight 1 = 0 := by norm_num [weight, weightInt]

theorem unit_weights (a : ℕ) : weight a ∈ Set.Icc (0 : ℝ) 1 := by
  rcases binary_weights a with ha | ha <;> simp [ha]

theorem tail (a : ℕ) (ha : 39 ≤ a) : weight a = 1 := by simp [weight, weightInt, ha]

def witnessPoint : ℚ := -2 / 15

def witnessJet : Jet := jet witnessPoint (coefficients weightInt 40)

def exactRationalGap : ℚ :=
  -2288543843625100514459554859588709461354575297157347704775831875529338137091190213569135188411635797948561243539968291181405419264527665867959 /
    26834479683007876144808381054741087848013801988623916461307317149476148188114166259765625

theorem rational_gap_exact :
    witnessJet.first ^ 2 - witnessJet.value * witnessJet.second = exactRationalGap := by
  decide +kernel

theorem exact_gap : laguerre (row 40 weight) (witnessPoint : ℝ) = (exactRationalGap : ℝ) := by
  have gap : (witnessJet.first : ℝ) ^ 2 - (witnessJet.value : ℝ) *
      (witnessJet.second : ℝ) = (exactRationalGap : ℝ) := by exact_mod_cast rational_gap_exact
  obtain ⟨value, first, second⟩ := jet_correct witnessPoint (coefficients weightInt 40)
  change (witnessJet.value : ℝ) = _ at value
  change (witnessJet.first : ℝ) = _ at first
  change (witnessJet.second : ℝ) = _ at second
  rw [coefficients_correct, ← show weight = (fun a => (weightInt a : ℝ)) from rfl] at value first second
  simpa only [value, first, second, laguerre] using gap

theorem negative_gap : laguerre (row 40 weight) (witnessPoint : ℝ) < 0 := by
  rw [exact_gap]
  exact_mod_cast (show exactRationalGap < 0 by norm_num [exactRationalGap])

/-- A binary cycle profile, with all lengths at least thirty-nine of weight one,
whose original excedance polynomial has a nonreal root. -/
theorem not_splits : ¬ (row 40 weight).Splits := fun split =>
  (not_lt_of_ge (laguerre_nonneg_of_splits split witnessPoint)) negative_gap

theorem quotient_not_splits : ¬ (weightedQuotient 40 weight).Splits := by
  intro split
  have shape := weightedQuotient_shape (n := 40) (k := 39) (by decide) (by decide)
    unit_weights tail
  exact not_splits (shape.2.2.2 ▸ (Polynomial.Splits.X.mul split))

theorem not_weak_interlacing :
    ¬ LongCycles.WeakRealInterlacing (row 39 weight) (row 40 weight) := by
  rintro ⟨_, _, s, _, b, _, _, _, upper, _⟩
  apply not_splits
  rw [upper, LongCycles.linearFactors]
  exact (Splits.C b).mul (Splits.prod fun i _ => Splits.X_sub_C (s i))

theorem not_strict_interlacing :
    ¬ StrictNegativeInterlacing (weightedQuotient 39 weight) (weightedQuotient 40 weight) 37 := by
  rintro ⟨_, s, _, _, _, upper, _⟩
  apply quotient_not_splits
  rw [upper]
  exact (Splits.C _).mul (Splits.prod fun i _ => Splits.X_sub_C (s i))

#print axioms laguerre_nonneg_of_splits
#print axioms coefficients_correct
#print axioms rational_gap_exact
#print axioms exact_gap
#print axioms negative_gap
#print axioms not_splits
#print axioms quotient_not_splits
#print axioms not_weak_interlacing
#print axioms not_strict_interlacing

end LongCycleBounds.CycleProfile.Counterexample
