import LongCycleFinite.Gamma
import LongCycleBounds.DescentRows
import LongCycles.FirstSplit

namespace LongCycleFinite

open Polynomial

def addCoeffs : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addCoeffs as bs

def scaleCoeffs (a : ℤ) (bs : List ℤ) := bs.map (a * ·)

def mulCoeffs : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, bs => addCoeffs (scaleCoeffs a bs) (0 :: mulCoeffs as bs)

theorem ofCoeffs_addCoeffs (as bs : List ℤ) :
    ofCoeffs (addCoeffs as bs) = ofCoeffs as + ofCoeffs bs := by
  induction as generalizing bs with
  | nil => simp [addCoeffs, ofCoeffs]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs, ofCoeffs]
    | cons b bs =>
      simp only [addCoeffs, ofCoeffs, Int.cast_add, map_add, ih]
      ring

theorem ofCoeffs_scaleCoeffs (a : ℤ) (bs : List ℤ) :
    ofCoeffs (scaleCoeffs a bs) = C (a : ℝ) * ofCoeffs bs := by
  induction bs with
  | nil => simp [scaleCoeffs, ofCoeffs]
  | cons b bs ih =>
    change ofCoeffs (a * b :: scaleCoeffs a bs) = _
    simp only [ofCoeffs, Int.cast_mul, map_mul, ih]
    ring

theorem ofCoeffs_mulCoeffs (as bs : List ℤ) :
    ofCoeffs (mulCoeffs as bs) = ofCoeffs as * ofCoeffs bs := by
  induction as with
  | nil => simp [mulCoeffs, ofCoeffs]
  | cons a as ih =>
    rw [mulCoeffs, ofCoeffs_addCoeffs, ofCoeffs_scaleCoeffs]
    simp only [ofCoeffs, Int.cast_zero, C_0, zero_add, ih]
    ring

def pascalRow : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => let cs := pascalRow n; addCoeffs cs (0 :: cs)

theorem ofCoeffs_pascalRow (n : ℕ) : ofCoeffs (pascalRow n) = (1 + X) ^ n := by
  induction n with
  | zero => simp [pascalRow, ofCoeffs]
  | succ n ih =>
    rw [pascalRow, ofCoeffs_addCoeffs]
    simp only [ofCoeffs, Int.cast_zero, C_0, zero_add, ih, pow_succ]
    ring

def expandCoeffs (d : ℕ) : List ℤ → List ℤ
  | [] => []
  | a :: as => addCoeffs (scaleCoeffs a (pascalRow d)) (0 :: expandCoeffs (d - 2) as)

theorem ofCoeffs_expandCoeffs (d : ℕ) (cs : List ℤ) :
    ofCoeffs (expandCoeffs d cs) = expandGamma d cs := by
  induction cs generalizing d with
  | nil => rfl
  | cons a as ih =>
    rw [expandCoeffs, ofCoeffs_addCoeffs, ofCoeffs_scaleCoeffs, ofCoeffs_pascalRow]
    simp only [expandGamma, ofCoeffs, Int.cast_zero, C_0, zero_add, ih]

theorem coeff_ofCoeffs (cs : List ℤ) (j : ℕ) :
    (ofCoeffs cs).coeff j = (cs[j]?.getD 0 : ℤ) := by
  induction cs generalizing j with
  | nil => simp [ofCoeffs]
  | cons c cs ih =>
    cases j with
    | zero => simp [ofCoeffs]
    | succ j =>
      rw [ofCoeffs, coeff_add, coeff_C, if_neg (Nat.succ_ne_zero j), coeff_X_mul, zero_add, ih]
      simp

def descentStep (m : ℕ) (cs : List ℤ) : List ℤ :=
  (List.range (m + 1)).map fun (j : ℕ) ↦
    ((j : ℤ) + 1) * cs[j]?.getD 0 + ((m : ℤ) + 1 - j) *
      (match j with | 0 => 0 | n + 1 => cs[n]?.getD 0)

def descentCoeffs : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => descentStep n (descentCoeffs n)

private theorem eulerian_degree_le (n : ℕ) : (LongCycles.eulerian n).natDegree ≤ n - 1 := by
  classical
  unfold LongCycles.eulerian
  apply natDegree_sum_le_of_forall_le
  intro π _
  apply (natDegree_X_pow_le _).trans
  cases n with
  | zero => simp [LongCycles.descents]
  | succ n =>
    unfold LongCycles.descents
    have h : (Finset.univ.filter fun x : Fin (n + 1) ↦
        ∃ y : Fin (n + 1), y.val = x.val + 1 ∧ π y < π x) ⊆
          Finset.univ.erase (Fin.last n) := by
      intro x hx
      obtain ⟨y, hy, _⟩ := (Finset.mem_filter.mp hx).2
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro he
      subst x
      have hp := y.isLt
      simp at hy
      omega
    simpa using Finset.card_le_card h

private theorem coeff_X_derivative (f : Polynomial ℝ) (j : ℕ) :
    (X * f.derivative).coeff j = (j : ℝ) * f.coeff j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [coeff_X_mul, coeff_derivative]
    simp only [Nat.cast_succ]
    ring

theorem ofCoeffs_descentCoeffs (n : ℕ) : ofCoeffs (descentCoeffs n) = LongCycles.eulerian n := by
  induction n with
  | zero => simp [descentCoeffs, ofCoeffs, LongCycleBounds.longEulerian_zero]
  | succ n ih =>
    let cs := descentCoeffs n
    let f := LongCycles.eulerian n
    have he : ofCoeffs cs = f := ih
    have hcoeff (j : ℕ) : (cs[j]?.getD 0 : ℝ) = f.coeff j := by rw [← he, coeff_ofCoeffs]
    ext j
    rw [LongCycleBounds.longEulerian_succ, descentCoeffs, coeff_ofCoeffs]
    by_cases hj : j < n + 1
    · rw [show descentCoeffs n = cs from rfl]
      simp only [descentStep, List.getElem?_map, List.getElem?_range hj, Option.map_some,
        Option.getD_some]
      have t : (1 + C (n : ℝ) * X) * f + X * (1 - X) * f.derivative =
          f + C (n : ℝ) * (X * f) + X * f.derivative - X * (X * f.derivative) := by ring
      change (↑_ : ℝ) = ((1 + C (n : ℝ) * X) * f + X * (1 - X) * f.derivative).coeff j
      rw [t]
      cases j with
      | zero => simp [hcoeff]
      | succ j =>
        rw [coeff_sub, coeff_add, coeff_add, coeff_C_mul, coeff_X_derivative f (j + 1),
          coeff_X_mul (X * f.derivative) j, coeff_X_derivative, coeff_X_mul f j]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one,
          hcoeff, Nat.cast_succ]
        ring
    · have hdeg : (LongCycles.eulerian (n + 1)).natDegree < j :=
        (eulerian_degree_le (n + 1)).trans_lt (by omega)
      rw [← LongCycleBounds.longEulerian_succ, coeff_eq_zero_of_natDegree_lt hdeg]
      have hh : (descentStep n (descentCoeffs n)).length ≤ j := by
        simpa [descentStep] using Nat.le_of_not_gt hj
      rw [List.getElem?_eq_none (by omega : (descentStep n (descentCoeffs n)).length ≤ j)]
      simp

/-- The two quotient rows attached to the frozen combinatorial first-split identities. -/
noncomputable def firstP (k : ℕ) : Polynomial ℝ := LongCycles.eulerian (2 * k - 2)

noncomputable def firstQ (k : ℕ) : Polynomial ℝ := LongCycles.eulerian (2 * k - 1) +
  C ((((2 * k).choose k / 2 : ℕ) : ℝ)) * X * (LongCycles.eulerian (k - 1)) ^ 2

theorem firstSplit_quotients (k : ℕ) (hk : 2 ≤ k) :
    LongCycles.enumerator (2 * k - 1) k = X * firstP k ∧
      LongCycles.enumerator (2 * k) k = X * firstQ k := LongCycles.firstSplitFamily k hk

def qCoeffs (k : ℕ) : List ℤ :=
  let a := descentCoeffs (k - 1)
  addCoeffs (descentCoeffs (2 * k - 1))
    (0 :: scaleCoeffs ((Nat.fast_choose (2 * k) k / 2 : ℕ) : ℤ) (mulCoeffs a a))

theorem ofCoeffs_qCoeffs (k : ℕ) : ofCoeffs (qCoeffs k) = firstQ k := by
  simp only [qCoeffs, ofCoeffs_addCoeffs, ofCoeffs, Int.cast_zero, C_0, zero_add,
    ofCoeffs_scaleCoeffs, Int.cast_natCast, ofCoeffs_mulCoeffs, ofCoeffs_descentCoeffs, firstQ,
    Nat.fast_choose, ← Nat.choose_eq_descFactorial_div_factorial]
  ring

#print axioms ofCoeffs_expandCoeffs
#print axioms coeff_ofCoeffs
#print axioms ofCoeffs_descentCoeffs
#print axioms ofCoeffs_qCoeffs
#print axioms firstSplit_quotients

end LongCycleFinite
