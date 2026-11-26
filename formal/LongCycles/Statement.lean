import Mathlib

/-!
# The two long-cycle rows at 23 and 24 letters

The definitions of the combinatorial rows and the ordinary Eulerian rows are
independent of any coefficient table. The named propositions at the end of
this file are formal specifications. Defining a proposition does not prove it.
-/

noncomputable section

namespace LongCycles

open Polynomial
open scoped BigOperators

/-- No orbit returns to its starting point at a positive time smaller than k.
The minimum positive return time on a finite orbit is its cycle length. -/
def Allowed {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, ∀ j : ℕ, 0 < j → j < k → (σ ^ j) x ≠ x

/-- Strict excedances in the one-line order on the original labels. -/
def excedances {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun x : Fin n => x < σ x).card

/-- The original sum over permutations, with a separate admissibility test. -/
def enumerator (n k : ℕ) : Polynomial ℝ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n), if Allowed k σ then X ^ (excedances σ) else 0

/-- Count adjacent descents. The existential quantifier has no witness at
the last position, so no wrap-around is counted. -/
def descents {m : ℕ} (σ : Equiv.Perm (Fin m)) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Fin m =>
    ∃ y : Fin m, y.val = x.val + 1 ∧ σ y < σ x).card

/-- The ordinary Eulerian polynomial with constant coefficient one. -/
def eulerian (m : ℕ) : Polynomial ℝ :=
  ∑ σ : Equiv.Perm (Fin m), X ^ (descents σ)

/-- Consequence of the admissibility convention, including its strict cutoff. -/
theorem ne_fixed_of_allowed {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Allowed k σ) (hk : 1 < k) (x : Fin n) : σ x ≠ x := by
  simpa using h x 1 (by decide) hk

/-- A factor is repeated once for each occurrence in the supplied root list.
An identity with this product gives a complete splitting over the reals. -/
def linearFactors {d : ℕ} (r : Fin d → ℝ) : Polynomial ℝ :=
  ∏ i : Fin d, (X - C (r i))

/-- Weak interlacing when the polynomial on the right has degree one larger.
The nonzero leading scalars allow arbitrary normalization. The two
factorizations exclude any unlisted roots, real or nonreal. -/
def WeakRealInterlacing (p q : Polynomial ℝ) : Prop :=
  ∃ d : ℕ, ∃ r : Fin d → ℝ, ∃ s : Fin (d + 1) → ℝ,
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧
      p = C a * linearFactors r ∧ q = C b * linearFactors s ∧
      Monotone r ∧ Monotone s ∧
      ∀ i : Fin d, s i.castSucc ≤ r i ∧ r i ≤ s i.succ

/-- The author's general conjecture. This is not an assumption in the
finite result. For n ≥ k ≥ 3 each row has degree n−1: the cycle
(0,1,…,n−1) attains n−1 excedances, and no permutation can exceed at n−1. -/
def GeneralConjecture : Prop :=
  ∀ k n : ℕ, 3 ≤ k → k ≤ n →
    WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k)

/-- The combinatorial cycle-type identities with no numerical root content.
Nat.choose (2*k) k / 2 is the count of unordered complementary supports. -/
def FirstSplitFamily : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    enumerator (2 * k - 1) k = X * eulerian (2 * k - 2) ∧
    enumerator (2 * k) k = X * (eulerian (2 * k - 1) +
      C (((2 * k).choose k / 2 : ℕ) : ℝ) * X * (eulerian (k - 1)) ^ 2)

/-- The two fixed identities used in the interlacing proof. -/
def FixedFirstSplit : Prop :=
  enumerator 23 12 = X * eulerian 22 ∧
  enumerator 24 12 = X * (eulerian 23 + C ((1352078 : ℕ) : ℝ) * X * (eulerian 11) ^ 2)

/-- A complete root witness for both original rows, including the single
factor X for the zero at the right endpoint of each ordered root list. -/
def PairRoots (r : Fin 21 → ℝ) (q : Fin 22 → ℝ) : Prop :=
  enumerator 23 12 = X * linearFactors r ∧
  enumerator 24 12 = X * linearFactors q ∧
  StrictMono r ∧ StrictMono q ∧
  (∀ i, r i < 0) ∧ (∀ j, q j < 0) ∧
  ∀ i : Fin 21, q i.castSucc < r i ∧ r i < q i.succ

/-- The paper uses one-based indices 12,14,16,18,20. -/
def sensitiveIndex (s : Fin 5) : Fin 21 :=
  ⟨11 + 2 * s.val, by have hs := s.isLt; omega⟩

def enclosureLower : Fin 5 → ℕ := ![783, 7521, 24098, 61232, 176570]

/-- Negative of the signed squared-cycle perturbation divided by the single-cycle term. -/
def relativeCorrection (x : ℝ) : ℝ :=
  ((1352078 : ℕ) : ℝ) * (-x) * ((eulerian 11).eval x) ^ 2 / (eulerian 23).eval x

/-- The analytic bound, the exact interval certificate, and the strict
ordering refer to the same increasing root witness. -/
def RatioData (r : Fin 21 → ℝ) : Prop :=
  let R : Fin 5 → ℝ := fun s => relativeCorrection (r (sensitiveIndex s))
  (∀ s : Fin 5, 0 < (eulerian 23).eval (r (sensitiveIndex s)) ∧
    0 ≤ R s ∧ R s < (49 / 150 : ℝ) ∧
    (enclosureLower s : ℝ) < 1000000 * R s ∧
    1000000 * R s < (enclosureLower s : ℝ) + 1) ∧
  StrictMono R

/-- The fixed-row claim, including the signed ratio bounds and strict rational
enclosures on the right of -1. ArticleScope adds the general cycle-type
identities and the reciprocal ratios to the common witness. -/
def ArticleClaim : Prop :=
  FixedFirstSplit ∧ ∃ r : Fin 21 → ℝ, ∃ q : Fin 22 → ℝ, PairRoots r q ∧ RatioData r

end LongCycles
