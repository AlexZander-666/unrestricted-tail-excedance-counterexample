import LongCycleFinite.Interlacing
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Polynomial.Basic

/-! A sign criterion for adjacent strict interlacing, including both exterior intervals. -/

noncomputable section
namespace LongCycleBounds.Sturm
open Polynomial Finset Filter Asymptotics
open scoped Topology

private theorem sign_sq (j : ℕ) : (-1 : ℝ)^j * (-1)^j = 1 := by rw [← mul_pow]; simp

private theorem opposite (j : ℕ) {x y : ℝ} (hx : 0 < (-1 : ℝ)^(j+1)*x)
    (hy : 0 < (-1 : ℝ)^j*y) : x*y < 0 := by
  have h := mul_pos hx hy
  rw [pow_succ] at h
  have he : ((-1 : ℝ)^j*(-1)*x)*((-1)^j*y) =
      -(((-1)^j*(-1)^j)*(x*y)) := by ring
  rw [he, sign_sq] at h
  linarith

private theorem left_sign (q : ℝ[X]) (d : ℕ) (hd : q.natDegree = d) (hc : 0 < q.leadingCoeff) :
    ∀ᶠ t : ℝ in atBot, 0 < (-1 : ℝ)^d*q.eval t := by
  have h := (IsEquivalent.refl (u := fun _ : ℝ ↦ (-1 : ℝ)^d) (l := atBot)).mul
    q.isEquivalent_atBot_lead
  apply h.eventually_pos
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  change 0 < (-1 : ℝ)^d*(q.leadingCoeff*t^q.natDegree)
  rw [hd, mul_left_comm, ← mul_pow]
  apply mul_pos hc (pow_pos (by linarith : 0 < (-1 : ℝ)*t) _)

/-- Evaluate the derivative of a monic polynomial at an ordered node in its full factorization.
The exponent counts the factors to the right of this node. -/
theorem node_derivative_sign {d : ℕ} (r : Fin d → ℝ) (hr : StrictMono r) (i : Fin d) :
    0 < (-1 : ℝ)^(d-1-i.val) * ((∏ j, (X - C (r j))).derivative.eval (r i)) := by
  classical
  change 0 < _ * (Lagrange.nodal univ r).derivative.eval (r i)
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ i)]
  simp only [Lagrange.nodal, eval_prod, eval_sub, eval_X, eval_C]
  let u : Finset (Fin d) := univ.erase i
  have hc : (u.filter (fun j ↦ i < j)) = Ioi i := by ext j; simp [u]; omega
  have hs : (∏ j ∈ u, (if i < j then (-1 : ℝ) else 1)) = (-1 : ℝ)^(d-1-i.val) := by
    rw [← prod_filter, hc, prod_const, Fin.card_Ioi]
  rw [← hs, ← prod_mul_distrib]
  apply prod_pos
  intro j hj
  have hji := (mem_erase.mp hj).1
  rcases lt_or_gt_of_ne hji with h | h
  · simp [not_lt.mpr h.le, sub_pos.mpr (hr h)]
  · rw [if_pos h]
    linarith [hr h]

private def cut {d : ℕ} (r : Fin d → ℝ) (a : ℝ) (j : ℕ) : ℝ :=
  if j=0 then a else if h : j-1 < d then r ⟨j-1,h⟩ else 0

@[simp] private theorem cut_middle {d} (r : Fin d → ℝ) (a : ℝ) (i : Fin d) :
    cut r a (i.val+1) = r i := by simp [cut, i.isLt]

private theorem cut_step {d : ℕ} (r : Fin d → ℝ) (a : ℝ) (ha : a < 0)
    (har : ∀ i, a < r i) (hm : StrictMono r) (hn : ∀ i, r i < 0)
    (i : Fin (d+1)) : cut r a i.val < cut r a (i.val+1) := by
  rcases i with ⟨j,hj⟩
  cases j with
  | zero =>
    by_cases hd : 0 < d
    · simpa [cut, hd] using har ⟨0,hd⟩
    · simpa [cut, hd] using ha
  | succ l =>
    have hld : l < d := by omega
    by_cases h : l+1 < d
    · simpa [cut,hld,h] using hm (show (⟨l,hld⟩ : Fin d) < ⟨l+1,h⟩ from Nat.lt_succ_self _)
    · simpa [cut,hld,h] using hn ⟨l,hld⟩

/-- Alternating signs at the specified factorization of p force all roots of q, including
one on either side of that list. The hypothesis is also valid when the list is empty. -/
theorem strict_of_signs {d : ℕ} {p q : ℝ[X]} (r : Fin d → ℝ) (hf : p = ∏ j, (X-C (r j)))
    (hm : StrictMono r) (hn : ∀ i, r i < 0)
    (hqm : 0 < q.leadingCoeff) (hqd : q.natDegree = d+1) (hq0 : 0 < q.eval 0)
    (hsg : ∀ i : Fin d, 0 < (-1 : ℝ)^(d-i.val)*q.eval (r i)) :
    LongCycleFinite.StrictNegativeInterlacing p q d := by
  classical
  have hpmon : p.Monic := hf ▸ monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)
  have hfar : ∀ᶠ x : ℝ in atBot, ∀ i, x < r i := Filter.eventually_all.mpr
    (fun i ↦ eventually_lt_atBot (r i))
  obtain ⟨a, hsign, ha, har⟩ := ((left_sign q _ hqd hqm).and
    ((eventually_lt_atBot (0 : ℝ)).and hfar)).exists
  have hc (j : ℕ) (hj : j ≤ d+1) : 0 < (-1 : ℝ)^(d+1-j)*q.eval (cut r a j) := by
    cases j with
    | zero => simpa [cut] using hsign
    | succ l =>
      by_cases hl : l<d
      · simpa [cut,hl] using hsg ⟨l,hl⟩
      · have : l=d := by omega
        subst l
        simpa [cut] using hq0
  have hroot (i : Fin (d+1)) : ∃ y, cut r a i.val < y ∧ y < cut r a (i.val+1) ∧ q.eval y = 0 := by
    apply LongCycleFinite.root_between q (cut_step r a ha har hm hn i)
    apply opposite (d-i.val)
    · simpa only [show d + 1 - i.val = d-i.val+1 by omega] using hc i.val (by omega)
    · simpa using hc (i.val+1) (by omega)
  choose s hs using hroot
  have hsmon : StrictMono s := Fin.strictMono_iff_lt_succ.mpr fun i ↦
    (hs i.castSucc).2.1.trans (hs i.succ).1
  have hsneg (i : Fin (d+1)) : s i < 0 := by
    apply (hs i).2.1.trans_le
    by_cases hi : i.val < d
    · simpa [cut,hi] using (hn ⟨_,hi⟩).le
    · simp [cut,hi]
  refine ⟨r,s,hpmon.leadingCoeff.symm ▸ one_ne_zero,hqm.ne',?_,
    LongCycleFinite.factor_of_degree_bound s (leadingCoeff_ne_zero.mp hqm.ne') hqd.le hsmon.injective
      (fun i ↦ (hs i).2.2),hm,hsmon,hn,hsneg,?_⟩
  · simpa [hpmon.leadingCoeff] using hf
  · intro i
    exact ⟨by simpa using (hs i.castSucc).2.1, by simpa using (hs i.succ).1⟩

end LongCycleBounds.Sturm
