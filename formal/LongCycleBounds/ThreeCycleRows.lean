import LongCycleBounds.AnchoredRows
import LongCycleBounds.ThreeCycleLengths
import LongCycleBounds.InsertionBoundary

/-! Exact original rows in the three-cycle range, using the label at the anchor. -/
noncomputable section

namespace LongCycleBounds.Band

open LongCycles Polynomial Finset
open scoped Classical

/-- Evaluation of the original row divided by its degree-independent insertion denominator. -/
def rowAt (j k : ℕ) (t : ℝ) : ℝ := (enumerator j k).eval t / (1-t)^j

private theorem rowAt_zero (k : ℕ) (t : ℝ) : rowAt 0 k t = 1 := by
  have term (σ : Equiv.Perm (Fin 0)) :
      (if Allowed k σ then (X : ℝ[X])^excedances σ else 0) = 1 := by
    have ok : Allowed k σ := fun x ↦ Fin.elim0 x
    have h : excedances σ = 0 := by simp [excedances]
    simp [ok,h]
  unfold rowAt enumerator
  simp only [term, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero,
    one_nsmul, eval_one, pow_zero, div_one]

private theorem rowAt_below {j k : ℕ} (hj : 0 < j) (hjk : j < k) (t : ℝ) :
    rowAt j k t = 0 := by
  let x : Fin j := ⟨0,hj⟩
  have no (σ : Equiv.Perm (Fin j)) : ¬Allowed k σ := by
    intro h
    have large := (Insertion.allowed_iff_lengthAt σ).mp h x
    have small : Insertion.lengthAt σ x ≤ j := by
      simpa [Insertion.lengthAt] using (Function.minimalPeriod_le_card (f := σ) (x := x))
    omega
  simp [rowAt, enumerator, no]

private theorem rowAt_anchor_sum {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (t : ℝ) :
    rowAt j k t = ∑ a ∈ Icc k j,
      ((j-1).choose (a-1):ℝ) * moment a t * rowAt (j-a) k t := by
  let x : Fin j := ⟨0, by omega⟩
  conv_lhs => unfold rowAt
  rw [Anchored.anchored_row_recurrence hk x, eval_finsetSum, Finset.sum_div]
  apply sum_congr rfl
  intro a ha
  have le := (mem_Icc.mp ha).2
  rw [eval_mul, eval_mul, eval_C, eval_mul, eval_X]
  unfold moment rowAt
  rw [show (1-t)^j=(1-t)^a*(1-t)^(j-a) by rw [←pow_add]; congr 1; omega]
  ring

private theorem rowAt_anchor_tail {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (t : ℝ) :
    rowAt j k t = moment j t + ∑ a ∈ Icc k (j-k),
      ((j-1).choose (a-1):ℝ) * moment a t * rowAt (j-a) k t := by
  rw [rowAt_anchor_sum hk hj t]
  have interval : Icc k j = insert j (Icc k (j-1)) := by
    ext a
    simp only [mem_Icc,mem_insert]
    omega
  rw [interval, sum_insert (by simp; omega), Nat.choose_self, Nat.cast_one, Nat.sub_self,
    rowAt_zero, one_mul, mul_one]
  congr 1
  symm
  apply sum_subset
  · intro a ha
    obtain ⟨hl,hu⟩ := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨hl,by omega⟩
  · intro a ha hnot
    obtain ⟨hl,hu⟩ := mem_Icc.mp ha
    have hgt : j-k < a := by simp only [mem_Icc,hl,true_and] at hnot; omega
    rw [rowAt_below (by omega : 0 < j-a) (by omega : j-a < k), mul_zero]

private theorem rowAt_one_two {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (hhi : j < 3*k)
    {t : ℝ} (ht : t ≠ 1) :
    rowAt j k t = moment j t + 1/2 * ∑ a ∈ Icc k (j-k),
      (j.choose a:ℝ)*moment a t*moment (j-a) t := by
  unfold rowAt
  rw [actual_band_row hk hj hhi, eval_mul, eval_X, deformed_eval j k 1 t ht]

private theorem choose_anchor {j a : ℕ} (ha : 1 ≤ a) (haj : a ≤ j) :
    ((j-1).choose (a-1):ℝ) = ((a:ℝ)/(j:ℝ)) * (j.choose a:ℝ) := by
  have hw := Nat.add_one_mul_choose_eq (j-1) (a-1)
  rw [Nat.sub_add_cancel (ha.trans haj), Nat.sub_add_cancel ha] at hw
  have h : (j:ℝ)*((j-1).choose (a-1):ℝ) = (j.choose a:ℝ)*(a:ℝ) := by
    exact_mod_cast hw
  have hpos : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  linear_combination h

/-- Summing the anchor weights over both possible positions supplies the factor 1/2. -/
theorem anchored_pair_weight {j k : ℕ} (hk : 1 ≤ k) (hj : k ≤ j) (f : ℕ → ℝ) :
    (∑ a ∈ Icc k (j-k), ((j-1).choose (a-1):ℝ)*f a*f (j-a)) =
      1/2 * ∑ a ∈ Icc k (j-k), (j.choose a:ℝ)*f a*f (j-a) := by
  let F (a : ℕ) : ℝ := (j.choose a:ℝ)*f a*f (j-a)
  let G (a : ℕ) : ℝ := (a:ℝ)/(j:ℝ)*F a
  have gj (a : ℕ) (ha : a ∈ Icc k (j-k)) : F (j-a) = F a := by
    have hu := (mem_Icc.mp ha).2
    simp only [F, Nat.choose_symm (by omega : a≤j), show j-(j-a)=a by omega]
    ring
  have normalized : (∑ a ∈ Icc k (j-k), ((j-1).choose (a-1):ℝ)*f a*f (j-a)) =
      ∑ a ∈ Icc k (j-k), G a := by
    apply sum_congr rfl
    intro a ha
    obtain ⟨hl,hu⟩ := mem_Icc.mp ha
    rw [choose_anchor (by omega : 1≤a) (by omega : a≤j)]
    simp only [G,F]
    ring
  have reindex : (∑ a ∈ Icc k (j-k), G (j-a)) = ∑ a ∈ Icc k (j-k), G a := by
    apply sum_bij' (fun a _ ↦ j-a) (fun a _ ↦ j-a)
    all_goals intros a ha; obtain ⟨_,_⟩ := mem_Icc.mp ha
    all_goals first | exact mem_Icc.mpr ⟨by omega, by omega⟩ | congr 1 <;> omega
  have total : (∑ a ∈ Icc k (j-k), G a) + (∑ a ∈ Icc k (j-k), G (j-a)) =
      ∑ a ∈ Icc k (j-k), F a := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    have hi := (mem_Icc.mp ha).2
    have hpos : (j:ℝ) ≠ 0 := by exact_mod_cast (show j≠0 by omega)
    simp only [G,gj a ha,Nat.cast_sub (show a≤j by omega)]
    field_simp
    ring
  rw [reindex] at total
  rw [normalized]
  change _ = 1/2 * ∑ a ∈ Icc k (j-k), F a
  linarith only [total]

/-- Summing the anchor weights over all three positions supplies a factor 1/3.
Length tuples with repeated entries are included in the same reindexing. -/
theorem anchored_triple_weight {j k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℝ) :
    (∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
      ((j-1).choose (a-1):ℝ)*((j-a).choose b:ℝ)*f a*f b*f (j-a-b)) =
      1/3 * ∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
        (j.choose a:ℝ)*((j-a).choose b:ℝ)*f a*f b*f (j-a-b) := by
  let F (v : ℕ × ℕ) : ℝ :=
    (j.choose v.1:ℝ)*((j-v.1).choose v.2:ℝ)*f v.1*f v.2*f (j-v.1-v.2)
  let G₁ (v : ℕ × ℕ) : ℝ := (v.1:ℝ)/(j:ℝ)*F v
  let G₂ (v : ℕ × ℕ) : ℝ := (v.2:ℝ)/(j:ℝ)*F v
  let G₃ (v : ℕ × ℕ) : ℝ := ((j-v.1-v.2:ℕ):ℝ)/(j:ℝ)*F v
  have inv (v : ℕ × ℕ) (hv : v ∈ tripleWindow j k) : F (v.2,j-v.1-v.2) = F v := by
    obtain ⟨a,b⟩ := v
    obtain ⟨hl,hr,hs⟩ := mem_tripleWindow.mp hv
    have hc : (j.choose b:ℝ)*((j-b).choose (j-a-b):ℝ) =
        (j.choose a:ℝ)*((j-a).choose b:ℝ) := by
      exact_mod_cast choose_triple_rotate (show a+b+(j-a-b)=j by omega)
    dsimp [F]
    rw [show j-b-(j-a-b)=a by omega, hc]
    ring
  have anchored :
      (∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
        ((j-1).choose (a-1):ℝ)*((j-a).choose b:ℝ)*f a*f b*f (j-a-b)) =
        ∑ v ∈ tripleWindow j k, G₁ v := by
    rw [←sum_tripleWindow j k
      (fun v ↦ ((j-1).choose (v.1-1):ℝ)*((j-v.1).choose v.2:ℝ)*f v.1*f v.2*f (j-v.1-v.2))]
    apply sum_congr rfl
    rintro ⟨a,b⟩ hv
    obtain ⟨hl,hr,hs⟩ := mem_tripleWindow.mp hv
    rw [choose_anchor (by omega : 1≤a) (by omega : a≤j)]
    dsimp [G₁,F]
    ring
  have rotate₁ : (∑ v ∈ tripleWindow j k, G₂ v) = ∑ v ∈ tripleWindow j k, G₁ v := by
    calc
      _ = ∑ v ∈ tripleWindow j k, G₁ (v.2,j-v.1-v.2) := by
        apply sum_congr rfl
        intro v hv
        simp only [G₂,G₁,inv v hv]
      _ = _ := sum_triple_rotate hk G₁
  have rotate₂ : (∑ v ∈ tripleWindow j k, G₃ v) = ∑ v ∈ tripleWindow j k, G₂ v := by
    calc
      _ = ∑ v ∈ tripleWindow j k, G₂ (v.2,j-v.1-v.2) := by
        apply sum_congr rfl
        intro v hv
        simp only [G₃,G₂,inv v hv]
      _ = _ := sum_triple_rotate hk G₂
  have total : (∑ v ∈ tripleWindow j k, G₁ v) + (∑ v ∈ tripleWindow j k, G₂ v) +
      (∑ v ∈ tripleWindow j k, G₃ v) = ∑ v ∈ tripleWindow j k, F v := by
    rw [←sum_add_distrib, ←sum_add_distrib]
    apply sum_congr rfl
    rintro ⟨a,b⟩ hv
    obtain ⟨hl,hr,hs⟩ := mem_tripleWindow.mp hv
    have hpos : (j:ℝ) ≠ 0 := by exact_mod_cast (show j≠0 by omega)
    simp only [G₁,G₂,G₃,Nat.cast_sub (show a≤j by omega),Nat.cast_sub (show b≤j-a by omega)]
    field_simp
    ring
  rw [rotate₂,rotate₁] at total
  rw [anchored, ←sum_tripleWindow j k F]
  linarith only [total]

/-- Exact evaluation of the original permutation row below the four-cycle threshold.
After taking the anchor cycle, a nonempty complement is in the two-cycle range. -/
theorem rowAt_threeCycle {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (hhi : j < 4*k)
    {t : ℝ} (ht : t ≠ 1) :
    rowAt j k t =
      moment j t + 1/2 * (∑ a ∈ Icc k (j-k), (j.choose a:ℝ)*moment a t*moment (j-a) t) +
        1/6 * (∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
          (j.choose a:ℝ)*((j-a).choose b:ℝ)*moment a t*moment b t*moment (j-a-b) t) := by
  let f (a : ℕ) := moment a t
  let A (a : ℕ) : ℝ := (j-1).choose (a-1)
  let B (a : ℕ) : ℝ := ∑ b ∈ Icc k (j-a-k),
    A a*((j-a).choose b:ℝ)*f a*f b*f (j-a-b)
  have b_expand (a : ℕ) : A a*f a*(∑ b ∈ Icc k (j-a-k),
      ((j-a).choose b:ℝ)*f b*f (j-a-b)) = B a := by
    unfold B
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ ↦ by ring)
  have expand (a : ℕ) (ha : a ∈ Icc k (j-k)) :
      A a*f a*rowAt (j-a) k t = A a*f a*f (j-a) + 1/2*B a := by
    obtain ⟨hl,hu⟩ := mem_Icc.mp ha
    rw [rowAt_one_two hk (by omega) (by omega) ht]
    change A a*f a*(f (j-a) + 1/2*(∑ b ∈ Icc k (j-a-k),
      ((j-a).choose b:ℝ)*f b*f (j-a-b))) = _
    rw [← b_expand]
    ring
  have support : (∑ a ∈ Icc k (j-k), B a) = ∑ a ∈ Icc k (j-2*k), B a := by
    symm
    apply sum_subset
    · intro a ha
      obtain ⟨hl,hu⟩ := mem_Icc.mp ha
      exact mem_Icc.mpr ⟨hl,by omega⟩
    · intro a ha hnot
      obtain ⟨hl,hu⟩ := mem_Icc.mp ha
      have hgt : j-2*k < a := by simp only [mem_Icc,hl,true_and] at hnot; omega
      simp [B, Icc_eq_empty_of_lt (show j-a-k<k by omega)]
  rw [rowAt_anchor_tail hk hj t]
  change f j + (∑ a ∈ Icc k (j-k), A a*f a*rowAt (j-a) k t) = _
  rw [sum_congr rfl expand, sum_add_distrib, ←mul_sum, support]
  change f j + ((∑ a ∈ Icc k (j-k), ((j-1).choose (a-1):ℝ)*f a*f (j-a)) +
    1/2*(∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
      ((j-1).choose (a-1):ℝ)*((j-a).choose b:ℝ)*f a*f b*f (j-a-b))) = _
  rw [anchored_pair_weight (by omega : 1≤k) hj f, anchored_triple_weight (by omega : 1≤k) f]
  ring

/-- The real insertion-normalized row in terms of ordinary single-cycle moments. -/
theorem normalizedEnumerator_threeCycle {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (hhi : j < 4*k)
    (x : ℝ) :
    normalizedEnumerator j k x =
      cycleMoment j x + 1/2 * (∑ a ∈ Icc k (j-k), (j.choose a:ℝ)*cycleMoment a x*cycleMoment (j-a) x) +
        1/6 * (∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
          (j.choose a:ℝ)*((j-a).choose b:ℝ)*cycleMoment a x*cycleMoment b x*cycleMoment (j-a-b) x) := by
  have ht : -Real.exp (-x) ≠ 1 := by linarith [Real.exp_pos (-x)]
  exact rowAt_threeCycle hk hj hhi ht

/-- The original polynomial is the complete two-cycle expression plus the
ordered three-cycle polynomial with multiplicity divided by 3!. -/
theorem enumerator_threeCycle {j k : ℕ} (hk : 2 ≤ k) (hj : k ≤ j) (hhi : j < 4*k) :
    enumerator j k =
      X*deformedRow j k 1 + C (1/6:ℝ) *
        (∑ a ∈ Icc k (j-2*k), ∑ b ∈ Icc k (j-a-k),
          C ((j.choose a:ℝ)*((j-a).choose b:ℝ)) *
            (X*eulerian (a-1))*(X*eulerian (b-1))*(X*eulerian (j-a-b-1))) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Iio_infinite (0:ℝ)).mono
  intro t ht
  have hlt : t < 0 := ht
  have ht₁ : t ≠ 1 := by linarith
  have hden : (1-t)^j ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr ht₁.symm)
  apply (div_left_inj' hden).mp
  rw [show (enumerator j k).eval t/(1-t)^j = rowAt j k t from rfl, rowAt_threeCycle hk hj hhi ht₁,
    eval_add, eval_mul, eval_X, eval_mul, eval_C, add_div, deformed_eval j k 1 t ht₁]
  congr 1
  rw [mul_div_assoc]
  congr 1
  simp only [eval_finsetSum,Finset.sum_div]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  obtain ⟨al,au⟩ := mem_Icc.mp ha
  obtain ⟨bl,bu⟩ := mem_Icc.mp hb
  simp only [eval_mul,eval_C,eval_X,moment]
  have hp : (1-t)^j = (1-t)^a*(1-t)^b*(1-t)^(j-a-b) := by
    rw [←pow_add,←pow_add]
    congr 1
    omega
  rw [hp]
  ring

#print axioms anchored_pair_weight
#print axioms anchored_triple_weight
#print axioms rowAt_threeCycle
#print axioms normalizedEnumerator_threeCycle
#print axioms enumerator_threeCycle

end LongCycleBounds.Band
