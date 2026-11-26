import LongCycleBounds.InsertionBoundary

/-! Grouped two-cycle lattice coefficients and their uniform factorial-moment bound. -/
noncomputable section
namespace LongCycleBounds.Band
open Finset

/-- Contribution of a split of a total lattice label into parts u and v. -/
def windowKernel (j k : ℕ) (u v : ℝ) : ℝ :=
  ∑ a ∈ Icc k (j-k), (j.choose a : ℝ)*u^(a-1)*v^(j-a-1)

/-- Ratio of the grouped coefficient at a positive total label to the single-cycle coefficient. -/
def transferWeight (j k l : ℕ) : ℝ :=
  1 + (∑ h ∈ Icc 1 (l-1), windowKernel j k h (l-h : ℕ)) /
    (2*(l:ℝ)^(j-1))

private theorem marked_choose {j a : ℕ} (lo : 1≤a) (hi : a<j) :
    j.choose a * a * (j-a) = j*(j-1)*(j-2).choose (a-1) := by
  have h1 := Nat.add_one_mul_choose_eq (j-1) (a-1)
  have h2 := Nat.choose_mul_succ_eq (j-2) (a-1)
  rw [show j-1+1=j by omega, show a-1+1=a by omega] at h1
  rw [show j-2+1=j-1 by omega,show j-1-(a-1)=j-a by omega] at h2
  rw [← h1,Nat.mul_assoc,← h2]
  ac_rfl

/-- Summing the binomial coefficient after marking one element on each side of a split
gives j(j-1)(u+v)^(j-2); truncation and the window lower bound yield this inequality. -/
theorem windowKernel_factorial_bound {j k : ℕ} (hk : 1≤k) (hj : 2*k≤j)
    {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    (k:ℝ)*(j-k:ℕ)*windowKernel j k u v ≤
      (j:ℝ)*(j-1:ℕ)*(u+v)^(j-2) := by
  let s := Icc k (j-k)
  let f (i : ℕ) := u^i*v^(j-2-i)*((j-2).choose i:ℝ)
  have part (a : ℕ) (ha : a∈s) :
      (k:ℝ)*(j-k:ℕ)*((j.choose a : ℝ)*u^(a-1)*v^(j-a-1)) ≤
      (j:ℝ)*(j-1:ℕ)*f (a-1) := by
    obtain ⟨hl,hr⟩ := mem_Icc.mp ha
    have ha' : a<j := by omega
    have aw : (k:ℝ)*(j-k:ℕ) ≤ (a:ℝ)*(j-a:ℕ) := by
      rw [Nat.cast_sub (by omega : k≤j), Nat.cast_sub (by omega : a≤j)]
      have h1 : (0:ℝ)≤a-k := sub_nonneg.mpr (by exact_mod_cast hl)
      have h2 : (0:ℝ)≤j-k-a := by
        have : (a:ℝ)+k≤j := by exact_mod_cast (by omega : a+k≤j)
        linarith
      nlinarith [mul_nonneg h1 h2]
    have he : (j.choose a:ℝ)*a*(j-a:ℕ) =
        (j:ℝ)*(j-1:ℕ)*((j-2).choose (a-1):ℝ) := by exact_mod_cast marked_choose (by omega) ha'
    calc _ ≤ ((a:ℝ)*(j-a:ℕ))*((j.choose a:ℝ)*u^(a-1)*v^(j-a-1)) :=
             mul_le_mul_of_nonneg_right aw (by positivity)
         _ = (j:ℝ)*(j-1:ℕ)*f (a-1) := by
             simp only [f,show j-2-(a-1)=j-a-1 by omega]
             linear_combination he * u^(a-1)*v^(j-a-1)
  have imageSum : ∑ a ∈ s, f (a-1) = ∑ i ∈ s.image (fun a ↦ a-1), f i := by
    rw [sum_image]
    intro a ha b hb h
    have := (mem_Icc.mp ha).1
    have := (mem_Icc.mp hb).1
    change a-1=b-1 at h
    omega
  have sub : s.image (fun a ↦ a-1) ⊆ range (j-2+1) := by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hi
    obtain ⟨_,_⟩ := mem_Icc.mp ha
    exact mem_range.mpr (by omega)
  have total : ∑ i ∈ range (j-2+1), f i = (u+v)^(j-2) := by
    rw [add_pow]
  calc _ = ∑ a ∈ s, (k:ℝ)*(j-k:ℕ)*((j.choose a:ℝ)*u^(a-1)*v^(j-a-1)) := by
           rw [windowKernel,mul_sum]
       _ ≤ ∑ a ∈ s, (j:ℝ)*(j-1:ℕ)*f (a-1) := sum_le_sum part
       _ = (j:ℝ)*(j-1:ℕ)*∑ a ∈ s, f (a-1) := by rw [mul_sum]
       _ ≤ (j:ℝ)*(j-1:ℕ)*(u+v)^(j-2) := by
           rw [imageSum,← total]
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           apply sum_le_sum_of_subset_of_nonneg sub
           intro i _ _
           dsimp [f]
           positivity

private theorem windowKernel_nonneg (j k : ℕ) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    0≤ windowKernel j k u v := by
  apply sum_nonneg
  intro a _
  positivity

/-- Keeping the number l-1 of positive ordered splits gives a finite-label sharpening. -/
theorem transferWeight_le_marked_ratio {j k l : ℕ} (hk : 1≤k) (hj : 2*k≤j) (hl : 1≤l) :
    transferWeight j k l ≤ 1 + ((l-1:ℕ):ℝ)*j*(j-1:ℕ)/(2*l*k*(j-k:ℕ)) := by
  have each (h : ℕ) (hm : h∈Icc 1 (l-1)) :
      (k:ℝ)*(j-k:ℕ)*windowKernel j k h (l-h:ℕ) ≤ (j:ℝ)*(j-1:ℕ)*(l:ℝ)^(j-2) := by
    have := (mem_Icc.mp hm).2
    have b := windowKernel_factorial_bound (u:=(h:ℝ)) (v:=((l-h:ℕ):ℝ)) hk hj (by positivity) (by positivity)
    rwa [show (h:ℝ)+((l-h:ℕ):ℝ)=l by rw [Nat.cast_sub (by omega : h≤l),add_sub_cancel]] at b
  have hsum := sum_le_sum each
  rw [←mul_sum] at hsum
  simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hsum
  have lpos : 0<(l:ℝ) := by exact_mod_cast (by omega : 0<l)
  have kpos : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have bpos : 0<((j-k:ℕ):ℝ) := by exact_mod_cast (by omega : 0<j-k)
  have power : (l:ℝ)^(j-1) = (l:ℝ)^(j-2)*l := by rw [←pow_succ]; congr 1; omega
  rw [transferWeight,add_le_add_iff_left,div_le_div_iff₀ (by positivity) (by positivity),power]
  convert mul_le_mul_of_nonneg_left hsum (show (0:ℝ)≤2*l by positivity) using 1 <;> ring

/-- The grouped multiplier is uniformly bounded, independently of the total label. -/
theorem transferWeight_bounds {j k l : ℕ} (hk : 1≤k) (hj : k≤j) (h3 : j≤3*k) (hl : 1≤l) :
    1≤transferWeight j k l ∧ transferWeight j k l ≤ 13/4 := by
  unfold transferWeight
  have den : 0<2*(l:ℝ)^(j-1) := by
    have : 0<(l:ℝ) := by exact_mod_cast (by omega : 0<l)
    positivity
  constructor
  · apply le_add_of_nonneg_right
    exact div_nonneg (sum_nonneg fun h _ ↦ windowKernel_nonneg _ _ (by positivity) (by positivity)) den.le
  by_cases hj2 : 2*k≤j
  · have scalar : 2*(j:ℝ)*(j-1:ℕ) ≤ 9*(k:ℝ)*(j-k:ℕ) := by
      rw [Nat.cast_sub (by omega : 1≤j), Nat.cast_sub hj]
      have h1 : (0:ℝ)≤3*k-j := by
        have : (j:ℝ)≤3*k := by exact_mod_cast h3
        linarith
      have h2 : (0:ℝ)≤2*j-3*k := by
        have : 2*(k:ℝ)≤j := by exact_mod_cast hj2
        linarith
      push_cast
      nlinarith [mul_nonneg h1 h2]
    apply (transferWeight_le_marked_ratio hk hj2 hl).trans
    have hl0 : 0<(l:ℝ) := by exact_mod_cast (by omega : 0<l)
    have hk0 : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
    have hb0 : 0<((j-k:ℕ):ℝ) := by exact_mod_cast (by omega : 0<j-k)
    have ls : ((l-1:ℕ):ℝ)≤l := by exact_mod_cast Nat.sub_le l 1
    rw [show (13/4:ℝ)=1+9/4 by norm_num,add_le_add_iff_left,div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left scalar hl0.le,
      mul_le_mul_of_nonneg_right ls (by positivity : 0≤(j:ℝ)*(j-1:ℕ))]
  · have empty : Icc k (j-k) = ∅ := Icc_eq_empty_of_lt (by omega)
    simp [windowKernel,empty]
    norm_num

private def splitCoeff (a b l : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 (l-1), (h:ℝ)^(a-1)*((l-h:ℕ):ℝ)^(b-1)

private theorem transferWeight_coefficient {j k : ℕ} (hj : 2≤j) (l : ℕ) :
    (l:ℝ)^(j-1)*transferWeight j k l =
      (l:ℝ)^(j-1) + 1/2*∑ a ∈ Icc k (j-k), (j.choose a:ℝ)*splitCoeff a (j-a) l := by
  rcases l with _|l
  · simp [transferWeight,splitCoeff,zero_pow (by omega : j-1≠0)]
  have hs : (∑ h ∈ Icc 1 (l.succ-1), windowKernel j k h (l.succ-h:ℕ)) =
      ∑ a ∈ Icc k (j-k), (j.choose a:ℝ)*splitCoeff a (j-a) l.succ := by
    unfold windowKernel splitCoeff
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [mul_sum]
    apply sum_congr rfl
    intro h _
    ring
  rw [transferWeight,hs]
  have h : (l.succ:ℝ)^(j-1) ≠ 0 := by positivity
  field_simp

private def seriesTerm (a : ℕ) (t : ℝ) (l : ℕ) : ℝ := (l:ℝ)^(a-1)*t^l

private theorem seriesTerm_hasSum {a : ℕ} (ha : 2≤a) {t : ℝ} (ht : ‖t‖<1) :
    HasSum (seriesTerm a t) (moment a t) := by
  have he := eulerian_eq_powerSeries (a-1) (by omega) t ht
  rw [show a-1+1=a by omega] at he
  rw [moment,he]
  exact (summable_pow_mul_geometric_of_norm_lt_one (a-1) ht).hasSum

private theorem seriesTerm_summable_norm (a : ℕ) {t : ℝ} (ht : ‖t‖<1) :
    Summable fun l ↦ ‖seriesTerm a t l‖ := by
  simpa [seriesTerm,norm_mul,norm_pow] using
    (summable_pow_mul_geometric_of_norm_lt_one (a-1) (show ‖‖t‖‖<1 by simpa using ht))

private theorem product_hasSum {a b : ℕ} (ha : 2≤a) (hb : 2≤b) {t : ℝ} (ht : ‖t‖<1) :
    HasSum (fun l ↦ t^l * splitCoeff a b l) (moment a t*moment b t) := by
  have conv := hasSum_sum_range_mul_of_summable_norm (seriesTerm_summable_norm a ht)
    (seriesTerm_summable_norm b ht)
  rw [(seriesTerm_hasSum ha ht).tsum_eq,(seriesTerm_hasSum hb ht).tsum_eq] at conv
  apply conv.congr_fun
  intro l
  rw [splitCoeff,mul_sum]
  let F (h : ℕ) := t^l*((h:ℝ)^(a-1)*((l-h:ℕ):ℝ)^(b-1))
  have hsub : Icc 1 (l-1) ⊆ range (l+1) := by
    intro h hh
    have := (mem_Icc.mp hh).2
    exact mem_range.mpr (by omega)
  have ends : ∑ h ∈ Icc 1 (l-1), F h = ∑ h ∈ range (l+1), F h := by
    apply sum_subset hsub
    intro h hi ho
    have := mem_range.mp hi
    simp only [mem_Icc] at ho
    rcases (show h=0 ∨ h=l by omega) with rfl|rfl
    · simp [F, zero_pow (by omega : a-1≠0)]
    · simp [F, zero_pow (by omega : b-1≠0)]
  change ∑ h ∈ Icc 1 (l-1), F h = _
  rw [ends]
  apply sum_congr rfl
  intro h hh
  have hi := mem_range.mp hh
  dsimp [F,seriesTerm]
  rw [show t^l=t^h*t^(l-h) by rw [←pow_add]; congr 1; omega]
  ring

/-- Regrouping the Cauchy products of the actual two-cycle permutation row by their
total positive lattice label. The term with label zero vanishes. -/
theorem normalizedEnumerator_hasSum_transfer {j k : ℕ} (hk : 2≤k) (lo : k≤j)
    (hi : j<3*k) (x : ℝ) (hx : 0<x) :
    HasSum (fun l : ℕ ↦ (-Real.exp (-x))^l*(l:ℝ)^(j-1)*transferWeight j k l)
      (normalizedEnumerator j k x) := by
  let t := -Real.exp (-x)
  have ht : ‖t‖<1 := by
    change ‖-Real.exp (-x)‖<1
    rw [norm_neg,Real.norm_of_nonneg (Real.exp_nonneg _),Real.exp_lt_one_iff]
    linarith
  have hterm (a : ℕ) (ha : a∈Icc k (j-k)) :
      HasSum (fun l ↦ (j.choose a:ℝ)*(t^l*splitCoeff a (j-a) l))
        ((j.choose a:ℝ)*(moment a t*moment (j-a) t)) := by
    obtain ⟨al,ar⟩ := mem_Icc.mp ha
    exact (product_hasSum (by omega) (by omega) ht).mul_left _
  have total := (seriesTerm_hasSum (a:=j) (by omega) ht).add ((hasSum_sum hterm).mul_left (1/2:ℝ))
  have val : normalizedEnumerator j k x = moment j t +
      1/2*∑ a ∈ Icc k (j-k), (j.choose a:ℝ)*(moment a t*moment (j-a) t) := by
    dsimp only [normalizedEnumerator]
    rw [actual_band_row hk lo hi,Polynomial.eval_mul,Polynomial.eval_X,
        deformed_eval j k 1 _ (by linarith [Real.exp_pos (-x)])]
    simp only [mul_assoc]; rfl
  rw [val]
  apply total.congr_fun
  intro l
  change t^l*(l:ℝ)^(j-1)*transferWeight j k l = _
  rw [mul_assoc,transferWeight_coefficient (by omega : 2≤j),mul_add]
  simp only [seriesTerm]
  rw [mul_comm (t^l) ((l:ℝ)^(j-1))]
  congr 1
  rw [← mul_assoc, mul_comm (t^l) (1/2),mul_assoc,mul_sum]
  congr 1
  apply sum_congr rfl
  intro a _
  ring

#print axioms normalizedEnumerator_hasSum_transfer

#print axioms windowKernel_factorial_bound
#print axioms transferWeight_le_marked_ratio
#print axioms transferWeight_bounds
end LongCycleBounds.Band
