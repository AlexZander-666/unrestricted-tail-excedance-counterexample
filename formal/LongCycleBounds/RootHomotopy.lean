import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import LongCycleBounds.LinearRowInduction

namespace LongCycleBounds.RootHomotopy
open Polynomial Complex Set Filter Topology LongCycleFinite
noncomputable section

private theorem lower_product (s : Multiset ℝ) (z : ℂ) :
    |z.im|^s.card ≤ ‖((s.map (fun r ↦ (X-C r : ℝ[X]))).prod).aeval z‖ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.card_cons,Multiset.map_cons,Multiset.prod_cons,map_mul,map_sub,aeval_X,aeval_C,
      Complex.norm_mul,pow_succ]
    rw [mul_comm (|z.im|^_)]
    exact mul_le_mul (by simpa using Complex.abs_im_le_norm (z-(r:ℂ))) ih
      (by positivity) (norm_nonneg _)

/-- Monic real-rootedness is characterized by a uniform lower bound off the real axis. -/
theorem splits_iff_imaginary_bound {p : ℝ[X]} (hm : p.Monic) :
    p.Splits ↔ ∀ z : ℂ, |z.im|^p.natDegree≤‖p.aeval z‖ := by
  constructor
  · intro hs z
    have b := lower_product p.roots z
    rwa [←hs.natDegree_eq_card_roots,←hs.eq_prod_roots_of_monic hm] at b
  · intro bound
    let i : ℝ →+* ℂ := Complex.ofRealHom
    apply Splits.of_splits_map i (IsAlgClosed.splits _)
    intro z hz
    have hzero := (mem_roots (hm.map i).ne_zero).mp hz
    have eq : p.aeval z=0 := by
      change (p.map (algebraMap ℝ ℂ)).IsRoot z at hzero
      simpa only [IsRoot,eval_map_algebraMap] using hzero
    have le := bound z
    rw [eq,norm_zero] at le
    have im : z.im=0 := by
      by_contra ne
      exact (not_lt_of_ge le) (pow_pos (abs_pos.mpr ne) _)
    exact ⟨z.re,Complex.ext (by simp [i]) (by simp [i,im])⟩

/-- Closedness only requires continuity of polynomial values at each fixed complex point. -/
theorem isClosed_splitting {U : Type*} [TopologicalSpace U] {d : ℕ} (P : U → ℝ[X])
    (monic : ∀ u,(P u).Monic) (deg : ∀ u,(P u).natDegree=d)
    (hc : ∀ z : ℂ, Continuous fun u ↦ (P u).aeval z) : IsClosed {u | (P u).Splits} := by
  have eq : {u | (P u).Splits} = ⋂ z : ℂ, {u | |z.im|^d ≤ ‖(P u).aeval z‖} := by
    ext u
    simp only [mem_iInter,mem_ofPred_eq,splits_iff_imaginary_bound (monic u),deg u]
  rw [eq]
  exact isClosed_iInter fun z ↦ isClosed_le continuous_const (hc z).norm

private theorem brackets_near_simple {p : ℝ[X]} {r : ℝ} (root : p.IsRoot r)
    (simple : ¬p.derivative.IsRoot r) :
    ∀ᶠ e in 𝓝[>] (0:ℝ), p.eval (r-e)*p.eval (r+e)<0 := by
  obtain ⟨q,h⟩ := dvd_iff_isRoot.mpr root
  have qne : q.eval r≠0 := by
    simpa [h,derivative_mul,IsRoot] using simple
  have cont : Continuous (fun e : ℝ ↦ q.eval (r-e)*q.eval (r+e)) :=
    (q.continuous.comp (continuous_const.sub continuous_id)).mul
      (q.continuous.comp (continuous_const.add continuous_id))
  have good : ∀ᶠ e in 𝓝 (0:ℝ), 0<q.eval (r-e)*q.eval (r+e) :=
    (isOpen_lt continuous_const cont).mem_nhds (by simpa using mul_self_pos.mpr qne)
  filter_upwards [good.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with e he ep
  have pos : 0<e := ep
  rw [h]
  simp only [eval_mul,eval_sub,eval_X,eval_C]
  have eq : (r-e-r)*q.eval (r-e)*((r+e-r)*q.eval (r+e))=-(e^2)*(q.eval (r-e)*q.eval (r+e)) := by ring
  rw [eq]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos pos)) he

theorem sorted_simple_roots {p : ℝ[X]} {d : ℕ} (hs : p.Splits) (hm : p.Monic)
    (deg : p.natDegree=d) (simple : ∀ r, p.IsRoot r → ¬p.derivative.IsRoot r) :
    ∃ r : Fin d → ℝ, StrictMono r ∧ (∀ i, p.IsRoot (r i)) ∧ p=∏ i,(X-C (r i)) := by
  classical
  have nodup : p.roots.Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro r
    rw [count_roots]
    by_contra! mul
    obtain ⟨z,m⟩ := (one_lt_rootMultiplicity_iff_isRoot hm.ne_zero).mp mul
    exact simple r z m
  let a := p.roots.toFinset
  have size : a.card=d := by
    unfold a
    rw [Multiset.toFinset_card_of_nodup nodup,←hs.natDegree_eq_card_roots,deg]
  let r := a.orderEmbOfFin size
  have roots (i : Fin d) : p.IsRoot (r i) :=
    (mem_roots hm.ne_zero).mp (Multiset.mem_toFinset.mp (a.orderEmbOfFin_mem size i))
  refine ⟨r,r.strictMono,roots,?_⟩
  simpa only [hm.leadingCoeff,map_one,one_mul] using
    factor_of_degree_bound r hm.ne_zero deg.le r.injective roots

/-- Simple real roots persist locally in a monic family of fixed degree. -/
theorem isOpen_splitting {U : Type*} [TopologicalSpace U] {d : ℕ} (P : U → ℝ[X])
    (monic : ∀ u,(P u).Monic) (deg : ∀ u,(P u).natDegree=d)
    (hc : ∀ x : ℝ, Continuous fun u ↦ (P u).eval x)
    (simple : ∀ u r, (P u).IsRoot r → ¬(P u).derivative.IsRoot r) :
    IsOpen {u | (P u).Splits} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro u hs
  change (P u).Splits at hs
  obtain ⟨r,inc,roots,_⟩ := sorted_simple_roots hs (monic u) (deg u) (simple u)
  have signs : ∀ᶠ e in 𝓝[>] (0:ℝ), ∀ i : Fin d, (P u).eval (r i-e)*(P u).eval (r i+e)<0 :=
    eventually_all.mpr (fun i ↦ brackets_near_simple (roots i) (simple u _ (roots i)))
  have sep : ∀ᶠ e in 𝓝[>] (0:ℝ), ∀ i j : Fin d, i<j → r i+e<r j-e := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases h : i<j
    · have lt := inc h
      filter_upwards [Ioo_mem_nhdsGT (show 0<(r j-r i)/2 by linarith)] with e he _
      linarith only [he.2]
    · exact Eventually.of_forall (fun _ h' ↦ (h h').elim)
  obtain ⟨e,hsign,hsep,ep⟩ := (signs.and (sep.and (self_mem_nhdsWithin : Ioi (0:ℝ)∈𝓝[>] 0))).exists
  have through : ∀ᶠ v in 𝓝 u, ∀ i : Fin d, (P v).eval (r i-e)*(P v).eval (r i+e)<0 :=
    eventually_all.mpr (fun i ↦ (isOpen_lt ((hc _).mul (hc _)) continuous_const).mem_nhds (hsign i))
  filter_upwards [through] with v good
  have near (i : Fin d) := root_between (P v) (show r i-e<r i+e by have : 0<e := ep;linarith) (good i)
  choose y left right zero using near
  have inc : StrictMono y := fun i j h ↦ (right i).trans ((hsep i j h).trans (left j))
  have fac := factor_of_degree_bound y (monic v).ne_zero (deg v).le inc.injective zero
  rw [fac]
  exact Splits.mul (Splits.C _) (Splits.prod (fun _ _ ↦ Splits.X_sub_C _))

/-- The set of real-rooted parameters is clopen when every real root of each member is simple. -/
theorem splits_of_connected {U : Type*} [TopologicalSpace U] [PreconnectedSpace U] {d : ℕ}
    (P : U → ℝ[X]) (monic : ∀ u,(P u).Monic) (deg : ∀ u,(P u).natDegree=d)
    (complexCont : ∀ z : ℂ, Continuous fun u ↦ (P u).aeval z)
    (realCont : ∀ x : ℝ, Continuous fun u ↦ (P u).eval x)
    (simple : ∀ u r, (P u).IsRoot r → ¬(P u).derivative.IsRoot r)
    (seed : ∃ u,(P u).Splits) : ∀ u,(P u).Splits := by
  have all := IsClopen.eq_univ (s:={u | (P u).Splits})
    ⟨isClosed_splitting P monic deg complexCont,isOpen_splitting P monic deg realCont simple⟩ seed
  intro u
  exact (Set.ext_iff.mp all u).mpr (Set.mem_univ u)

/-- A strict sign along all negative predecessor roots propagates an entire adjacent pair.
Only a single anchor splitting for the predecessor and exclusion of nonnegative roots are needed. -/
theorem interlacing_of_connected_sign {U : Type*} [TopologicalSpace U] [PreconnectedSpace U]
    {d : ℕ} (P Q : U → ℝ[X]) (monic : ∀ u,(P u).Monic) (deg : ∀ u,(P u).natDegree=d)
    (complexCont : ∀ z : ℂ, Continuous fun u ↦ (P u).aeval z)
    (realCont : ∀ x : ℝ, Continuous fun u ↦ (P u).eval x)
    (neg : ∀ u t, (P u).IsRoot t → t<0)
    (nextMonic : ∀ u,(Q u).Monic) (nextDeg : ∀ u,(Q u).natDegree=d+1)
    (pos : ∀ u,0<(Q u).eval 0)
    (sign : ∀ u t, t<0 → (P u).eval t=0 → (Q u).eval t*(P u).derivative.eval t<0)
    (seed : ∃ u,(P u).Splits) :
    ∀ u,StrictNegativeInterlacing (P u) (Q u) d := by
  have simple (u : U) (t : ℝ) (h : (P u).IsRoot t) : ¬(P u).derivative.IsRoot t := by
    intro dbl
    have bad := sign u t (neg u t h) h
    simp only [IsRoot] at dbl
    simp [dbl] at bad
  have splits := splits_of_connected P monic deg complexCont realCont simple seed
  intro u
  obtain ⟨r,inc,roots,fac⟩ := sorted_simple_roots (splits u) (monic u) (deg u) (simple u)
  exact Band.linear_sturm_step r fac inc (fun i ↦ neg u _ (roots i)) (nextMonic u)
    (nextDeg u) (pos u) (sign u)

#print axioms interlacing_of_connected_sign
#print axioms isOpen_splitting
#print axioms splits_of_connected

#print axioms splits_iff_imaginary_bound
#print axioms isClosed_splitting
end
end LongCycleBounds.RootHomotopy
