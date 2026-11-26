import Mathlib

noncomputable section

namespace ClusterGraphAudit

open Polynomial

/-- The k-clique size is always positive; the empty list represents the empty graph. -/
abbrev Size := {m : ℕ // 0 < m}

/-- Exact interior inequalities in formula (7.5), with a common degree bound.
The zero polynomial automatically satisfies this predicate at any bound. -/
def CoefficientLC (p : Polynomial ℤ) (d : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i < d → p.coeff (i-1) * p.coeff (i+1) ≤ (p.coeff i)^2

/-- Signed complete-component Möbius row, formula (3.4). -/
def mobiusRow (m : Size) : Polynomial ℤ :=
  ∏ j ∈ Finset.Ico 1 m.val, (C ((m.val - j : ℕ) : ℤ) + C (j : ℤ) * X)

/-- Strict adjacent descents, as used in the original Eulerian polynomial. -/
def descents {m : ℕ} (π : Equiv.Perm (Fin m)) : ℕ := by
  classical
  exact (Finset.univ.filter fun j : Fin m =>
    ∃ l : Fin m, l.val = j.val + 1 ∧ π l < π j).card

def eulerian (m : Size) : Polynomial ℤ :=
  ∑ π : Equiv.Perm (Fin m.val), X ^ descents π

def degreeBound (sizes : List Size) : ℕ :=
  (sizes.map (fun m => m.val - 1)).sum

def productDifference (sizes : List Size) : Polynomial ℤ :=
  (sizes.map mobiusRow).prod - (sizes.map eulerian).prod

/-- Algebraic target on the product side of the two original graph bridges. -/
def ProductClaim : Prop :=
  ∀ sizes : List Size, CoefficientLC (productDifference sizes) (degreeBound sizes)

/-- Every connected component of an abstract finite simple graph is complete. -/
def IsCluster {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y, x ≠ y → G.Reachable x y → G.Adj x y

def componentCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := Nat.card G.ConnectedComponent

/-- Type of each original graph invariant, before the graph-dependent sign is applied. -/
abbrev GraphPolynomial := {n : ℕ} → SimpleGraph (Fin n) → Polynomial ℤ

/-- A target template. Instantiate mu and h using the weighted-bond-poset
Möbius sum and graph-associahedron face sum, respectively, before proving the graph theorem. -/
def GraphTarget (mu h : GraphPolynomial) : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), IsCluster G →
    CoefficientLC
      (C ((-1 : ℤ)^(n - componentCount G)) * mu G - h G)
      (n - componentCount G)

/-- An actual union of cliques on a labelled sigma type. -/
abbrev Vertex (sizes : List Size) := (j : Fin sizes.length) × Fin (sizes.get j).val

def unionOfCliques (sizes : List Size) : SimpleGraph (Vertex sizes) where
  Adj x y := x.1 = y.1 ∧ x ≠ y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- Explicit obligations for the two graph invariants and their simultaneous
identification on the same actual graph decomposition. -/
def GraphBridges (mu h : GraphPolynomial) : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), IsCluster G →
    ∃ sizes : List Size,
      Nonempty (G ≃g unionOfCliques sizes) ∧ n - componentCount G = degreeBound sizes ∧
      C ((-1 : ℤ)^(n - componentCount G)) * mu G = (sizes.map mobiusRow).prod ∧
      h G = (sizes.map eulerian).prod

theorem graphTarget_of_bridges {mu h : GraphPolynomial}
    (hprod : ProductClaim) (hb : GraphBridges mu h) : GraphTarget mu h := by
  intro n G hG
  obtain ⟨s, _, hdeg, hp, hq⟩ := hb n G hG
  rw [hp, hq, hdeg]
  exact hprod s

end ClusterGraphAudit
