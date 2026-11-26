import LongCycleFinite.Rounded

namespace LongCycleFinite

structure Window where
  left : Dyadic
  right : Dyadic
  deriving Inhabited

def negativeSign (exponent : ℕ) : Bool := exponent % 2 != 0

def windowOK (p q : List ℤ) (exponent : ℕ) (w : Window) : Bool :=
  roundedSign (negativeSign exponent) p w.left &&
  roundedSign (!negativeSign exponent) p w.right &&
  roundedSign (negativeSign exponent) q w.left &&
  roundedSign (negativeSign exponent) q w.right

def signsOK (p q : List ℤ) : ℕ → List Window → Bool
  | _, [] => true
  | j, w :: ws => windowOK p q j w && signsOK p q (j - 1) ws

def orderOK : Dyadic → List Window → Bool
  | previous, [] => previous.less Dyadic.zero
  | previous, w :: ws =>
    previous.less w.left && w.left.less w.right && orderOK w.right ws

def boundaryOK (p q : List ℤ) (outer : Dyadic) (n : ℕ) : Bool :=
  decide (p.length = n + 1 ∧ q.length = n + 2) &&
  decide (0 < p.getLastD 0 ∧ 0 < q.getLastD 0) &&
  roundedSign (negativeSign (n + 1)) q outer && roundedSign false q Dyadic.zero

def caseOK (p q : List ℤ) (outer : Dyadic) (ws : List Window) : Bool :=
  boundaryOK p q outer ws.length && orderOK outer ws && signsOK p q ws.length ws

theorem signsOK_append (p q : List ℤ) (j : ℕ) (ws vs : List Window) :
    signsOK p q j (ws ++ vs) = (signsOK p q j ws && signsOK p q (j - ws.length) vs) := by
  induction ws generalizing j with
  | nil => simp [signsOK]
  | cons w ws ih =>
    simp [signsOK, ih, Nat.sub_sub, Nat.add_comm, Bool.and_assoc]

theorem signsOK_at {p q : List ℤ} {j : ℕ} {ws : List Window}
    (h : signsOK p q j ws = true) (i : Fin ws.length) :
    windowOK p q (j - i.val) (ws.get i) = true := by
  induction ws generalizing j with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    rcases Bool.and_eq_true_iff.mp h with ⟨h0, ht⟩
    refine Fin.cases ?_ (fun l ↦ ?_) i
    · simpa using h0
    · simpa [Nat.sub_sub, Nat.add_comm] using ih ht l

theorem orderOK_between {outer : Dyadic} {ws : List Window}
    (h : orderOK outer ws = true) :
    outer.value < 0 ∧
    (∀ i : Fin ws.length, outer.value < (ws.get i).left.value ∧
      (ws.get i).left.value < (ws.get i).right.value ∧ (ws.get i).right.value < 0) ∧
    ∀ i j : Fin ws.length, i < j → (ws.get i).right.value < (ws.get j).left.value := by
  induction ws generalizing outer with
  | nil =>
    refine ⟨?_, fun i ↦ Fin.elim0 i, fun i _ _ ↦ Fin.elim0 i⟩
    simpa [orderOK, Dyadic.less_iff] using h
  | cons w ws ih =>
    have h' : (outer.less w.left = true ∧ w.left.less w.right = true) ∧
        orderOK w.right ws = true := by simpa only [orderOK, Bool.and_eq_true_iff] using h
    obtain ⟨⟨h0, h1⟩, ht⟩ := h'
    have h0' := (Dyadic.less_iff outer w.left).mp h0
    have h1' := (Dyadic.less_iff w.left w.right).mp h1
    obtain ⟨h2, hs, ho⟩ := ih ht
    refine ⟨h0'.trans (h1'.trans h2), ?_, ?_⟩
    · intro i
      refine Fin.cases ⟨h0', h1', h2⟩ (fun j ↦ ?_) i
      exact ⟨h0'.trans (h1'.trans (hs j).1), (hs j).2⟩
    · intro i
      refine Fin.cases ?_ (fun a ↦ ?_) i
      · intro j
        refine Fin.cases ?_ (fun b ↦ ?_) j
        · intro h
          exact (lt_irrefl _ h).elim
        · intro _
          exact (hs b).1
      · intro j
        refine Fin.cases ?_ (fun b ↦ ?_) j
        · intro h
          exact (Fin.not_lt_zero _ h).elim
        · intro h
          exact ho a b (Fin.succ_lt_succ_iff.mp h)

#print axioms signsOK_at
#print axioms orderOK_between

end LongCycleFinite
