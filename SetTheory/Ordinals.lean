import SetTheory.Axioms
import SetTheory.Basic

noncomputable section

def ω : V := {x ∈ exists_inductive_set | fun x => ∀ X : V, inductive_set X → x ∈ X}

def p_order : V → Prop := fun X => (∀ x y z : X, x ∉ x ∧ (x ∈ y ∧ y ∈ z → x ∈ z))
def l_order : V → Prop := fun X => (p_order X ∧ ∀ x y : X, (x ≠ y → (x ∈ y ∨ y ∈ x)))
def least : V → V → Prop := fun u => (fun X => (u ∈ X ∧ ∀ x : X, u ≠ x → u ∈ x))
def w_order : V → Prop := fun X => (l_order X ∧ ∀ U : 𝒫 X, U ≠ ∅ → ∃ u : V, least u U)
def transitive : V → Prop := fun X => (∀ x : X, x ⊆ X)
def is_ord : V → Prop := fun X => (w_order X ∧ transitive X)
def On : Type := {X : V // is_ord X}

instance : Coe On V where
  coe α := α.val

theorem succ_p_order_is_p_order {X : V} : p_order X → p_order (succ X) := by
  unfold p_order
  intro h
  intro x y z 
  sorry
