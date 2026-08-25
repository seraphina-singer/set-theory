import SetTheory.Axioms
import SetTheory.Basic

def abc : Type := {X : Nat // X % 2 = 0}
example : 2 = (⟨2, by rfl⟩ : abc).val := by rfl

noncomputable section

def ω : V := {x ∈ exists_inductive_set | fun x => ∀ X : V, inductive_set X → x ∈ X}

def is_irreflexive : V → Prop := fun X => ∀ x : X, x ∉ x
def is_transitive_relation : V → Prop := fun X => ∀ x y z : X, x ∈ y ∧ y ∈ z → x ∈ z
def is_p_order : V → Prop := fun X => is_irreflexive X ∧ is_transitive_relation X
def is_total_relation : V → Prop := fun X => ∀ x y : X, x ≠ y → x ∈ y ∨ y ∈ x
def is_l_order : V → Prop := fun X => is_p_order X ∧ is_total_relation X
def is_least : V → V → Prop := fun u => (fun X => u ∈ X ∧ ∀ x : X, u ≠ x → u ∈ x)
def is_w_order : V → Prop := fun X => (is_l_order X ∧ ∀ U : 𝒫 X, U ≠ ∅ → ∃ u : V, is_least u U)
def is_transitive : V → Prop := fun X => (∀ x : X, x ⊆ X)
def is_ord : V → Prop := fun X => (is_w_order X ∧ is_transitive X)
def On : Type := {X : V // is_ord X}

instance : Coe On V where
  coe α := α.val

theorem succ_irreflexive_is_irreflexive (X : V) : is_irreflexive X → is_irreflexive (succ X) := by
  unfold is_irreflexive
  intro h
  intro x
  obtain ⟨x, hx⟩ := x
  rw [element_of_successor] at hx
  rcases hx with h1 | h2
  . exact h ⟨x, h1⟩
  . rw [subtype_value]
    rw [h2]
    intro hc
    exact h ⟨X, hc⟩ hc

theorem succ_transitive_relation_is_transitive_relation (X : V) : is_transitive_relation X → is_transitive_relation (succ X) := by
  unfold is_transitive_relation
  intro h
  intro x y z
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, hz⟩ := z
  rw [subtype_value]
  rw [subtype_value]
  rw [subtype_value]
  rw [element_of_successor] at hx
  rw [element_of_successor] at hy
  rw [element_of_successor] at hz
  rcases hz with hz | hz
  . sorry
  . 

theorem succ_p_order_is_p_order {X : V} : is_p_order X → is_p_order (succ X) := by
  unfold is_p_order
  intro h
  intro x
  constructor
  . intro x
    obtain ⟨x, hx⟩ := x
    rw [element_of_successor] at hx
    rcases hx with h1 | h2
    exact h.left ⟨x, h1⟩
  sorry
