import SetTheory.Axioms
import SetTheory.Basic

noncomputable section

def ω : V := {x ∈ exists_inductive_set | fun x => ∀ X : V, is_inductive X → x ∈ X}

def is_irrfl (X : V) : Prop := ∀ x : V, x ∈ X → x ∉ x
def is_trans_rel (X : V) : Prop := ∀ x y z : V, x ∈ X → y ∈ X → z ∈ X → x ∈ y → y ∈ z → x ∈ z
def is_p_order (X : V) : Prop := is_irrfl X ∧ is_trans_rel X
def is_tot_rel (X : V) : Prop := ∀ x y : V, x ∈ X → y ∈ X → x ≠ y → x ∈ y ∨ y ∈ x
def is_l_order (X : V) : Prop := is_p_order X ∧ is_tot_rel X
def is_least (u X : V) : Prop := u ∈ X ∧ (∀ x : V, x ∈ X → u ≠ x → u ∈ x)
def has_least (X : V) : Prop := ∃ u : V, is_least u X
def is_w_order (X : V) : Prop := is_l_order X ∧ (∀ U : V, U ∈ 𝒫 X → U ≠ ∅ → has_least U)
def is_trans (X : V) : Prop := ∀ x : V, x ∈ X → x ⊆ X
def is_ord (X : V) : Prop := is_w_order X ∧ is_trans X

theorem ord_is_trans_rel {α : V} : is_ord α → is_trans_rel α := by
  intro h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1, h3⟩ := h1
  obtain ⟨h1, h4⟩ := h1
  obtain ⟨h1, h5⟩ := h1
  exact h5

theorem ord_is_total_rel {α : V} : is_ord α → is_tot_rel α := by
  intro h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1, h3⟩ := h1
  obtain ⟨h1, h4⟩ := h1
  exact h4

theorem subset_of_ord_has_least {U α : V} : is_ord α → U ⊆ α → U ≠ ∅ → has_least U := by
  intro hα huα hu
  obtain ⟨h1, h2⟩ := hα
  obtain ⟨h1, h3⟩ := h1
  rw [← elmt_of_p_set] at huα
  exact h3 U huα hu

theorem ord_is_trans {α : V} : is_ord α → is_trans α := by
  intro h
  obtain ⟨h1, h2⟩ := h
  exact h2

theorem elmt_of_elmt_of_ord {u x α} : is_ord α → u ∈ x → x ∈ α → u ∈ α := by
  intro hα hu hx
  exact elmt_of_subset (ord_is_trans hα x hx) hu

theorem elmt_of_ord_is_ord (X : V) : is_ord X → (∀ x : V, x ∈ X → is_ord x) := by
  intro hX x hxX
  constructor
  . constructor
    . constructor
      . constructor
        . sorry
        . intro u v w hux hvx hwx huv hvw
          have huX : u ∈ X := by exact elmt_of_elmt_of_ord hX hux hxX
          have hvX : v ∈ X := by exact elmt_of_elmt_of_ord hX hvx hxX
          have hwX : w ∈ X := by exact elmt_of_elmt_of_ord hX hwx hxX
          --exact ord_is_trans_rel hX
          sorry
      . intro u v hux hvx huv
        have huX : u ∈ X := by exact elmt_of_elmt_of_ord hX hux hxX
        have hvX : v ∈ X := by exact elmt_of_elmt_of_ord hX hvx hxX
        exact ord_is_total_rel hX u v huX hvX huv
    . intro U hU1 hU2
      rw [elmt_of_p_set] at hU1
      have hUX : U ⊆ X := by exact subset_trans hU1 (ord_is_trans hX x hxX)
      exact subset_of_ord_has_least hX hUX hU2
  . intro u hux v hvu
    have huX : u ∈ X := by exact elmt_of_elmt_of_ord hX hux hxX
    have hvX : v ∈ X := by exact elmt_of_elmt_of_ord hX hvu huX
    exact ord_is_trans_rel hX v u x hvX huX hxX hvu hux
