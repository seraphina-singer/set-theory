import SetTheory.Axioms

theorem subtype_value (x X : V) (h : x ∈ X) : (⟨x, h⟩ : X).val = x := by rfl

section extensionality

theorem eq_iff_same_elements (X Y : V) : X = Y ↔ ∀ u : V, u ∈ X ↔ u ∈ Y := by
  constructor
  . intro h
    intro u
    rw [h]
  . intro h
    exact ax_extensionality h

theorem subset_self (X : V) : X ⊆ X := by
  unfold is_subset
  intro u
  exact u.property

theorem eq_iff_subsets (X Y : V) : X = Y ↔ X ⊆ Y ∧ Y ⊆ X := by
  constructor
  . intro h
    rw [h]
    exact ⟨subset_self Y, subset_self Y⟩
  . intro h
    unfold is_subset at h
    obtain ⟨h1, h2⟩ := h
    rw [eq_iff_same_elements]
    intro u
    constructor
    . intro h
      exact h1 ⟨u, h⟩
    . intro h
      exact h2 ⟨u, h⟩

end extensionality

section pairing

theorem element_of_pair {u a b : V} : u ∈ {a, b} ↔ u = a ∨ u = b := by
  exact ax_pairing u

theorem left_in_pair {a b : V} : a ∈ {a, b} := by
  rw [element_of_pair]
  left
  rfl

theorem right_in_pair {a b : V} : b ∈ {a, b} := by
  rw [element_of_pair]
  right
  rfl

theorem pair_unique {X a b : V} : X = {a, b} ↔ ∀ u : V, u ∈ X ↔ u = a ∨ u = b := by
  constructor
  . intro h
    rw [h]
    intro u
    exact element_of_pair
  . intro h
    rw [eq_iff_same_elements]
    intro u
    rw [element_of_pair]
    exact h u

end pairing

section singleton

theorem element_of_singleton {u a : V} : u ∈ {a} ↔ u = a := by
  rw [← or_self (u = a)]
  exact ax_pairing u

theorem input_in_singleton {a : V} : a ∈ {a} := by
  exact left_in_pair

theorem singleton_unique {X a : V} : X = {a} ↔ ∀ u : V, u ∈ X ↔ u = a := by
  constructor
  . intro h
    rw [h]
    intro u
    exact element_of_singleton
  . intro h
    rw [eq_iff_same_elements]
    intro u
    rw [element_of_singleton]
    exact h u

end singleton

section separation

end separation

section empty_set

end empty_set

section Union

theorem element_of_Union {u X : V} : u ∈ ⋃ X ↔ ∃ x : X, u ∈ x := by
  exact ax_union u

theorem Union_unique {Y X : V} : Y = ⋃ X ↔ ∀ u : V, u ∈ Y ↔ ∃ x : X, u ∈ x := by
  constructor
  . intro h
    rw [h]
    intro u
    exact element_of_Union
  . intro h
    rw [eq_iff_same_elements]
    intro u
    rw [element_of_Union]
    exact h u

end Union

section union

theorem element_of_union {u X Y : V} : u ∈ X ∪ Y ↔ u ∈ X ∨ u ∈ Y := by
  unfold un
  rw [element_of_Union]
  constructor
  . intro h
    obtain ⟨x, hu⟩ := h
    obtain ⟨x, hx⟩ := x
    rw [element_of_pair] at hx
    rcases hx with hX | hY
    . left
      rw [← hX]
      exact hu
    . right
      rw [← hY]
      exact hu
  . intro h
    rcases h with hX | hY
    . exists ⟨X, left_in_pair⟩
    . exists ⟨Y, right_in_pair⟩

theorem union_unique {Z X Y : V} : Z = X ∪ Y ↔ ∀ u : V, u ∈ Z ↔ u ∈ X ∨ u ∈ Y := by
  constructor
  . intro h
    rw [h]
    intro u
    exact element_of_union
  . intro h
    rw [eq_iff_same_elements]
    intro u
    rw [element_of_union]
    exact h u

end union

section successor

theorem element_of_successor {u a : V} : u ∈ succ a ↔ u ∈ a ∨ u = a := by
  unfold succ
  rw [element_of_union]
  rw [element_of_singleton]

theorem successor_unique {X a : V} : X = succ a ↔ ∀ u : V, u ∈ X ↔ u ∈ a ∨ u = a := by
  constructor
  . intro h
    intro u
    rw [h]
    exact element_of_successor
  . intro h
    rw [eq_iff_same_elements]
    intro u
    rw [element_of_successor]
    exact h u

end successor
