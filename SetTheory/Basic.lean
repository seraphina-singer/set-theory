import SetTheory.Axioms

section extensionality

theorem eq_iff_same_elmts {X Y : V} : X = Y ↔ ∀ u : V, u ∈ X ↔ u ∈ Y := by
  constructor
  . intro h u
    rw [h]
  . intro h
    exact ax_extensionality h

theorem elmt_of_subset {u X Y : V} : X ⊆ Y → u ∈ X → u ∈ Y := by
  intro h hu
  exact h u hu

theorem subset_self {X : V} : X ⊆ X := by
  intro u h
  exact h

theorem subset_trans {X Y Z : V} : X ⊆ Y → Y ⊆ Z → X ⊆ Z := by
  intro hXY hYZ
  intro u hu
  exact hYZ u (hXY u hu)

theorem eq_iff_subsets {X Y : V} : X = Y ↔ X ⊆ Y ∧ Y ⊆ X := by
  constructor
  . intro h
    rw [h]
    exact ⟨subset_self, subset_self⟩
  . intro h
    obtain ⟨h1, h2⟩ := h
    rw [eq_iff_same_elmts]
    intro u
    constructor
    . intro h
      exact h1 u h
    . intro h
      exact h2 u h

end extensionality

section pairing

theorem elmt_of_pair {u a b : V} : u ∈ {a, b} ↔ u = a ∨ u = b := by
  exact ax_pairing u 

theorem left_in_pair {a b : V} : a ∈ {a, b} := by
  rw [elmt_of_pair]
  left
  rfl

theorem right_in_pair {a b : V} : b ∈ {a, b} := by
  rw [elmt_of_pair]
  right
  rfl

theorem pair_unique {X a b : V} : X = {a, b} ↔ ∀ u : V, u ∈ X ↔ u = a ∨ u = b := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_pair
  . intro h
    rw [eq_iff_same_elmts]
    intro u
    rw [elmt_of_pair]
    exact h u

end pairing

section singleton

theorem elmt_of_single {u a : V} : u ∈ {a} ↔ u = a := by
  rw [← or_self (u = a)]
  exact elmt_of_pair

theorem input_in_single {a : V} : a ∈ {a} := by
  exact left_in_pair

theorem single_unique {X a : V} : X = {a} ↔ ∀ u : V, u ∈ X ↔ u = a := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_single
  . intro h
    rw [eq_iff_same_elmts]
    intro u
    rw [elmt_of_single]
    exact h u

end singleton

section separation

end separation

section empty_set

end empty_set

section Union

theorem elmt_of_Un {u X : V} : u ∈ ⋃ X ↔ ∃ x : V, x ∈ X ∧ u ∈ x := by
  exact ax_union u

theorem Un_unique {Y X : V} : Y = ⋃ X ↔ ∀ u : V, u ∈ Y ↔ ∃ x : V, x ∈ X ∧ u ∈ x := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_Un
  . intro h
    rw [eq_iff_same_elmts]
    intro u
    rw [elmt_of_Un]
    exact h u

end Union

section union

theorem elmt_of_un {u X Y : V} : u ∈ X ∪ Y ↔ u ∈ X ∨ u ∈ Y := by
  unfold un
  rw [elmt_of_Un]
  constructor
  . intro h
    obtain ⟨x, hu⟩ := h
    obtain ⟨hx, hu⟩ := hu
    rw [elmt_of_pair] at hx
    rcases hx with hX | hY
    . left
      rw [← hX]
      exact hu
    . right
      rw [← hY]
      exact hu
  . intro h
    rcases h with hX | hY
    . exists X
      exact ⟨left_in_pair, hX⟩
    . exists Y
      exact ⟨right_in_pair, hY⟩

theorem un_unique {Z X Y : V} : Z = X ∪ Y ↔ ∀ u : V, u ∈ Z ↔ u ∈ X ∨ u ∈ Y := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_un
  . intro h
    rw [eq_iff_same_elmts]
    intro u
    rw [elmt_of_un]
    exact h u

end union

section successor

theorem elmt_of_succ {u a : V} : u ∈ succ a ↔ u ∈ a ∨ u = a := by
  unfold succ
  rw [elmt_of_un]
  rw [elmt_of_single]

theorem succ_unique {X a : V} : X = succ a ↔ ∀ u : V, u ∈ X ↔ u ∈ a ∨ u = a := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_succ
  . intro h
    rw [eq_iff_same_elmts]
    intro u
    rw [elmt_of_succ]
    exact h u

end successor

section Intersection

end Intersection

section intersection

end intersection

section power_set

theorem elmt_of_p_set {U X : V} : U ∈ 𝒫 X ↔ U ⊆ X := by
  exact ax_power_set U

end power_set
