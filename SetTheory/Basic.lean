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

theorem pair_unique {X a b : V} : X = {a, b} ↔ ∀ u : V, u ∈ X ↔ u = a ∨ u = b := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_pair
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_pair]
    exact h u

theorem left_in_pair {a b : V} : a ∈ {a, b} := by
  rw [elmt_of_pair]
  left
  rfl

theorem right_in_pair {a b : V} : b ∈ {a, b} := by
  rw [elmt_of_pair]
  right
  rfl

end pairing

section singleton

theorem elmt_of_single {u a : V} : u ∈ {a} ↔ u = a := by
  rw [← or_self (u = a)]
  exact elmt_of_pair

theorem single_unique {X a : V} : X = {a} ↔ ∀ u : V, u ∈ X ↔ u = a := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_single
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_single]
    exact h u

theorem set_in_single {a : V} : a ∈ {a} := by
  exact left_in_pair

end singleton

section separation

theorem elmt_of_separ {u X : V} {φ : V → Prop} : u ∈ {x ∈ X | φ} ↔ u ∈ X ∧ φ u := by
  exact ax_separation u

theorem separ_unique {Y X : V} {φ : V → Prop} : Y = {x ∈ X | φ} ↔ ∀ u : V, u ∈ Y ↔ u ∈ X ∧ φ u := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_separ
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_separ]
    exact h u

end separation

section empty_set

theorem empty_set_empty : ∀ x : V, x ∉ ∅ := by
  intro x h
  unfold «∅» at h
  rw [elmt_of_separ] at h
  obtain ⟨h1, h2⟩ := h
  exact h2

theorem empty_set_unique {X : V} : X = ∅ ↔ ∀ x : V, x ∉ X := by
  constructor
  . intro h
    rw [h]
    exact empty_set_empty
  . rw [eq_iff_same_elmts]
    intro h x
    constructor
    . intro hx
      exfalso
      exact h x hx
    . intro hx
      exfalso
      exact empty_set_empty x hx

theorem has_member_ne_empty {x X : V} : x ∈ X → X ≠ ∅ := by
  intro hx hX
  rw [empty_set_unique] at hX
  exact hX x hx

theorem ne_empty_has_member {X : V} : X ≠ ∅ → ∃ x : V, x ∈ X := by
  intro h
  by_cases h2  : ∃ x : V, x ∈ X
  . exact h2
  . rw [not_exists] at h2
    change ∀ x : V, x ∉ X at h2
    rw [← empty_set_unique] at h2
    exfalso
    exact h h2

theorem non_empty_set {X : V} : X ≠ ∅ ↔ ∃ x : V, x ∈ X := by
  constructor
  . exact ne_empty_has_member
  . intro h
    obtain ⟨x, hx⟩ := h
    exact has_member_ne_empty hx

end empty_set

section Union

theorem elmt_of_Un {u X : V} : u ∈ ⋃ X ↔ ∃ x : V, x ∈ X ∧ u ∈ x := by
  exact ax_union u

theorem Un_unique {Y X : V} : Y = ⋃ X ↔ ∀ u : V, u ∈ Y ↔ ∃ x : V, x ∈ X ∧ u ∈ x := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_Un
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_Un]
    exact h u

theorem elmt_subset_Un {x X : V} : x ∈ X → x ⊆ ⋃ X := by
  intro hx u hu
  rw [elmt_of_Un]
  exists x

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
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_un]
    exact h u

theorem left_subset_un {X Y : V} : X ⊆ X ∪ Y := by
  unfold un
  exact elmt_subset_Un left_in_pair

theorem right_subset_un {X Y : V} : Y ⊆ X ∪ Y := by
  unfold un
  exact elmt_subset_Un right_in_pair

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
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_succ]
    exact h u

end successor

section Intersection

theorem elmt_of_Inter {u X} : u ∈ ⋂ X ↔ X ≠ ∅ ∧ ∀ x : V, x ∈ X → u ∈ x := by
  unfold Intersect
  rw [elmt_of_separ]
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    constructor
    . rw [elmt_of_Un] at h1
      obtain ⟨x, ⟨hxX, hux⟩⟩ := h1
      exact has_member_ne_empty hxX
    . intro x
      exact h2 x
  . intro h
    obtain ⟨h1, h2⟩ := h
    constructor
    . rw [elmt_of_Un]
      rw [non_empty_set] at h1
      obtain ⟨x, hx⟩ := h1
      exists x
      exact ⟨hx, h2 x hx⟩
    . exact h2

theorem Inter_unique {Y X : V} : Y = ⋂ X ↔ ∀ u : V, u ∈ Y ↔ X ≠ ∅ ∧ ∀ x : V, x ∈ X → u ∈ x := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_Inter
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_Inter]
    exact h u

theorem Inter_subset_elmt {x X : V} : x ∈ X → ⋂ X ⊆ x := by
  intro hx u hu
  rw [elmt_of_Inter] at hu
  obtain ⟨hX, hu⟩ := hu
  exact hu x hx

end Intersection

section intersection

theorem elmt_of_inter {u X Y : V} : u ∈ X ∩ Y ↔ u ∈ X ∧ u ∈ Y := by
  unfold intersect
  rw [elmt_of_Inter]
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h2 X left_in_pair, h2 Y right_in_pair⟩
  . intro h
    obtain ⟨hX, hY⟩ := h
    constructor
    . exact has_member_ne_empty left_in_pair
    . intro x hx
      rw [elmt_of_pair] at hx
      rcases hx with hx | hx
      . rw [hx]
        exact hX
      . rw [hx]
        exact hY

theorem inter_unique {Z X Y : V} : Z = X ∩ Y ↔ ∀ u : V, u ∈ Z ↔ u ∈ X ∧ u ∈ Y := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_inter
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_inter]
    exact h u

theorem inter_subset_left {X Y : V} : X ∩ Y ⊆ X := by
  unfold intersect
  exact Inter_subset_elmt left_in_pair

theorem inter_subset_right {X Y : V} : X ∩ Y ⊆ Y := by
  unfold intersect
  exact Inter_subset_elmt right_in_pair

end intersection

section power_set

theorem elmt_of_p_set {U X : V} : U ∈ 𝒫 X ↔ U ⊆ X := by
  exact ax_power_set U

theorem p_set_unique {Y X : V} : Y = 𝒫 X ↔ ∀ U : V, U ∈ Y ↔ U ⊆ X := by
  constructor
  . intro h u
    rw [h]
    exact elmt_of_p_set
  . rw [eq_iff_same_elmts]
    intro h u
    rw [elmt_of_p_set]
    exact h u

end power_set
