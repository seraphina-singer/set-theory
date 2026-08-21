import SetTheory.Axioms

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
