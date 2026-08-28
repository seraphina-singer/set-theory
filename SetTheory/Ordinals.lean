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

theorem ord_is_irrfl {α x : V} : is_ord α → x ∈ α → x ∉ x := by
  intro h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1, h3⟩ := h1
  obtain ⟨h1, h4⟩ := h1
  obtain ⟨h1, h5⟩ := h1
  exact h1 x

theorem ord_is_trans_rel {α x y z: V} : is_ord α → x ∈ α → y ∈ α → z ∈ α → x ∈ y → y ∈ z → x ∈ z := by
  intro h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1, h3⟩ := h1
  obtain ⟨h1, h4⟩ := h1
  obtain ⟨h1, h5⟩ := h1
  exact h5 x y z

theorem ord_is_total_rel {α x y : V} : is_ord α → x ∈ α → y ∈ α → x ≠ y → x ∈ y ∨ y ∈ x := by
  intro h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1, h3⟩ := h1
  obtain ⟨h1, h4⟩ := h1
  exact h4 x y

theorem subset_of_ord_has_least {U α : V} : is_ord α → U ⊆ α → U ≠ ∅ → has_least U := by
  intro hα huα hu
  obtain ⟨h1, h2⟩ := hα
  obtain ⟨h1, h3⟩ := h1
  rw [← elmt_of_p_set] at huα
  exact h3 U huα hu

theorem ord_is_trans {α x : V} : is_ord α → x ∈ α → x ⊆ α := by
  intro h
  obtain ⟨h1, h2⟩ := h
  exact h2 x

theorem elmt_of_elmt_of_ord {u x α} : is_ord α → u ∈ x → x ∈ α → u ∈ α := by
  intro hα hu hx
  exact elmt_of_subset (ord_is_trans hα hx) hu

theorem elmt_of_ord_is_ord {α x : V} : is_ord α → x ∈ α → is_ord x := by
  intro hα hxα
  constructor
  . constructor
    . constructor
      . constructor
        . intro u hu
          have huα : u ∈ α := by exact elmt_of_elmt_of_ord hα hu hxα
          exact ord_is_irrfl hα huα
        . intro u v w hux hvx hwx huv hvw
          have huα : u ∈ α := by exact elmt_of_elmt_of_ord hα hux hxα
          have hvα : v ∈ α := by exact elmt_of_elmt_of_ord hα hvx hxα
          have hwα : w ∈ α := by exact elmt_of_elmt_of_ord hα hwx hxα
          exact ord_is_trans_rel hα huα hvα hwα huv hvw
      . intro u v hux hvx huv
        have huα : u ∈ α := by exact elmt_of_elmt_of_ord hα hux hxα
        have hvα : v ∈ α := by exact elmt_of_elmt_of_ord hα hvx hxα
        exact ord_is_total_rel hα huα hvα huv
    . intro U hU1 hU2
      rw [elmt_of_p_set] at hU1
      have hUα : U ⊆ α := by exact subset_trans hU1 (ord_is_trans hα hxα)
      exact subset_of_ord_has_least hα hUα hU2
  . intro u hux v hvu
    have huα : u ∈ α := by exact elmt_of_elmt_of_ord hα hux hxα
    have hvα : v ∈ α := by exact elmt_of_elmt_of_ord hα hvu huα
    exact ord_is_trans_rel hα hvα huα hxα hvu hux

theorem succ_of_ord_is_ord {α : V} : is_ord α → is_ord (succ α) := by
  intro hα
  constructor
  . constructor
    . constructor
      . constructor
        . intro x hxα hxx
          rw [elmt_of_succ] at hxα
          rcases hxα with hxα | hxα
          . exact ord_is_irrfl hα hxα hxx
          . rw [← hxα] at hα
            exact ord_is_irrfl hα hxx hxx
        . intro x y z hxα hyα hzα
          have hz : is_ord z := by
            rw [elmt_of_succ] at hzα
            rcases hzα with hzα | hzα
            . exact elmt_of_ord_is_ord hα hzα
            . rw [hzα]
              exact hα
          exact elmt_of_elmt_of_ord hz
      . intro x y hx hy hxy
        rw [elmt_of_succ] at hx
        rw [elmt_of_succ] at hy
        rcases hx with hx | hx
        . rcases hy with hy | hy
          . exact ord_is_total_rel hα hx hy hxy
          . left
            rw [hy]
            exact hx
        . rcases hy with hy | hy
          . right
            rw [hx]
            exact hy
          . exfalso
            rw [← hy] at hx
            exact hxy hx
    . intro U hUα hU
      rw [elmt_of_p_set] at hUα
      by_cases h : U ∩ α = ∅
      . have hU' : ∀ u : V, u ∈ U → u = α := by
          intro u
          intro hu
          have huα : u ∈ succ α := by exact hUα u hu
          rw [elmt_of_succ] at huα
          rcases huα with huα | huα
          . rw [empty_set_unique] at h
            specialize h u
            unfold not_is_element at h
            rw [elmt_of_inter] at h
            exfalso
            exact h ⟨hu, huα⟩
          . exact huα
        exists α
        constructor
        . by_cases hαU : α ∈ U
          . exact hαU
          . rw [non_empty_set] at hU
            obtain ⟨x, hx⟩ := hU
            have hxα : x = α := by exact hU' x hx
            rw [hxα] at hx
            exfalso
            exact hαU hx
        . intro x hxU hαx
          symm at hαx
          exfalso 
          exact hαx (hU' x hxU)
      . change U ∩ α ≠ ∅ at h
        have h2 : has_least (U ∩ α) := by
          exact subset_of_ord_has_least hα inter_subset_right h
        obtain ⟨u, hu⟩ := h2
        exists u
        obtain ⟨huU, hu⟩ := hu
        constructor
        . exact inter_subset_left u huU
        . intro x hx hux
          have hxα : x ∈ succ α := by exact elmt_of_subset hUα hx
          rw [elmt_of_succ] at hxα
          rcases hxα with hxα | hxα
          . exact hu x (elmt_of_inter.2 ⟨hx, hxα⟩) hux
          . rw [elmt_of_inter] at huU
            rw [hxα]
            exact huU.right
  . intro x hxα u hux
    rw [elmt_of_succ]
    left
    rw [elmt_of_succ] at hxα
    rcases hxα with hxα | hxα
    . exact elmt_of_elmt_of_ord hα hux hxα
    . rw [← hxα]
      exact hux
