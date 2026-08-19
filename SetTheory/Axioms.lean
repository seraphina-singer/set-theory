noncomputable section

opaque V : Type

@[instance] axiom ax_set_inhabited : Inhabited V

opaque is_element : V → V → Prop
infix:50 (priority := high) " ∈ " => is_element

instance : CoeSort V Type where
  coe X := {Y : V // Y ∈ X}
instance {X : V} : CoeOut (V → X) (V → V) where
  coe f := fun x => (f x)
instance {X : V} : Coe (V → V) (X → V) where
  coe f := fun x => (f x)
instance {X Y : V} : CoeOut (X → Y) (X → V) where
  coe f := fun x => (f x)

def not_is_element : V → V → Prop := fun x => (fun X => ¬ (x ∈ X))
infix:50 (priority := high) " ∉ " => not_is_element
def is_subset : V → V → Prop := fun X => (fun Y => (∀ u : X, u ∈ Y))
infix:50 (priority := high) " ⊆ " => is_subset
def not_is_subset : V → V → Prop := fun X => (fun Y => (¬ (X ⊆ Y)))
infix:50 (priority := high) " ⊈ " => not_is_subset

notation (name := ignore) "ignore " _ign:arg e:arg => e

axiom ax_exists_set : V

axiom ax_extensionality {X Y : V} : (∀ u : V, u ∈ X ↔ u ∈ Y) → X = Y

opaque pair : V → V → V
notation:max "{" a ", " b "}" => pair a b
axiom ax_pairing {a b : V} : ∀ u : V, u ∈ {a, b} ↔ u = a ∨ u = b

def single {a : V}: V := {a, a}
notation:max "{" a "}" => {a, a}

opaque separ : V → (V → Prop) → V
notation:max "{" X:arg " ∈ " Y:arg " | " φ:arg"}" => ignore X (separ Y φ)
axiom ax_separation {X : V} {φ : V → Prop} : ∀ u : V, u ∈ {x ∈ X | φ} ↔ u ∈ X ∧ φ u

def «∅» : V := {u ∈ ax_exists_set | fun _ ↦ False}
notation:max "∅" => «∅»

opaque union : V → V
prefix:65 (priority := high) "⋃ " => union
def union_2 : V → V → V := fun a => (fun b => (⋃ {a, b}))
infixr:70 (priority := high) " ∪ " => union_2
axiom ax_union {X : V} : ∀ u : V, u ∈ ⋃ X ↔ ∃ z : X, u ∈ z

def succ : V → V := fun a => (a ∪ {a})

def intersect : V → V := fun X => {Y ∈ (⋃ X) | fun u => ∀ x : X, u ∈ x}
prefix:65 (priority := high) "⋂ " => intersect
def intersect_2 : V → V → V := fun a => (fun b => (⋂ {a, b}))
infixr:70 (priority := high) " ∩ " => intersect_2

opaque power : V → V
prefix:65 (priority := high) "𝒫 " => power
axiom ax_power_set {X : V} : ∀ u : V, u ∈ 𝒫 X ↔ u ⊆ X

def inductive_set : V → Prop := fun X => (∅ ∈ X ∧ ∀ u : X, succ u ∈ X)
opaque exists_inductive_set : V
axiom ax_infinity : inductive_set exists_inductive_set

opaque replace : (X : V) → (X → V) → V
notation:max F "[" X "]" => replace X F
axiom ax_replacement {X : V} {F : X → V} : ∀ u : V, u ∈ F[X] ↔ ∃ x : X, F x = u
