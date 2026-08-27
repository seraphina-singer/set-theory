noncomputable section axioms

opaque V : Type

@[instance] axiom ax_set_inhabited : Inhabited V

opaque is_element : V → V → Prop
infix:50 (priority := high) " ∈ " => is_element

def not_is_element (x X : V) : Prop := ¬ (x ∈ X)
infix:50 (priority := high) " ∉ " => not_is_element
def is_subset (X Y : V) : Prop := ∀ u : V, u ∈ X → u ∈ Y
infix:50 (priority := high) " ⊆ " => is_subset
def not_is_subset (X Y : V) : Prop := ¬ (X ⊆ Y)
infix:50 (priority := high) " ⊈ " => not_is_subset

notation (name := ignore) "ignore " _ign:arg e:arg => e

axiom ax_exists_set : V

axiom ax_extensionality {X Y : V} : (∀ u : V, u ∈ X ↔ u ∈ Y) → X = Y

opaque pair : V → V → V
notation:max "{" a ", " b "}" => pair a b
axiom ax_pairing {a b : V} : ∀ u : V, u ∈ {a, b} ↔ u = a ∨ u = b

def single (a : V) : V := {a, a}
notation:max "{" a "}" => single a

opaque separ : V → (V → Prop) → V
notation:max "{" x:arg " ∈ " X:arg " | " φ:arg"}" => ignore x (separ X φ)
axiom ax_separation {X : V} {φ : V → Prop} : ∀ u : V, u ∈ {x ∈ X | φ} ↔ u ∈ X ∧ φ u

def «∅» : V := {u ∈ ax_exists_set | fun _ ↦ False}
notation:max "∅" => «∅»

opaque Un : V → V
prefix:65 (priority := high) "⋃ " => Un
def un (X Y : V) : V := ⋃ {X, Y}
infixr:70 (priority := high) " ∪ " => un
axiom ax_union {X : V} : ∀ u : V, u ∈ ⋃ X ↔ ∃ x : V, x ∈ X ∧ u ∈ x

def succ (a : V) : V := a ∪ {a}

def Intersect (X : V) : V := {Y ∈ (⋃ X) | fun u => ∀ x : V, x ∈ X → u ∈ x}
prefix:65 (priority := high) "⋂ " => Intersect
def intersect (X Y : V) : V := ⋂ {X, Y}
infixr:70 (priority := high) " ∩ " => intersect

opaque power : V → V
prefix:65 (priority := high) "𝒫 " => power
axiom ax_power_set {X : V} : ∀ u : V, u ∈ 𝒫 X ↔ u ⊆ X

def is_inductive : V → Prop := fun X => (∅ ∈ X → ∀ u : V, u ∈ X → succ u ∈ X)
opaque exists_inductive_set : V
axiom ax_infinity : is_inductive exists_inductive_set

opaque replace : V → (V → V) → V
notation:max F "[" X "]" => replace X F
axiom ax_replacement {X : V} {F : V → V} : ∀ u : V, u ∈ F[X] ↔ ∃ x : V, x ∈ X ∧ F x = u

end axioms
