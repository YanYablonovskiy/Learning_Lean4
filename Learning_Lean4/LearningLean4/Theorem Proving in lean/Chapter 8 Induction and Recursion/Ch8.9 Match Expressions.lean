/-
Lean also provides a compiler for match-with expressions found in many
functional languages:
-/
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def isNotZero_tac (m : Nat) : Bool := by
  cases m with
  | zero => exact false
  | succ => exact true

/-
This does not look very different from an ordinary pattern matching definition, but the
point is that a match can be used anywhere in an expression, and with arbitrary arguments.
-/

def isNotZero' (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl

/-
Here is another example:
-/
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true  => 0
      | m+1, true  => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl

/-
Lean uses the match construct internally to implement pattern-matching in all parts of
the system.

Thus, all four of these definitions have the same net effect:
-/

def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n --eq compiler

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n --match

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n ---λ abstraction /deconstruction

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n --let binding, deconstruction

#eval bar₁ (3, 4)

#eval bar₂ (3, 4)

#eval bar₃ (3, 4)

#eval bar₄ (3, 4)

#eval bar₁ (3, 4) == bar₂ (3, 4) && bar₂ (3, 4) == bar₃ (3, 4) && bar₃ (3, 4) == bar₄ (3, 4)

/-
These variations are equally useful for destructing propositions:
-/

variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
