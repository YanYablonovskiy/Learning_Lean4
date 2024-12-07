/-
Auto Bound Implicit Arguments

In the previous section, we have shown how implicit arguments make functions more convenient to use.

However, functions such as compose are still quite verbose to define.

Note that the universe polymorphic compose is even more verbose than the one previously defined.
-/
universe U V W
def compose {α : Type U} {β : Type V} {γ : Type W}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)


-- some of my attempts
def f₁ (x:Nat): Nat := by
  cases x
  . case zero => exact (Nat.zero)
  . case succ n => exact (2*(Nat.succ n))

def f₂ (x:Nat): Nat := by
  cases x
  . case zero => exact (Nat.zero)
  . case succ n => exact (3*(Nat.succ n))


#eval compose f₂ f₁ 1
#check compose f₂ f₁ 1
#reduce compose f₂ f₁ 1

 -- error #print compose f₂ f₁ 1

/-
You can avoid the universe command by providing the universe parameters when defining compose.
-/

def composeₛ.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

/-
Lean 4 supports a new feature called auto bound implicit arguments.

It makes functions such as compose much more convenient to write.

When Lean processes the header of a declaration, any unbound identifier is automatically
added as an implicit argument if it is a single lower case or greek letter.

With this feature we can write compose as
-/
def composeₐ (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @composeₐ
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
#check @compose
--@compose : {α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → (β → γ) → (α → β) → α → γ
#check @composeₛ
--@composeₛ : {α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → (β → γ) → (α → β) → α → γ

/-
Note that Lean inferred a more general type using Sort instead of Type.

Although we love this feature and use it extensively when implementing Lean, we realize some users may feel uncomfortable with it.

Thus, you can disable it using the command set_option autoImplicit false.
-/

--set_option autoImplicit false

/- The following definition produces `unknown identifier` errors -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
