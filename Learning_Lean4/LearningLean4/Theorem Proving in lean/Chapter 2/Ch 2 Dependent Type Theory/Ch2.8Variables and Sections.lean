--Consider the following three function definitions:

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

  --Lean provides you with the variable command to make such declarations look more compact:
  
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose_c := g (f x)
def doTwice_c := h (h x)
def doThrice_c := h (h (h x))

#print compose_c
#print doTwice_c
#print doThrice_c

--Printing them out shows that all three groups of definitions have exactly the same effect.

--The variable command instructs Lean to insert the declared variables as bound variables 
--in definitions that refer to them by name. Lean is smart enough to figure out which variables
--are used explicitly or implicitly in a definition. You can therefore proceed 
--as though α, β, γ, g, f, h, and x are fixed objects when you write your definitions,
--and let Lean abstract the definitions for you automatically.

--When declared in this way, a variable stays in scope
--until the end of the file you are working on. Sometimes, however,
--it is useful to limit the scope of a variable.
--For that purpose, Lean provides the notion of a section:

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose_s := g (f x)
  def doTwice_s := h (h x)
  def doThrice_s := h (h (h x))
end useful

--When the section is closed, the variables go out of scope, and cannot be referenced any more.

--You do not have to indent the lines within a section. Nor do you have to name a section, 
--which is to say, you can use an anonymous section / end pair.
--If you do name a section, however, you have to close it using the same name. 
--Sections can also be nested, which allows you to declare new variables incrementally.