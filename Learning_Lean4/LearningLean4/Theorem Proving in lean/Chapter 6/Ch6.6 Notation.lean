/-
Identifiers in Lean can include any alphanumeric characters, including Greek characters
(other than ∀ , Σ , and λ , which, as we have seen, have a special meaning
in the dependent type theory).

They can also include subscripts, which can be entered by typing \_ followed
by the desired subscripted character.

Lean's parser is extensible, which is to say, we can define new notation.

Lean's syntax can be extended and customized by users at every level, ranging from basic
"mixfix" notations to custom elaborators.

In fact, all builtin syntax is parsed and processed using the same mechanisms
and APIs open to users.

In this section, we will describe and explain the various extension points.

While introducing new notations is a relatively rare feature in programming languages
and sometimes even frowned upon because of its potential to obscure code,
it is an invaluable tool in formalization for expressing established
conventions and notations of the respective field succinctly in code.

Going beyond basic notations, Lean's ability to factor out common boilerplate
code into (well-behaved) macros and to embed entire custom
domain specific languages (DSLs) to textually encode subproblems efficiently and
readably can be of great benefit to both programmers and proof engineers alike.
-/

/-
Notations and Precedence

The most basic syntax extension commands allow introducing new (or overloading existing)
prefix, infix, and postfix operators.
-/

section

infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
postfix:max "⁻¹"  => InvImage

/-
After the initial command name describing the operator kind (its "fixity"), we give the parsing precedence of
the operator preceded by a colon :, then a new or existing token surrounded by double quotes
(the whitespace is used for pretty printing), then the function this operator should be translated
to after the arrow =>.

The precedence is a natural number describing how "tightly" an operator binds to its arguments,
encoding the order of operations.

We can make this more precise by looking at the commands the above unfold to:
-/

end

notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
notation:1024 arg:1024 "⁻¹" => InvImage arg  -- `max` is a shorthand for precedence 1024

/-
It turns out that all commands from the first code block are in fact command macros translating to the more general notation command.

We will learn about writing such macros below.

Instead of a single token, the notation command accepts a mixed sequence of tokens and named term placeholders
with precedences, which can be referenced on the right-hand side of => and will be replaced by the respective
term parsed at that position.

A placeholder with precedence p accepts only notations with precedence at least p in that place.

Thus the string a + b + c cannot be parsed as the equivalent of a + (b + c) because the right-hand side
operand of an infixl notation has precedence one greater than the notation itself.

In contrast, infixr reuses the notation's precedence for the right-hand side operand,
so a ^ b ^ c can be parsed as a ^ (b ^ c).

Note that if we used notation directly to introduce an infix notation like
-/

notation:65 lhs:65 " ~ " rhs:65 =>  lhs rhs

/-
where the precedences do not sufficiently determine associativity, Lean's parser will default to right associativity.

More precisely, Lean's parser follows a local longest parse rule in the presence of ambiguous grammars:
when parsing the right-hand side of a ~ in a ~ b ~ c, it will continue parsing as long as possible
(as the current precedence allows), not stopping after b but parsing ~ c as well.

Thus the term is equivalent to a ~ (b ~ c).

As mentioned above, the notation command allows us to define arbitrary mixfix syntax freely mixing
tokens and placeholders.
-/

notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ =>  Γ e τ

/-
Placeholders without precedence default to 0, i.e. they accept notations of any precedence in their place.

If two notations overlap, we again apply the longest parse rule:
-/
notation:65 a " + " b:66 " + " c:66 => a + b - c

--#eval 1 + 2 + 3  -- 0

/-
The new notation is preferred to the binary notation since the latter, before chaining, would stop parsing after 1 + 2.

If there are multiple notations accepting the same longest parse, the choice will be delayed until elaboration,
which will fail unless exactly one overload is type-correct.
-/
