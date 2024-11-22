/-
In this chapter, we describe an alternative approach to constructing proofs, using tactics.

A proof term is a representation of a mathematical proof; tactics are commands, or instructions,
that describe how to build such a proof.

Informally, you might begin a mathematical proof by saying

"to prove the forward direction, unfold the definition, apply the previous lemma, and simplify."

Just as these are instructions that tell the reader how to find the relevant proof, tactics
are instructions that tell Lean how to construct a proof term.

They naturally support an incremental style of writing proofs, in which you decompose a proof
and work on goals one step at a time.

We will describe proofs that consist of sequences of tactics as "tactic-style" proofs,
to contrast with the ways of writing proof terms we have seen so far, which we
will call "term-style" proofs. Each style has its own advantages and disadvantages.

For example, tactic-style proofs can be harder to read, because they require the reader to predict or guess the results of each instruction.

But they can also be shorter and easier to write.

Moreover, tactics offer a gateway to using Lean's automation, since automated procedures are themselves tactics.


-/


/-

Conceptually, stating a theorem or introducing a have statement creates a goal, namely, the goal of
constructing a term with the expected type.

For example, the following creates the goal of constructing a term of type p ∧ q ∧ p,
in a context with constants p q : Prop, hp : p and hq : q:

-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  sorry

-- p q : Prop
-- hp : p
-- hq : q
-- ⊢ p ∧ q ∧ p

/-
You can write this goal as follows:

p : Prop, q : Prop, hp : p, hq : q ⊢ p ∧ q ∧ p
-/

/-

Indeed, if you replace the "sorry" by an underscore in the example above, Lean will report that
it is exactly this goal that has been left unsolved.

-/

--theorem test₁ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := _

-- don't know how to synthesize placeholder
-- context:
-- p q : Prop
-- hp : p
-- hq : q
-- ⊢ p ∧ q ∧ p

/-

Ordinarily, you meet such a goal by writing an explicit term. But wherever a term is expected,
Lean allows us to insert instead a by <tactics> block, where <tactics> is a sequence of commands,
separated by semicolons or line breaks.

You can prove the theorem above in that way:

-/

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp

/-
We often put the by keyword on the preceding line, and write the example above as:
-/
theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

/-
The apply tactic applies an expression, viewed as denoting a function with zero or more arguments.

It unifies the conclusion (of the given expression) with the expression in the current goal,
and creates new goals for the remaining arguments, provided that no later arguments depend on them.

In the example above, the command apply And.intro yields two subgoals:
-/

/-
    case left
    p q : Prop
    hp : p
    hq : q
    ⊢ p

    case right
    p q : Prop
    hp : p
    hq : q
    ⊢ q ∧ p
-/

/-
The first goal is met with the command exact hp.

The exact command is just a variant of apply which signals that the expression given should fill the goal exactly.

It is good form to use it in a tactic proof, since its failure signals that something has gone wrong.

It is also more robust than apply, since the elaborator takes the expected type, given by the target of the goal,
into account when processing the expression that is being applied.

In this case, however, apply would work just as well.

-/

theorem test₄ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  apply hp
  apply And.intro
  exact hq
  exact hp

/-

You can see the resulting proof term with the #print command.

-/

#print test₄

/-
You can write a tactic script incrementally.

In VS Code, you can open a window to display messages by pressing Ctrl-Shift-Enter,
and that window will then show you the current goal whenever the cursor is in a tactic block.

In Emacs, you can see the goal at the end of any line by pressing C-c C-g, or see the remaining goal
in an incomplete proof by putting the cursor after the first character of the last tactic.

If the proof is incomplete, the token by is decorated with a red squiggly line, and the error
message contains the remaining goals.

Tactic commands can take compound expressions, not just single identifiers.

The following is a shorter version of the preceding proof:
-/

theorem test₅ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

/-
Unsurprisingly, it produces exactly the same proof term:
-/

#print test₅

/-
Multiple tactic applications can be written in a single line by concatenating with a semicolon.
-/
theorem test₆ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp


/-
Tactics that may produce multiple subgoals often tag them.

For example, the tactic apply And.intro tagged the first subgoal as left, and the second
as right.

In the case of the apply tactic, the tags are inferred from the parameters' names used
in the And.intro declaration.

You can structure your tactics using the notation case <tag> => <tactics>.

The following is a structured version of our first tactic proof in this chapter.
-/
theorem test₇ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

/-

You can solve the subgoal right before left using the case notation:

-/


theorem testₐ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro --suffices hq : q , hqp: q ∧ p from And.intro hq hqp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

  --apply names things for you; can you name it yourself?

  --apply is essentially like a 'suffices', leaving with goals after

/-
Note that Lean hides the other goals inside the case block.

We say it is "focusing" on the selected goal.

Moreover, Lean flags an error if the selected goal is not fully solved at the
end of the case block.
-/

/-
For simple subgoals, it may not be worth selecting a subgoal using its tag, but you may still want
to structure the proof.

Lean also provides the "bullet" notation . <tactics> (or · <tactics>) for structuring proofs:

-/

theorem test₉ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
