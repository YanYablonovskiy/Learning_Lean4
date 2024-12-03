/-
You are now familiar with the fundamentals of dependent type theory, both as a language for defining mathematical objects
and a language for constructing proofs.

The one thing you are missing is a mechanism for defining new data types.

We will fill this gap in the next chapter, which introduces the notion of an inductive data type.

But first, in this chapter, we take a break from the mechanics of type theory to explore some pragmatic
aspects of interacting with Lean.

Not all of the information found here will be useful to you right away.

We recommend skimming this section to get a sense of Lean's features, and then returning to it as necessary.
-/

/-
Importing Files

The goal of Lean's front end is to interpret user input, construct formal expressions,
and check that they are well-formed and type-correct.

Lean also supports the use of various editors, which provide continuous checking and feedback.

More information can be found on the Lean documentation pages.

The definitions and theorems in Lean's standard library are spread across multiple files.

Users may also wish to make use of additional libraries, or develop their own projects across multiple files.

When Lean starts, it automatically imports the contents of the library Init folder,
which includes a number of fundamental definitions and constructions.

As a result, most of the examples we present here work "out of the box."

If you want to use additional files, however, they need to be imported manually, via an import
statement at the beginning of a file. The command
-/

--import Bar.Baz.Blah

/-
imports the file Bar/Baz/Blah.olean, where the descriptions are interpreted relative to the Lean search path.

Information as to how the search path is determined can be found on the documentation pages.

By default, it includes the standard library directory, and (in some contexts) the root of the user's local project.

Importing is transitive. In other words, if you import Foo and Foo imports Bar, then you also have access to the contents of Bar, and do not need to import it explicitly.

-/
