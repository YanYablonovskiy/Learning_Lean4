/-
Lean maintains a number of internal variables that can be set by users to control its behavior.

The syntax for doing so is as follows:
-/

/- set_option <name> <value> -/

/-
One very useful family of options controls the way Lean's pretty- printer displays terms.

The following options take an input of true or false:
-/

/-
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
-/

/-
As an example, the following settings yield much longer output:
-/
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1

/-
The command set_option pp.all true carries out these settings all at once, whereas set_option pp.all false
reverts to the previous values.

Pretty printing additional information is often very useful when you are debugging a proof,
or trying to understand a cryptic error message.

Too much information can be overwhelming, though, and Lean's defaults
are generally sufficient for ordinary interactions.
-/
