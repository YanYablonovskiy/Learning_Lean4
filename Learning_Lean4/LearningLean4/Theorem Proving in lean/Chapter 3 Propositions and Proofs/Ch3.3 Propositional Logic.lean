/-

Lean defines all the standard logical connectives and notation.
The propositional connectives come with the following notation:

Ascii	     Unicode	   Editor shortcut	    Definition
True			 True
False			 False
Not	          ¬	            \not, \neg	       Not
/\	          ∧	            \and	             And
\/	          ∨	            \or	               Or
->	          →	            \to, \r, \imp	     Arrow Constructor/Implies
<->	           ↔	          \iff, \lr	         Iff

They all take values in Prop.
-/
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False -- ¬p → (p ↔ False)
#check p ∨ q → q ∨ p
