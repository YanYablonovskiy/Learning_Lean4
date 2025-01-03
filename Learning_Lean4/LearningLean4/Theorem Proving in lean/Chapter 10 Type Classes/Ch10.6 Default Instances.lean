
/-
Default Instances:

In the class HMul, the parameters α and β are treated as input values.

Thus, type class synthesis only starts after these two types are known.

This may often be too restrictive.
-/
namespace ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

-- Error "typeclass instance problem is stuck, it is often due to metavariables HMul ?m.89 ?m.90 ?m.91"
#check_failure fun y => xs.map (fun x => hMul x y)


/-

The instance HMul is not synthesized by Lean because the type of y has not been provided.

However, it is natural to assume that the type of y and x should be the same in this kind
of situation. We can achieve exactly that using default instances.


-/



@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul



#check fun y => xs.map (fun x => hMul x y)  -- Int → List Int

--assumes y is Int as default, maps the list entry x known as Int , assumes y is Int


/-
By tagging the instance above with the attribute default_instance,
we are instructing Lean to use this instance on pending type class synthesis problems.

The actual Lean implementation defines homogeneous and heterogeneous classes for
arithmetical operators.

Moreover, a+b, a*b, a-b, a/b, and a%b are notations for the heterogeneous versions.

The instance OfNat Nat n is the default instance (with priority 100) for the OfNat class.

This is why the numeral 2 has type Nat when the expected type is not known.

You can define default instances with higher priority to override the builtin ones.
-/
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational
/-

Priorities are also useful to control the interaction between different default instances. |

For example, suppose xs has type List α. When elaborating xs.map (fun x => 2 * x),
we want the homogeneous instance for multiplication to have higher priority than the default instance
for OfNat.

This is particularly important when we have implemented only the instance HMul α α α,
and did not implement HMul Nat α α.

Now, we reveal how the notation a*b is defined in Lean

-/

class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n



class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

--the heterogenous default instance

infixl:70 " * " => HMul.hMul
/-
The Mul class is convenient for types that only implement the homogeneous multiplication.
-/

end ex
