/-
Output Parameters:

By default, Lean only tries to synthesize an instance Inhabited T when the term T is
known and does not contain missing parts.

The following command produces the error "typeclass instance problem is stuck,
it is often due to metavariables ?m.7" because the type has a missing part (i.e., the _).
-/
#check_failure (inferInstance : Inhabited (Nat × _))

/-
You can view the parameter of the type class Inhabited as an input value for the type class
synthesizer.

When a type class has multiple parameters, you can mark some of them as output parameters.

Lean will start type class synthesizer even when these parameters have missing parts.

In the following example, we use output parameters to define a heterogeneous polymorphic
multiplication.
-/

namespace ex

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]


/-
The parameters α and β are considered input parameters and γ an output one.

Given an application hMul a b, after the types of a and b are known, the type class
synthesizer is invoked, and the resulting type is obtained from the output parameter γ.

In the example above, we defined two instances.

The first one is the homogeneous multiplication for natural numbers.

The second is the scalar multiplication for arrays.

Note that you chain instances and generalize the second instance.
-/


instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b) --bs is the array, a is the scalar

#eval hMul 4 3                    -- 12
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]
#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]

--chained, last example


end ex
/-
You can use our new scalar array multiplication instance on arrays of type Array β with
a scalar of type α whenever you have an instance HMul α β γ.

In the last #eval, note that the instance was used twice on an array of arrays.
-/
