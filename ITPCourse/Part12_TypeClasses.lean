
import Mathlib.Data.List.Sort   -- For the `List` type
import Mathlib.Data.Real.Basic  -- For `Real` numbers

section Type_classes
/-
  Sometimes we want to add additional information on top of existing types.

  As an example, suppose we want to order a type:
-/
structure OrderOn (τ: Type) where
  -- The ≤ relation
  leq: τ → τ → Prop
  -- Preorder laws
  leq_refl: ∀ x, leq x x
  leq_trans: ∀ {x y z}, leq x y → leq y z → leq x z

def orderNat: OrderOn Nat where
  leq := Nat.le
  leq_refl := Nat.le_refl
  leq_trans := Nat.le_trans

/-
  We might then want to define ways to define an order on, say, types such
  as `τ × σ`, `τ ⊕ σ`, `τ → σ`, … given orders for `τ` and `σ`.
-/
def orderProduct {τ σ: Type} (oτ: OrderOn τ) (oσ: OrderOn σ)
  : OrderOn (τ × σ)
  where
  leq := λ (t₁,s₁) (t₂,s₂) => oτ.leq t₁ t₂ ∧ oσ.leq s₁ s₂
  leq_refl := sorry   -- (Proofs omitted since not relevant)
  leq_trans := sorry
/-
  … and so on for other types.

  Using this approach can be cumbersome, though, since we have to manually
  construct the order associated to a type every single time.
  Below, we check if a `List` (a type from the library) is ordered.
-/
def orderedList {τ: Type} (oτ: OrderOn τ): List τ → Prop
| []   => True
| [_]  => True
| (x₁ :: x₂ :: rest)
  => oτ.leq x₁ x₂ ∧ orderedList oτ (x₂ :: rest)

def a_list: List (Nat × Nat) := [(0,10), (4,17), (5,22)]

example
  : orderedList (orderProduct orderNat orderNat) a_list
             -- ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑ Inconvenient!
  := by
  simp [ a_list, orderedList , orderNat , orderProduct ]

/-
  Type classes provide an automated way to construct the additional
  information associated to a type, such as the order as done above.

  A `class` is similar to a `structure` with (at least) one parameter.
-/
class Order (τ: Type) where
  -- The ≤ relation
  leq: τ → τ → Prop
  -- Preorder laws
  leq_refl: ∀ x, leq x x
  leq_trans: ∀ {x y z}, leq x y → leq y z → leq x z

/-
  Class instances provide a way to connect any type `τ` to their order.
-/
instance instOrderNat: Order Nat where
  leq := Nat.le
  leq_refl := Nat.le_refl
  leq_trans := Nat.le_trans

/-
  An argument in brackets `[o: Order …]` makes Lean automatically search
  for other instances. This is called a _class constraint_.
-/
instance instOrderProduct {τ σ: Type} [oτ: Order τ] [oσ: Order σ]
  : Order (τ × σ)
  where
  leq := λ (t₁,s₁) (t₂,s₂) => oτ.leq t₁ t₂ ∧ oσ.leq s₁ s₂
  leq_refl := sorry
  leq_trans := sorry

def orderedList₂ {τ: Type} [oτ: Order τ]: List τ → Prop
| []   => True
| [_]  => True
| (x₁ :: x₂ :: rest)
  => oτ.leq x₁ x₂ ∧ orderedList₂ (x₂ :: rest)
                            --  ↑  No additional argument here!

def ord_example
  : orderedList₂ a_list
             -- ↑  No additional argument here!
  := by
  simp [ a_list, orderedList₂ , Order.leq ]
/-
  Note how Lean automatically inferred the instance, providing the right
  order relation to the called function. Effectively, Lean operates in
  the following way:
  - `a_list` is a `List (Nat × Nat)`, so `τ` is inferred to be `Nat × Nat`
  - `orderList'` requires `Order (Nat × Nat)`, we search for instances
  - `instOrderProduct` can provide that, but requires `Order Nat` (twice)
  - `instOrderNat` provides `Order Nat`
  Lean then automatically solves the constraint at hand while generating the
  missing arguments for us.

  We can show the inferred instances as follows:
-/
section
set_option pp.all true
#check orderedList₂ a_list
end

/-
  Also note that sometimes we can also completely avoid naming instances.
-/
def orderedList₃ {τ: Type} [Order τ]: List τ → Prop
                        -- ↑ No given name
| []   => True
| [_]  => True
| (x₁ :: x₂ :: rest)
  => Order.leq x₁ x₂ ∧ orderedList₃ (x₂ :: rest)
  -- ↑ No reference to any particular instance, we exploit inference.

/-
  Type classes are heavily exploited in the Lean standard libraries to keep
  the notational noise down. Instead of using
    `Nat.le x y`
    `Int.le x y`
    `Rat.le x y`
    `Real.le x y`
    …
  we can simply write the much more readable
    `x ≤ y`
  and Lean will pick up the "right" relation for the types at hand.
-/
#print LE
#check instLENat
/-
  The same happens for addition, multiplication, and many other common
  mathematical operators.

  Even number literals like `42` implicitly use type classes so that they
  can be used as `Nat`, `Int`, … or whatever type is needed. This is also
  why, when the context does not demand a precise type, we explicitly have
  to use something like `(42: Nat)` to prod Lean into selecting the right
  instance.
-/
#print OfNat

section
set_option pp.all true
#check (42: Nat)
#check (42: Int)
#check (42: Rat)
#check (42: Real)   -- This also involves another type class.
end

/-
  Finally note that is is possible that a class constraint like `[Order τ]`
  can be solved in multiple different ways, if there are multiple instances
  that can do that.
-/
instance instOrderString₁: Order String where
  leq := λ x y => x ≤ y   -- standard alphabetic/lexicographic order
  leq_refl := sorry
  leq_trans := sorry
instance instOrderString₂: Order String where
  leq := λ x y => y ≤ x   -- opposite order
  leq_refl := sorry
  leq_trans := sorry
/-
  The automatic constraint solver will pick one of these when dealing with
  `[Order String]`. There are ways to change the priority between
  conflicting instances, but we will not see them. Refer to the Lean
  documentation if you really need this. When possible, avoiding conflicting
  instances is the best solution.
-/
end Type_classes

section Decidable_properties
/-
  A fairly common class of propositions is the `Decidable` class, that
  comprises those propositions that can be checked through computation,
  i.e. with an algorithm.
-/
example (x y z: Nat): Decidable (x+y ≤ z)
  := inferInstance  -- Let Lean find the needed instances

/-
  Decidable properties include (among others)
  - common arithmetic operators on `Nat`, `Int`, `Rat`
  - common logical operators `=`, `≠`, `≤`, … on `Nat`, `Int`, `Rat`
  - combinations of decidable properties using `∧`, `∨`, `→`, `↔`, `¬`

  The `Decidable` class does NOT include (among others)
  - properties involving `∀` or `∃`
  - properties on most functions
  - properties on `Real` numbers
  Intuitively, this is because to check `∀ n: Nat, P n` sometimes we do
  not really have an algorithm. Note that we can not actually check
    `P 0`, `P 1`, `P 2`, …
  because when no counterexample exists that would take infinite time, so we
  would not be able to that `∀ n: Nat, P n` is true.

  [ Note: the general absence of an algorithm can actually be proved with
    tools from _computability theory_ (also known as _recursion theory_). ]

  Further, we can not decide `f = g` when `f g: Nat → Bool`. Testing those
  functions on their whole infinite domain is unfeasible.

  `Real` numbers can be represented in many ways, but all of them involve
  function-like objects, such as
  - converging rational sequences (`Nat → Rat`)
  - sequences of (say) base-2 digits (`Nat → Bool`)
  - suitable sets of rationals (`Rat → Prop`)
  Therefore, we can not have an algorithm to decide `x = 0` when `x: Real`.
-/

/-
  Decidable properties can be used inside an `if …` in definitions, even if
  their type is `Prop` (and not `Bool`).
-/
def half_parabola₁ (x: Int): Int
  :=
  if x ≤ 0
  then 0
  else x^2

/-
  Lean prods ourselves to use `Decidable` properties as much as possible
  since it helps automating simplification steps in proofs.

  Sometimes, though, this `Decidable` restriction in `if … ` is simply too
  strong. Working with real numbers, for instance, requires us to use many
  undecidable properties.

  In such cases, Lean allows us to exploit axioms and pretend that all
  propositions are "decidable":
-/
#check Classical.propDecidable
/-
  Here is a simple example. Note how Lean still forces us to mark the
  definition as `noncomputable`, since it is not backed by an algorithm.
-/
noncomputable
def half_parabola₂ (x: Real): Real
  :=
  if x ≤ 0
  then 0
  else x^2

#print axioms Classical.propDecidable
#print axioms half_parabola₂

/-
  More complex conditions might require to exploit `propDecidable` more
  explicitly.
-/
noncomputable
def best_function₁ (f g: Real → Real) (x: Real): Real
  :=
  let _ := Classical.propDecidable  -- Put the result in scope
  if (∀ y, f y ≤ g y)
  then f x
  else g x

/-
  In tactics mode, `classical` does just that:
-/
noncomputable
def best_function₂ (f g: Real → Real) (x: Real): Real
  := by
  classical
  exact if (∀ y, f y ≤ g y)
        then f x
        else g x

example (f g: Real → Real)
  : True
  := by
  classical
  let best (x: Real): Real :=
    if ∀ y, f y ≤ g y
    then f x
    else g x
  trivial

end Decidable_properties

section Common_library_type_classes
/-
  We saw the `LE` class providing the `≤` relation. Note, however, that `LE`
  on its own does not guarantee any property on `≤`.
  If we want to assume some properties on `≤`, we can use other classes.
-/
#print LE
#print Preorder           -- reflexive and transitive
#print PartialOrder       -- antisymmetric
#print LinearOrder        -- `a≤b ∨ b≤a`
#print SemilatticeSup     -- `sup a b`
#print SemilatticeInf     -- `inf a b`
#print Lattice            -- both `sup` and `inf`
#print CompleteLattice    -- Suprema/infima for any set
-- (We will see the `Set α` type soon)

/-
  A similar trend is found in other classes. The `+` operation is provided
  by classes `HAdd` and `Add`, but without any laws.
  Other classes provide more laws.

  The same idea is applied to other common operations.
-/
#print HAdd  -- lawless `a+b` (where `a` and `b` may be of different types)
#print Add   -- lawless `a+b` (`a` and `b` of the same type)
#print Zero  -- lawless `0`
#print Neg   -- lawless `-a`
#print Sub   -- lawless `a-b`
#print AddSemigroup   -- associative
#print AddZeroClass   -- `0` is the identity
#print AddMonoid
#print SubNegMonoid   -- negation and subtraction laws
#print AddGroup
#print AddCommGroup
#print Semiring
#print Ring
#print CommRing
#print Field

/-
  __Exercise__: Inspect the jungle of classes that contribute to the
  definition of `Field`. You can also use Loogle to browse them with more
  ease.
-/
end Common_library_type_classes

section Recap_exercises
/-
  __Exercise__: Consider the following type representing a 2×2 matrix.
  Make it into an additive monoid, as defined by the `AddMonoid` class, by
  completing the related instances below.
-/
structure Mat (K: Type) [Field K] where
  a₁₁: K
  a₁₂: K
  a₂₁: K
  a₂₂: K

instance instMatZero (K) [Field K]
  : Zero (Mat K) where
  zero := {a₁₁ := 0, a₁₂ := 0, a₂₁ := 0, a₂₂ := 0}

instance instMatAdd (K) [Field K]
  : Add (Mat K) where
  -- Add two matrices
  add := sorry

instance instMatAddMonoid (K) [Field K]
  : AddMonoid (Mat K) where
  -- Prove the monoid laws
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  -- The class also requires to define "multiplication by a natural number".
  -- You can ignore this, and leave the following line as it is.
  nsmul := nsmulRec

/-
  __Exercise__: Extend the above exercise to make `Mat K` into a `Ring`.
-/

/-
  __Exercise__: The following `Opposite T` type represents the values of
  type `T`, but ordered in the opposite order. Complete the instances
  below.
-/

@[ext]
structure Opposite (T: Type) where
  t: T

instance instOppositeLE (T: Type) [LE T]
  : LE (Opposite T) where
  le := sorry

instance instOppositePartialOrder (T: Type) [PartialOrder T]
  : PartialOrder (Opposite T) where
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

/-
  __Exercise__: Extend the exercise above testing your `Opposite` instances
  with the following data. Complete the proofs. This might amount to a
  single `simp` or `decide`.
-/

-- A sorted list of naturals
def testList: List ℕ := [1,5,8,42,100]

-- We reverse the list and switch to `Opposite`.
-- Notice the `reverse` and `map` standard list functions.
def testListOp: List (Opposite ℕ)
  := testList.reverse.map (λ x => {t := x})

-- `testList` is sorted (using the standard ordering)
example: testList.Sorted LE.le
  := by sorry

-- `testListOp` is also sorted (using our ordering)
example: testListOp.Sorted LE.le
  := by sorry

end Recap_exercises
