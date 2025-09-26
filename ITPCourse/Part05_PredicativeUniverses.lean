/-
  Before moving forward with Lean, we now take a quick look at its
  foundations.
-/

namespace PredicativeUniverses

section Types_as_terms
/-
  So far, we used Lean _types_ to describe the "nature" of the values which
  are denoted by Lean _terms_.

  For example `"hello"` is a `String`, and `true` is a `Bool`.

  To make languages like Lean truly usable in practice, it is convenient to
  allow terms to denote _types_ as well.
-/

def Point: Type := Nat × Nat

def Pair: Type → Type
  := λ α => α × α

example: Point = Pair Nat
  := rfl

/-
  There is a lot to digest here:

  - The term `Nat × Nat` is indeed a term, very much like `2 + 2`.

  - The term `2 + 2` denotes a value of type `Nat`. Similarly, the term
    `Nat × Nat` denotes a "value" of type `Type`.

  - `Type` is therefore the "type of types". (More on this below.)

  - `def Point: Type := …` defines the identifier `Point` as a type that is
    equal to `Nat × Nat`.

  - `def Pair: Type → Type := …` defines a function from types to types.
-/

/-
  __Exercise__: Define a `tuple` function that returns the type of 2-tuples
  or 3-tuples of `Nat`, depending on its boolean argument.
  Test the function with one or two `example:`s.
-/
def tuple (threeD: Bool): Type
  := sorry

/-
  __Exercise__: Verify using `#check` the type of `Nat`, `Unit`, `String`,
  and a few other product/sum/function types of your choice.
-/

end Types_as_terms

section Predicative_universes
/-
  We know that
    `"hello"` has type `String`
    `String`  has type `Type`
  or, in a more succinct notation,
    `"hello" : String : Type`
  One might then wonder: if values (`"hello"`) have a type (`String`), and
  if types (`String`) have also a type (`Type`), … does `Type` have a type
  too?

  __Exercise__: Find out with the `#check` below.
-/

#check Type

/-
  So, the type of `Type` is not `Type` itself, but a new `Type 1` type.

  This instantly raises a new question: what about `Type 1` then?

  __Exercise__: Find out we indeed have an infinite hierarchy
    `"hello" : String : Type : Type 1 : Type 2 : Type 3 : ⋯`
-/

#check "hello"
#check String
#check Type
#check Type 1
#check Type 2

/-
  `Type`, without any argument, is actually an alias for `Type 0`.
-/

section Girard's_paradox
/-
  One might wonder why we need all this complexity. It would be tempting to
  just declare that `Type` is a type, and so it is of type `Type`, and
  obtain a simpler system:
    `"hello" : String : Type : Type : Type : ⋯`

  Alas, this breaks the foundations of the type system, allowing one to
  define a term of type `Empty`, exploiting the so called Girard's paradox.
  If we want to use Lean to do mathematics, we can not allow that since it
  would make our logical system inconsistent, i.e. being able to prove any
  statement and its negation as well.

  We will not discuss Girard's paradox further in this course, but feel free
  to look it up it you are curious. (For a simpler version, you can also
  look up "hypergame paradox".)
-/
end Girard's_paradox

/-
  These "types of types" of the form `Type u` types are called _universes_.

  The `Type u` universes are called _predicative_ because of the actual type
  formation rule for functions. Previously we have seen that
    if   `α` is a type
    and  `β` is a type,
    then `α → β` is a type.
  We can now refine that rule to use universes:
    if  `α : Type u₁`
    and `β : Type u₂`
    then `α → β : Type (max u₁ u₂)`

  For example:
-/

#check Nat → Nat      -- `Type` (aka `Type 0`)
#check Nat → Type     -- `Type 1`
#check Type → Nat     -- `Type 1`
#check Type → Type    -- `Type 1`
#check Type → Type 1  -- `Type 2`

/-
  The product and sum type formation rules are similar.
-/

#check Nat × String  -- `Type`
#check Nat × Type    -- `Type 1`
#check Nat × Type 1  -- `Type 2`
#check Nat ⊕ Type    -- `Type 1`
#check Nat ⊕ Type 1  -- `Type 2`

example: Nat × Type
  := (42, String)

example: Nat × Type 1
  := (42, Type)

example: Nat × Type 1
  := (42, Type → Type)

example: Nat ⊕ Type
  := .inl 12

example: Nat ⊕ Type
  := .inr String

end Predicative_universes

section Discussion
/-
  You might wonder if this level of generality is actually needed in
  practice. The answer to this question might vary, depending on what kind
  of mathematics we want to work with.

  In many cases `Type` (i.e., `Type 0`) is already large enough to formalize
  the mathematical objects we want to study. There we find all the standard
  numeric types (naturals, integers, reals, …), and --as we shall see-- we
  can model sets, relations, functions, … on such types.

  However, sometimes we want to go a little further. If we want to define
  the application that maps any vector space to its dual, or any group `G`
  to the direct product `G × G`, then we are essentially defining a
  `Type → Type` map, and for that we need `Type 1`.

  Needing much higher universes is arguably rather uncommon, but not
  completely ruled out. Category theory, for instance, tends to involve
  notions which can require moving up in the hierarchy.

  As a general recommendation, do not worry too much about the existence of
  higher universes. Just know that, when (and if) the need arises, they are
  there.

  A final remark: note that the Lean standard library tends to be as
  general as possible, and that often involves advanced features of Lean
  that can be puzzling to a newcomer. The pragmatic reason we are studying
  universes in some detail is _not_ that we will use them often, but that
  the library does so. Understanding the Lean foundations to a certain
  extent is then crucial to be able to use the library.
-/
end Discussion

section One_more_universe
/-
  As a remark, note that Lean has just one more universe beyond the `Type u`
  ones we have seen above. It is the universe of logical _propositions_, and
  is named `Prop`.

  `Prop` is special: crucially, it is _not_ predicative like `Type u`, but
  uses a very different type formation rule.
  We will study it later. For now, just note that `Prop : Type 0`, so `Prop`
  is a type just like `Bool`, `String`, and `Nat`.

  Finally, note that the Lean universe names in the hierarchy
    `Prop   : Type 0 : Type 1 : Type 2 : ⋯`
  are actually _aliases_ (!) for the actual names
    `Sort 0 : Sort 1 : Sort 2 : Sort 3 : ⋯`
  That is, `Sort 0` is `Prop`, and `Sort (u+1)` is `Type u`.

  For now, just remember that sometimes in the Lean library we will find
  some functions operating on `Sort …`: these can also work on `Type …` if
  we shift the universe index by one.
-/

/-
  So far we have only seen simple equalities as propositions.
-/
example: Prop
  := 2 + 2 = 4

/-
  Functions from a type like `Nat` to `Prop` can be understood as
  "properties on `Nat`", or even as subsets of `Nat`.
-/
def equalToFive: Nat → Prop
  := λ n => n = 5   -- Given `n`, return the proposition `n = 5`.

/-
  Indeed, we can define the "powerset" operator, or the "type of subsets" as
  follows:
-/
def 𝒫 (τ: Type): Type
  := τ → Prop

/-
  Here is a function that can construct singletons.

  Note the function application `𝒫 Nat` that applies `𝒫` to `Nat`, resulting
  in `Nat → Prop`.
-/
def singletonNat (n: Nat): 𝒫 Nat
  := λ m => m = n

/-
  Relations can also be modelled as functions `α → β → Prop`.
-/
def halfOf: Nat → Nat → Prop
  := λ n m => n+n = m

end One_more_universe

section Structures_in_a_given_universe
/-
  When defining a `structure`, we can explicitly state the universe where
  the new structure type will be created.
-/
structure Struct₁: Type 2 where
  a: String
  b: Type
  c: Type 1

/-
  The chosen universe must be "large enough" to account for all th field
  types: when defining
    ```
    structure … : Type u where
      a₁: α₁
      ⋮
      aₙ: αₙ
    ```
  then each `αᵢ` must have type `Type uᵢ` with `uᵢ ≤ u`.

  __Exercise__: In the definition of `Struct₁`, try changing `Type 2` to
  `Type 1`.

  We can choose a larger universe level, if we want.
-/
structure Struct₂: Type 8 where
                     -- ↑ --
  a: String
  b: Type
  c: Type 1

end Structures_in_a_given_universe

section Structures_with_parameters
/-
  Structure types can be parametrized:
-/
structure FunctionChain (α₁: Type) (α₂: Type) (α₃: Type) (α₄: Type) where
  f₁: α₁ → α₂
  f₂: α₂ → α₃
  f₃: α₃ → α₄

/-
  Note that this effectively makes `FunctionChain` a type-valued function.
-/
#check FunctionChain  -- Type → Type → Type → Type → Type

/-
  Another example: a type isomorphism without the associated laws.
-/
structure PreIsomorphism (α β: Type) where
  forward: α → β
  back: β → α

/-
  __Exercise__: Define a `structure` carrying the group operations on a
  given type `τ`. Ignore the group laws for the moment.
  Then answer:
    - would it be any different if defined `MonoidOps`?
    - `SemigroupOps`?
    - `MagmaOps`?
-/
structure GroupOps (τ: Type) where
  -- Add your fields here

/-
  __Exercise__: Define a `structure` carrying the ring operations.
  Ignore the ring laws.
-/
structure Ring (τ: Type) where
  -- Add your fields here
end Structures_with_parameters

section Universe_polymorphism
/-
  In the definition above, we always had to mention a _fixed_ universe
  to work within. This can be inconvenient and lead to repeated code:
-/
def Endomorphism₀ (τ: Type 0): Type 0 := τ → τ
def Endomorphism₁ (τ: Type 1): Type 1 := τ → τ
def Endomorphism₂ (τ: Type 2): Type 2 := τ → τ

/-
  We can generalize this to an arbitrary universe:
-/
def Endomorphism.{u} (τ: Type u): Type u := τ → τ

/-
  Then `u` is aumatically inferred on use:
-/
#reduce (types:=true) Endomorphism String  -- `u = 0`
#reduce (types:=true) Endomorphism Type    -- `u = 1`
/-
  Note: without `(types:=true)`, `#reduce` does not simplify types.
-/

/-
  __Exercise__: `structure`s can be universe-polymophic too!
  Try guessing the syntax to generalize `PreIsomorphism` to arbitrary
  universes.
-/

/-
  __Exercise__: The syntax `α × β` actually stands for `Prod α β` where
  `Prod` is a structure defined in the Lean standard library. Check out its
  definition.
-/
#print Prod

end Universe_polymorphism

section Recap_exercises
/-
  __Exercise__: Define a `structure` to represent the field operations.
  Then use that to define another `structure` to define the operations for a
  vector space over a given field.
  Ignore the laws for fields and vector spaces.

  __Exercise__: Try making the definitions in the previous exercise
  universe-polymorphic.
-/

/-
  __Exercise__: Define a `structure` for an ordering over a type.
  Ignore the ordering laws, but focus on the operations. There are several
  possible notions of "order".
  Recall that a relation can be modelled as a function `α → β → Prop`.

  __Exercise__: Define a function that takes an ordering and "reverses" it.

  __Exercise__: Try making the definitions in the previous exercise
  universe-polymorphic.
-/
end Recap_exercises

end PredicativeUniverses
