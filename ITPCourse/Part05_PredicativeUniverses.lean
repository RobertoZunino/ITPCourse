/-
  Before moving forward with Lean, we now take a quick look at its
  foundations.
-/

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

end One_more_universe
