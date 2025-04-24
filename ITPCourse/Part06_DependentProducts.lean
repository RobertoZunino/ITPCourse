/-
  We finally introduce _dependent types_, one of the most important features
  of the Lean type system. We start from dependent products.
-/

section Dependent_products
/-
  Who said that the codomain of a function must be _fixed_?

  Suppose we have a type-valued function like this one:
-/

def codomain (b: Bool): Type
  := if b then String else Nat

/-
  We can then think of a function `f: Bool → codomain …` satisfying
    `f true  := "hello" : codomain true`
    `f false := 42      : codomain false`
  Note how the codomain type is actually a function of the boolean
  _argument_, so it is not fixed. It _depends_ on the argument value.

  This kind of function can be defined in Lean as follows:
-/

def f₁: (b: Bool) → codomain b
  := λ b => match b with
  | true  => "hello"
  | false => (42: Nat)

/-
  The type `(b: Bool) → codomain b` is called a _dependent product_ type.
  Effectively, this function can be thought as a sort of indexed product of
  types
    `Π (b: Bool), codomain b`   -- (pseudo code, not actual Lean)
  which in case is the straightforward product
    `codomain true × codomain false`

  Indeed, any function `f` can be thought as a tuple
    `⟨ f …, f …, f …,  … ⟩`
  where the components of the tuple are indexed by the function domain.

  The dependent product type can be written in this alternative form:
-/

def f₂: ∀ (b: Bool), codomain b   -- Still the same type.
  := f₁

/-
  Also, dependent types can be implicitly involved when defining a function
  while naming its arguments.
-/

def f₃ (b: Bool): codomain b
  := f₂ b

#check f₃    -- `(b: Bool) → codomain b`

section Polymorphic_functions
/-
  Here is another example of dependent products.

  Defining the identity function on each type can be tiresome:
-/

def identityNat: Nat → Nat := λ x => x
def identityBool: Bool → Bool := λ x => x
def identityString: String → String := λ x => x

/-
  Instead, we can exploit dependent products!
-/

def identity₁: (τ: Type) → τ → τ
  := λ _τ x => x
-- or, more pragmatically
def identity₂ (τ: Type) (x: τ): τ
  := x

#check identity₁
#check identity₂

example: Nat    := identity₁ Nat 42
example: String := identity₁ String "hello"

/-
  Functions that can operate on multiple types like `identity₁` are called
  _polymoprhic_.

  __Exercise__: Define a polymorphic function `x ↦ (x,x)`. Make it work on
  any `x`, of any type.

  __Exercise__: Define a polymorphic function that swaps the components of
  a pair (of any two types).

  __Exercise__: Recall that algebraic types form an abelian semiring, up to
  isomorphism. The isomorphisms that prove the semiring laws can all be
  defined as polymorphic functions. Select a few of them and make them
  general.
-/
end Polymorphic_functions

-- TODO implicit arguments (`_` and `{x} → …`)

-- TODO dependent pattern match (in a simple case)?

-- TODO introduction elimination

end Dependent_products
