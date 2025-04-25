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
  We can then picture a function `f: Bool → codomain …` satisfying
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
  _polymorphic_.

  __Exercise__: Define a polymorphic function `x ↦ (x,x)`. Make it work on
  any `x`, of any type.

  __Exercise__: Define a polymorphic function that swaps the components of
  a pair (of any two types).

  __Exercise__: Recall that algebraic types form an abelian semiring, up to
  isomorphism. The isomorphisms that prove the semiring laws can all be
  defined as polymorphic functions. Select a few of them and make them
  general.
-/

/-
  We can add universe-polymorphism on top of type-polymorphism to obtain
  a "truly general" identity function.
-/
def identity₃.{u} (τ: Type u) (x: τ): τ
  := x

/-
  Indeed, this is -essentially- how identity is defined in the Lean standard
  library. A minor difference is that the library uses `Sort u` instead of
  `Type u` to be even more general.

  (Ignore the curly braces in the type of `id`, for now.)
-/
#print id

example := @id Nat 42       -- (Ignore the `@`, for now.)
example := @id Type Nat
example := @id (Type 1) (Type × Bool)

end Polymorphic_functions

section Implicit_arguments
/-
  Passing _all_ the arguments to dependently typed functions can be
  inconvenient. For instance, consider this example:
-/
example := identity₁ Bool true
/-
  Here, having to specify `Bool` looks redundant: if the second argument
  is `true`, then the first _has_ to be `Bool` to make the function call
  meaningful.

  We can ask Lean to infer that argument for us by using `_`.
-/
example := identity₁ _ true      -- `_` inferred as `Bool`.
/-
  __Exercise__: Hover your mouse pointer over the `_` to discover the
  inferred argument.

  __Exercise__: Convince yourself that we can not reasonably expect `_` to
  just work in all cases. Suppose
    `f: Nat → Type`
    `g: (n: Nat) → f n → String`.
  Here, `g _ true` requires to find `n` such that `f n` is `Bool`.
  This can be a very complex task!

  Still, in practice `_` does work on many cases, so feel free to use it
  when you feel it appropriate to hide distracting details.
  Note that, when `_` works, it might still be a good idea to avoid it and
  type the argument so that the resulting code does not omit vital
  information for human readers.

  Distinguishing between "distracting details" and "vital information" is
  a skill that can only be learnt with time and experience.
-/

/-
  When defining a function, if you expect that one of the arguments will
  almost invariable be `_` at each function call site, then you can declare
  the argument to be _implicit_, as follows.
-/
def swapPair₁ (α β: Type) (p: α×β): β×α
           -- ↑ regular arguments within parentheses
  := (p.2, p.1)

example := swapPair₁ Bool String (true, "hello")
example := swapPair₁ _    _      (true, "hello")

def swapPair₂ {α β: Type} (p: α×β): β×α
           -- ↑ implicit arguments within braces
 := (p.2, p.1)
example := swapPair₂ (true, "hello")
                 -- ↑ No implicit args!
example := @swapPair₂ Bool String (true, "hello")
        -- ↑ The `@` makes _all_ arguments explicit again
example := @swapPair₂ _    _      (true, "hello")
        -- ↑          ↑    ↑
        -- (This works, but only obfuscates the intent)
example := swapPair₂ (α:=Bool) (true, "hello")
                  -- ↑ Single implicit argument made explicit
                  -- `α` is the name of the argument in the `def` above
                  -- `β` is still implicit here
example := swapPair₂ (β:=String) (true, "hello")
example := swapPair₂ (α:=Bool) (β:=String) (true, "hello")

end Implicit_arguments

-- TODO dependent pattern match (in a simple case)?

-- TODO introduction elimination

end Dependent_products
