/-
  We finally introduce _dependent types_, one of the most important features
  of the Lean type system. We start from dependent products.
-/

section Dependent_products

section First_examples
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

end First_examples

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

section Telescopes
/-
  Note that in the most extreme case, a function with multiple arguments
  could have a type of the following form:
    `(x₁: τ₁) → (x₂: τ₂ x₁) → (x₃: τ₃ x₁ x₂) → ⋯ → σ x₁ … xₙ`
  There, the type of each `xᵢ` depends on _all_ the previous arguments.

  Fortunately, it is rare to see such extreme level of dependency in types.

  This is sometimes referred to as a telescope, since every piece connects
  inside the next one in the sequence.

  Finally, note that when defining a function we can normally reorder its
  arguments as we please, but in the presence of dependent types, the non
  dependent arguments must come earlier than the arguments whose type
  depend on them. In an extreme case like the telescope above, no reordering
  is possible at all.
-/
end Telescopes

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

section Foundations_of_dependent_products
/-
  Let's review the rules for dependent product types:

  - __Type Formation__: if
      `α: Type u`
      `β: α → Type v`
    then `(a: α) → β a` is a type in the universe `Type (max u v)`.

  - __Introduction__: to construct a function of type `(a: α) → β a`, we can
    use the usual function syntax `λ a: α => t` (and its variants). For this
    to be well-typed, we need the term `t` to have type `β a` where `a` is
    indeed the variable denoting the function argument.

  - __Elimination__: we can apply functions as usual, but now the involved
    types are slightly more complex. If we have two terms
      `f: (a: α) → β a`
      `e: α`
    then the application `f e` has type `β e`.
    We stress that `e` can be an arbitrary term -- it does not have to be a
    variable. This means that we now have types like `β e` which can mention
    arbitrary terms inside their syntax. We no longer have a rigid "barrier"
    between _terms_ and _types_: the syntax of types can include terms, and
    vice versa.

  - __Computation / β__: as for regular functions.

  - __Uniqueness / η__: as for regular functions.
-/

/-
  Note in passing that dependent products indeed generalize the notion of
  function type `α → β`. In fact, function types are implemented in Lean as
  dependent products with a constant codomain.
-/
example: (Nat → String) = ((_n:Nat) → String)
  := rfl

#check ((_n:Nat) → String)  -- This is printed as a function type!
/-
  This is easy to remember as the informal equation
    `Π (a: A), B ≅ Bᴬ`
  when `B` does not depend on the index `a`.
-/
end Foundations_of_dependent_products

section A_glimpse_at_dependent_pattern_matching
/-
  Pattern matching in the presence of dependent types becomes much more
  subtle and interesting.

  We will study it later, but for now let's discuss an "appetizer" example:
-/
def extractString₁
  (b: Bool)
  (x: if b then String × Nat else Bool × String)
  : String
  := match b , x with
  | true  , y => y.1
  | false , z => z.2

/-
  First, this is a dependently-typed function: its first argument `b` occurs
  in the type of the second argument `x`, which is given by an intricate
  term `if b then …`. The result type is instead fixed to `String`.

  Second, the `match` involves _two_ terms instead of just one. Terms `b`
  and `x` are matched simultaneously. On its own matching two (or more)
  values instead of just one might look like a simple generalization.

  However, types play a subtle role here. Consider the first case of the
  `match`. There, we have `b = true` and `x = y`. If we put our cursor right
  before `y.1`, we can observe that at that point `x` and `y` have
  _different_ types, in spite of them being equal!
  Lean reports these types:
    `x : if b    = true then String × Nat else Bool × String`
    `y : if true = true then String × Nat else Bool × String`
  Since we matched `b = true`, the type of `y` reflects that knowledge.
  This makes Lean see that `y: String × Nat`, which is needed to accept the
  term `y.1` as a `String`.

  A similar subtle reasoning is needed for `z.2` in the second case.

  __Exercise__: Try using `x.1` instead of `y.1` and observe what happens.
-/

/-
  Lean sometimes performs some more "magic" to make `match` work even when
  if we strictly follow the rules it should not.
  For instance, the following code is silently rewritten as our code
  above.
-/
def extractString₂
  (b: Bool)
  (x: if b then String × Nat else Bool × String)
  : String
  := match b with
  | true  => x.1
  | false => x.2

#print extractString₂
/-
  A technical note: in the printed code, we can read
    ```
    fun b x ↦
    match b, x with
    | true, x => x.fst
    | false, x => x.snd
    ```
  Note that the two variables named `x` in the patterns are distinct
  variables from the one bound by the `fun b x ↦ …`, even if they share the
  same name. This is similar to what happens in
    `(λ x => … (λ x => x+x) … )`
  Inside `x+x`, the identifier `x` names the argument variable for the
  innermost `λ`, while the argument of the outermost variable is shadowed.
  It is equivalent to:
    `(λ x => … (λ y => y+y) … )`
-/
end A_glimpse_at_dependent_pattern_matching

end Dependent_products
