
section Inductive_types
/-
  An inductive type is a type whose values are only those that can be
  formed though a given set of operations, named _constructors_.

  Inductive types, as their name suggests, also allow for defining a type
  through _induction_. Still, to help understanding, we start our
  presentation from a few basic examples which do not exploit induction at
  all.
-/

section Not_really_inductive_inductive_types

section Enumerated_types

inductive Color
| red: Color
| green: Color
| blue: Color
/-
  Here, `Color.red` is a constant of type `Color`, and is one of the
  introduction forms for that type. In many contexts, it can be shortened
  as `.red`.

  The other constructors `.green` and `.blue` provide other introduction
  forms. Each form is _distinct_ from the others.

  Elimination is done through pattern matching/case analysis.

  Effectively, the `Color` type is isomorphic to a sum type.
    `Color ≅ Unit ⊕ Unit ⊕ Unit`
-/
def Color.permute₁ (c: Color): Color
  := match c with
  | .red   => .green
  | .green => .blue
  | .blue  => .red

-- Equivalent to the above
def Color.permute₂: Color → Color
  | .red   => .green
  | .green => .blue
  | .blue  => .red

end Enumerated_types

section Algebraic_types
/-
  In `inductive` types, constructors are allowed to be functions:
-/
def Point: Type := Nat × Nat -- `Nat` coordinates

inductive Shape
  -- A segment given by its endpoints
| segment: Point → Point → Shape
  -- A triangle given by its vertices
| triangle: Point → Point → Point → Shape
  -- A circle given by its center and radius
| circle: Point → Nat → Shape
/-
  Each constructor type must end with `… → Shape`.

  Each constructor has a disjoint image from any other constructor. Further,
  it acts injectively on its arguments, as if it were building a tuple.

  Effectively, the `Shape` type above is isomorphic to:
    `Shape ≅ (Point × Point) ⊕ (Point × Point × Point) ⊕ (Point × Nat)`

  Introduction and elimination work as shown below.
-/
example: Shape
  := .circle (3,4) 42

def Shape.translate_x (δx: Nat): Shape → Shape
  | .segment (x₁, y₁) (x₂, y₂)
    => .segment (x₁ + δx, y₁) (x₂ + δx, y₂)
  | .triangle (x₁, y₁) (x₂, y₂) (x₃, y₃)
    => .triangle (x₁ + δx, y₁) (x₂ + δx, y₂) (x₃ + δx, y₃)
  | .circle (x, y) r
    => .circle (x + δx, y) r

/-
  Effectively, any _algebraic_ type formed through the operations
    `Empty, ⊕, Unit, ×`
  can be represented, up to type isomorphism, as an `inductive` type.
  Indeed, as we previously mentioned, by exploiting the abelian semiring
  laws, any such type can be written in polynomial form (a sum-of-products)
    `… × (… × … × …) ⊕ (… × …) ⊕ ⋯`
  This can then be turned into an `inductive` type: we can declare a
  constructor `c` for each product in the sum, and make `c` take as many
  arguments as the factors in the product it corresponds to.

  __Exercise__: Try turning
    `Nat ⊕ (String × Bool) ⊕ Unit`
  into an `inductive` type.
-/
end Algebraic_types

end Not_really_inductive_inductive_types

section Actually_inductive_inductive_types
/-
  Constructors are allowed to use in their arguments the type we are
  defining right now.

  That is, the type of a constructor `c: … → … → … → T` can mention `T` in
  the `…` parts. This makes the type actually _inductive_.

  [ Actually, there are a few restrictions on how `T` can be used there, but
    we will not discuss them. ]

  The most famous example inductive type is, of course, `ℕ`:
-/
inductive ℕ
| zero: ℕ
| succ: ℕ → ℕ

/-
  Introduction is done in the obvious way:
-/
example: ℕ := .zero
example: ℕ := .succ .zero
example: ℕ := .succ (.succ .zero)
example: ℕ := .succ (.succ (.succ .zero))

-- Alternative syntax
example: ℕ := ℕ.zero
example: ℕ := ℕ.zero.succ
example: ℕ := ℕ.zero.succ.succ
example: ℕ := ℕ.zero.succ.succ.succ

/-
  Elimination is done with pattern matching, as usual, but the functions
  we define can now be _recursive_.
-/
def ℕ.double₁: ℕ → ℕ
| .zero   => .zero
| .succ n => .succ (.succ (ℕ.double₁ n))

-- Alternative syntax
def ℕ.double₂: ℕ → ℕ
| .zero   => .zero
| .succ n => n.double₂.succ.succ
/-
  Recursive functions definitions must make their recursive calls with
  "structurally smaller" arguments, to ensure the recursion eventually
  terminates.

  For instance, these are disallowed:
    `def f (n: ℕ): ℕ  := f n`
    `def f (n: ℕ): ℕ  := f (n.succ)`
-/

/-
  Note that the standard `Nat` type was defined just like our `ℕ` above:
-/
#print Nat

section The_recursor

/-
  Each time an inductive type `τ` is defined, Lean implicitly creates a
  special function `τ.rec` called _recursor_. The recursor has many purposes:

    - `τ.rec` acts as a general elimination rule for `τ`.

    - `τ.rec` is implicitly used to implement recursive functions (such as
      `ℕ.double` above).

    - `τ.rec` provides an _induction principle_ that can be exploited to
      prove theorems.

  Let us read the type for `ℕ.rec`, which is quite complex:
-/
#print ℕ.rec
/-
  This is a universe-polymorphic function. Let us discuss the case where
  `Sort u = Prop`. The recursor type then states:

    - Given any `motive: ℕ → Prop` (a property on `ℕ`)
    - Given the base case `motive ℕ.zero`
    - Given the induction case `∀ (a: ℕ), motive a → motive a.succ`
    - Then, we have `∀ (t: ℕ), motive t`

  So, this is the standard induction principle on natural numbers. The
  property is called a `motive`, the `∀`s are dependent product types,
  but everything else is very familiar.

  Note that the case `Sort u = Type` (or `= Type v`) is relatively similar:

    - Given any `motive: ℕ → Type` (a type family indexed by naturals)
    - Given a value in the first type in the family `motive ℕ.zero`
    - Given a way to construct values in the next type from the previous one
      `(a: ℕ) → motive a → motive a.succ`
    - Then, we have a value on all types in the family, i.e., we have a
      dependent function `(t: ℕ) → motive t`

  It might be helpful to consider the simpler case where `motive t` is a
  constant `α`, so the resulting function is simply of type `ℕ → α`. The
  recursor then simply takes `x: α`, `f: α → α` and `n: ℕ`, and repeatedly
  applies `n` times the function `f` to `x` so to obtain `⋯ f (f (f x))` of
  type `α`.
-/

section A_theoretical_remark
/-
  Note that, even in the case of actually inductive types like `ℕ` we still
  have an isomorphism like those we observed for algebraic types. Applying
  the same technique we get:
    `ℕ ≅ Unit ⊕ ℕ`

  Indeed, one can argue that `ℕ` is the "smallest" solution to this
  "recursive type equation". (In category theory, this is referred to as an
  "initial F-algebra".)

  In a sense, the recursor makes `ℕ` to be the "smallest", the "least" type
  which admits introductions `.zero` and `.succ`. Indeed, any other type `α`
  admitting those would satisfy the base case and induction case above, so
  we get an inclusion function `ℕ → α` trough `ℕ.rec`.
-/
end A_theoretical_remark

end The_recursor

end Actually_inductive_inductive_types

end Inductive_types

section List_example
/-
  A common inductive type is the list type, the type of finite sequences.

  Here is how to define lists of naturals.
-/
inductive ListOfNat
| nil: ListOfNat
| cons: Nat → ListOfNat → ListOfNat
/-
  A list can either be empty (`.nil`) or start with a natural "head" and
  continue with a list "tail" (`.cons head tail`).

  Indeed, we have the isomorphism
    `ListOfNat ≅ Unit ⊕ Nat × ListOfNat`

  Here is a possible list:
-/
example: ListOfNat
  := .cons 3 (.cons 4 (.cons 2 (.cons 10 .nil)))

/-
  A list type can easily be generalized by using a _parameter_, as follows:
-/
inductive ListOf (τ: Type)
| nil: ListOf τ
| cons: τ → ListOf τ → ListOf τ
/-
  Note that a parameter used in an inductive type definition must be fixed
  throughout the whole definition. Above, all occurrences of `ListOf` are
  mentioning `τ` as their argument, forming `ListOf τ`.

  In general, a type `inductive T (x₁:…) ⋯ (xₙ:…)` must always use `T` as
  in `T x₁ … xₙ` whenever `T` occurs in the constructors' types. We can
  _not_ use `T e₁ … eₙ` with arbitrary expressions `e₁, …, eₙ`.

  [ Note: This will be relaxed later on when we will use both _parameters_
    and _indices_ ]

  In the constructor types, parameters occur as implicit arguments.
  We do not have to pass them explicitly.
    `List.cons: {τ : Type} → τ → ListOf τ → ListOf τ`
-/

/-
  Computing the length of a list is done recursively.
-/
def ListOf.length {τ}: ListOf τ → Nat
| .nil       => .zero
| .cons _ tl => tl.length.succ
/-
  Note that we do not have to write `τ: Type` since it is inferred.
  (We can if we want to, though.)
-/

/-
  Summing a list of naturals is easy to define.
-/
def ListOf.sum: ListOf Nat → Nat
| .nil       => 0
| .cons n ns => n + ns.sum

/-
  The `map` function applied the same operation `f` on all the list
  elements.
  Given
    `.cons x₁ (.cons x₂ … .nil)`
  we compute
    `.cons (f x₁) (.cons (f x₂) … .nil)`
-/
def ListOf.map {τ σ} (f: τ → σ): ListOf τ → ListOf σ
| .nil       => .nil
| .cons x xs => .cons (f x) (xs.map f)

/-
  The `filter` function takes a predicate `p: τ → Bool` on the list elements
  and removes from the list all the elements that do not satisfy `p`.
-/
def ListOf.filter {τ} (p: τ → Bool): ListOf τ → ListOf τ
| .nil => .nil
| .cons x xs =>
  if p x
  then .cons x (xs.filter p)
  else xs.filter p

/-
  __Exercise__: Define a function to concatenate two lists.
  Proceed by recursion on the first argument `xs`.
-/
def ListOf.append {τ} (xs ys: ListOf τ): ListOf τ
  := sorry

/-
  __Exercise__: Define a function to reverse a list.
  Exploit `append`.
-/
def ListOf.reverse {τ}: ListOf τ → ListOf τ
  := sorry

/-
  __Exercise__: Define a function that takes a binary function `f` and a
  value `a`, and maps the list
    `.cons x₁ (.cons x₂ (.cons x₃ (.cons x₄ .nil)))`
  to
    `f x₁ (f x₂ (f x₃ (f x₄ a)))`
  and behaves similarly on lists of other lengths as well.
  (Note the exact types below.)
-/
def ListOf.foldr {τ σ} (f: τ → σ → σ): ListOf τ → σ
  := sorry

/-
  __Exercise__: Define the sum of a `ListOf Nat` without recursion, using
  `foldr` instead.
-/

/-
  __Exercise__: Define a function that takes a binary function `f` and a
  value `a`, and maps the list
    `.cons x₁ (.cons x₂ (.cons x₃ (.cons x₄ … .nil)))`
  to
    `f (f (f (f a x₁) x₂) x₃) x₄)`
  and behaves similarly on lists of other lengths as well.
  (Note the exact types below.)
-/
def ListOf.foldl {τ σ} (f: σ → τ → σ): ListOf τ → σ
  := sorry

/-
  __Exercise__: Read and understand the recursor type.
-/
#check ListOf.rec

end List_example

section Tree_example
/-
  A binary tree type can be defined similarly to the list one.
-/
inductive TreeOf (τ: Type)
| leaf: τ → TreeOf τ
| branch: TreeOf τ → TreeOf τ → TreeOf τ

example: TreeOf String
  := .branch
  (.leaf "a")
  (.leaf "b")

example: TreeOf String
  := .branch
  (.leaf "a")
  (.branch
    (.leaf "b")
    (.leaf "c"))

/-
  __Exercise__: Define `TreeOf.map` analogously to what we did for lists.
  What type should it have?
-/

/-
  __Exercise__: Define a function `TreeOf.mirror` that exchanges the left
  subtrees with the right ones, in each point of the tree.
  Test your function on a simple tree.
-/
def TreeOf.mirror {τ}: TreeOf τ → TreeOf τ
  := sorry

/-
  __Exercise__: (challenging)
  Define `TreeOf.fold` analogously to the `foldr` function on lists.
  What type should it have?
-/
end Tree_example

section Expression_example
/-
  The inductive type of arithmetic expressions.
-/
inductive Expr
  -- Literal
| lit: Nat → Expr
  -- Addition
| add: Expr → Expr → Expr
  -- Multiplication
| mul: Expr → Expr → Expr

/-
  The evaluation function (the "semantics").
-/
def Expr.semantics: Expr → Nat
| lit n     => n
| add e₁ e₂ => e₁.semantics + e₂.semantics
| mul e₁ e₂ => e₁.semantics * e₂.semantics

/-
  __Exercise__: Add variables to expressions.
    `| var: String → Expr`
  Modify the semantics so that it now depends on an "environment" `ρ`
  that provides the value of each variable.
    `def Expr.semantics (ρ: String → Nat): Expr → Nat`
-/

/-
  __Exercise__: (challenging)
  Add subtraction to expressions.
    `| sub: Expr → Expr → Expr`
  The library `-` operator on `Nat` returns `0` where it should arguably be
  undefined because the actual result would be negative.
  Make our semantics avoid that case by making it return an "error" value
  instead. More precisely, return `Unit ⊕ Nat` where
    `.inl ()` is the "error" result value
    `.inr n` is a "successful" result `n: Nat`

  `def Expr.semantics: Expr → Unit ⊕ Nat`
-/

/-
  __Exercise__: Check out the `Option` library type and use that in the
  previous exercise.
-/
#print Option

/-
  __Exercise__: (challenging)
  Our expressions always have a `Nat` result. How boring!
  Add constructors for introducing and eliminating pairs.
    `| cons: Expr → Expr → Expr`
    `| π₁: Expr → Expr`
    `| π₂: Expr → Expr`
  Make the new semantics return a `Option Value`, as per the definition
  below. Note that we are allowing nested pairs, as in pairs-of-pairs-of-…
  so values are inductively defined too!
-/
inductive Value
| nat: Nat → Value
| pair: Value → Value → Value

end Expression_example

-- TODO more examples: propositions

-- TODO type formation rule, etc.
