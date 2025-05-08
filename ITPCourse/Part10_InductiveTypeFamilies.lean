
section Inductive_type_families
/-
  So far, we saw inductive types with _parameters_,
    `inductive T (a₁: α₁) …`
  The values of such parameters `aᵢ` can not change within the inductive
  definition: whenever `T` is used, it must occur within `T a₁ …`.

  We now introduce _indices_. They play a similar role as parameters, but
  they can change.

  Here is a type for lists having length at most three.
-/
inductive ShortList (τ: Type): Nat → Type
| dim0: ShortList τ 0
| dim1: τ → ShortList τ 1
| dim2: τ → τ → ShortList τ 2
| dim3: τ → τ → τ → ShortList τ 3
/-
  This defines the type
    `ShortList: Type → Nat → Type`

  Its first argument `τ: Type` is a parameter, and works as usual.

  Instead, the second argument of type `Nat` is an _index_. Unlike
  parameters, indices can be used arbitrarily: their value is not
  constrained within the definition.
-/

/-
  The full syntax for an `inductive` type is therefore
    ```
    inductive T (param₁: π₁) … (paramₙ: πₙ)
              : (index₁: ι₁) → … → (indexₖ: ιₖ) → Sort u
    | cons₁: … → … → T param₁ … paramₙ e₁ … eₖ
    ⋮
    ```
  where `eᵢ` are arbitrary expressions.

  Constructors can, of course, mention `T` in their arguments to make `T`
  into an actually inductive type. Each use of `T` must have the form
    `T param₁ … paramₙ t₁ … tₖ`
  where the `paramᵢ` are fixed, but the indices can change.

  Observe this definition of `ListOf τ n`, the type of lists of length `n`.
-/
inductive ListOf (τ: Type): Nat → Type
| nil: ListOf τ 0
| cons: {n: Nat} → τ → ListOf τ n → ListOf τ n.succ

example: ListOf String 3
  := .cons "aaa" (.cons "bbb" (.cons "ccc" .nil))
  -- The exact value of `n` is inferred at each `.cons` use.

/-
  In the inductive definition above, the length index varies, and can be
  `0`, `n`, or `n.succ`, unlike the parameter `τ` which is fixed.

  We stress that here we are _not_ defining the type `ListOf τ k` in terms
  of itself, because its definition also depends on `ListOf τ k'` where
  `k'` is a different index.
  Instead, here we are actually defining the whole _type family_ `ListOf τ`
  in terms of itself. This is a family of type `Nat → Type`.

  In general, a type `T param₁ … index₁ …: Type` is not defined in terms of
  itself. The whole type family `T param₁ …: ⋯ → Type` is.

  The recursor is affected by this additional complexity. Now it involves a
  _motive_ which is no longer a plain function, but is a _dependent product_
  instead.
-/
#check ListOf.rec
/-
  Basically, the indices now occur in the motive telescope:
    `motive : (a : Nat) → ListOf τ a → Sort u`
  The parameters do not.

  __Exercise__: Read and understand the type of the recursor above.
-/
end Inductive_type_families

section Inductive_predicates
/-
  Indices commonly occur in inductive definitions that define a proposition,
  i.e. a type in `Prop`.

  This defines the property "being an even natural":
-/
inductive Even: Nat → Prop
| base: Even 0
| step: ∀ {n}, Even n → Even n.succ.succ

/-
  This defines the property "being a true boolean":
-/
inductive IsTrue: Bool → Prop
| isTrue: IsTrue true

/-
  Here is a more complex example: the Collatz conjecture.

  Given `n: Natural`, repeat these operations:
    if `n ≤ 1`, stop
    otherwise, if `n` is even, divide it by two
    otherwise, multiply it by three and add one
  The Collatz conjecture states that this eventually stops for all `n`.

  The Collatz relation associates to each `n` the number of steps that are
  required to stop the procedure above. It is a function. iff the conjecture
  holds.

  We can not easily define the function `def Collatz (n: Nat): Nat` since it
  would require to prove the conjecture. But we can easily define the
  relation.
-/
inductive Collatz: Nat → Nat → Prop
| base0: Collatz 0 0
| base1: Collatz 1 0
| stepEven: {n k: Nat} → Collatz (n+1) k    → Collatz (2*n+2) k.succ
| stepOdd : {n k: Nat} → Collatz (6*n+10) k → Collatz (2*n+3) k.succ
-- Note: we could have used "> 1" to simplify the last two cases.

example: Collatz 5 5
  := by
  apply Collatz.stepOdd (n:=1)
  apply Collatz.stepEven (n:=7)
  apply Collatz.stepEven (n:=3)
  apply Collatz.stepEven (n:=1)
  apply Collatz.stepEven (n:=0)
  exact Collatz.base1

--  Good luck in proving this ;-)
theorem Collatz_conjecture: ∀ n, ∃ k, Collatz n k
  := sorry

/-
  In the definition of `Collatz` the second index (the step counter) always
  increases, but the first index can either increase or decrease.

  The inductive definition has no issues with this lack of termination since
  it defines a relation. In the worst case, is the "recursion" goes on
  forever the relation will simply fail to hold.

  To stress the point, we now define a predicate which never holds because
  it involves an infinite "recursion", and an `inductive` definition
  provides the "smallest" (as-false-as-possible) predicate satisfying the
  constructors.
-/
inductive NonTriviallyFalse: Nat → Prop
| inc: ∀ n, NonTriviallyFalse n.succ → NonTriviallyFalse n
| dec: ∀ n, NonTriviallyFalse n      → NonTriviallyFalse n.succ

theorem NonTriviallyFalse.is_false (n: Nat): ¬ NonTriviallyFalse n
  := by
  intro h
  induction h
  case inc ntf ih =>
    exact ih
  case dec nft ih =>
    exact ih

end Inductive_predicates

section Equality
/-
  At last, the equality relation.
-/
inductive Equal {τ: Type} (x: τ): τ → Prop
| refl: Equal x x

example: Equal "abc" "abc"
  := .refl

/-
  (What a deceptively innocent-looking definition!)

  Equality is the smallest relation which satisfies the reflexivity axiom,
  as required by the `refl` constructor. This may seem quite intuitive.

  However, looking at the definition more closely, we can see that in the
  proposition `Equal x y` we have `x` as a _parameter_ and `y` as an
  _index_. Indeed, `x` is fixed to an arbitrary value, but `y` is then
  constrained to be equal to `x`.

  Perhaps, `Equal` should be better understood as if we defined the predicate
    `Equal x: τ → Prop`
  meaning "being equal to `x`".

  The recursor provides the substitution property of equality. Basically,
  given `Equal x a` the recursor proves
    `motive x ⋯ → motive a ⋯`
-/
#check Equal.rec

-- The substutition principle in a simpler form
theorem Equal.subst (τ: Type) (P: τ → Prop)
  (x y: τ)
  (eq: Equal x y)
  : P x → P y
  := by
  intro h
  cases eq
  exact h

-- TODO much more on equality

end Equality

-- TODO dependent match
