
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
def Equal.subst.{u} {τ: Type} (motive: τ → Sort u)
  {x y: τ}
  (eq: Equal x y)
  : motive x → motive y
  := by
  intro h
  cases eq
  exact h

/-
  The standard library equality relation is named `Eq`.
  The syntax `x = y` is a notation for `Eq x y`.
-/
#print Eq
/-
  `rfl` or `Eq.refl …` is the introduction form.
-/
example: Eq "abc" "abc" := rfl
example: "abc" = "abc"  := rfl              -- term-style `rfl`
example: "abc" = "abc"  := by rfl           -- it is also a tactic
example: "abc" = "abc"  := Eq.refl "abc"
example: "abc" = "abc"  := Eq.refl _        -- inferred

/-
  When eliminating an assumption `h: x = y`, we can use the same tactics
  we use for inductive types (`cases`, `induction`), but we also have a few
  specific ones for equality.

  The tactic `subst h` requires an hypothesis `h: x = expression` where
  `expression` does not involve `x`. It replaces `x` with `expression`
  _everywhere_: in all the hypotheses and in the goal. After this, `h` is
  removed making `x` completely disappear.

  `subst h` also works when `h: expression = x`.

  `subst x` also works, and automatically searches for a suitable hypothesis
  `h: x = …` or `h: … = x`.

  `subst` can not operate with equations of other forms.
-/
example
  (P: Nat → Prop)
  (n m: Nat)
  (h1: m*m + 42 = n)
  (h2: P n)
  : P (m*m + 42)
  := by
  subst h1   -- or `subst n`
  exact h2

/-
  The `rw [ h ]` tactic, instead, works with any equation `h: e₁ = e₂` and
  rewrites the _goal_ replacing `e₁` with `e₂`.

  `rw [ ←h ]` instead replaces `e₂` with `e₁` in the _goal_.
  (It is equivalent to `rw [ h.symm ]` which applies symmetry first to the
  term `h`.)

  `rw [ h1, h2, ←h3, … ]` chains multiple rewritings.

  `rw [ … ] at h'` rewrites the _hypothesis_ `h'` instead of the goal.
-/
example
  (P: Nat → Prop)
  (n m: Nat)
  (h1: n*n = m + 2)
  (h2: P (n*n + 4))
  : P (m + 6)
  := by
  rw [ h1 ] at h2
  exact h2

theorem eq_transitivity₁
  (a b c: Nat)
  (h1: a = b)
  (h2: b = c)
  : a = c
  := by
  rw [ h1 ]  -- on the goal
  exact h2

theorem eq_transitivity₂
  (a b c: Nat)
  (h1: a = b)
  (h2: b = c)
  : a = c
  := by
  rw [ h1 , h2 ]
  -- `rw` also tries `rfl` at the end automatically

/-
  `rw [ h ]` also works when `h` is a `∀`-quantified equality.
-/
example
  (P: Nat → Prop)
  (f g: Nat → Nat)
  (h1: ∀ k, f k = g k)
  (h2: P (f 42))
  : P (g 42)
  := by
  rw [ h1 ] at h2
  -- `rw [ h1 42 ] at h2` would also work, but `k` is inferred anyway
  exact h2

/-
  The `conv` tactic allows us to focus on only a _part_ of an expression
  before we use `rw`. This is useful when `rw` would otherwise rewrite the
  wrong part.
-/
example
  (P: Nat → Nat → Nat → Prop)
  (a b: Nat)
  (h1: a = b)
  (h2: P a a a)
  : P a b a
  := by
  -- `rw [ h1 ] at h2` rewrites too much and produces `P b b b`.
  conv at h2 =>
    arg 2 -- focus on the second argument
    rw [ h1 ]
  exact h2
/-
  In "`conv` mode" we can use the following tactics:
    - `left`/`lhs` focus on the left part
    - `right`/`rhs` focus on the left part
    - `arg k` focus on the `k`-th argument
    - `rw [ … ]` rewrite on the focused spot
    - `dsimp` simplify definitions and compute
    - `intro` enter a `λ x => …`
    and many others.
-/
example
  (a b: Nat)
  (h1: a = b)
  : (λ n => n + a + a + n)
  = (λ n => n + b + a + n)
  := by
  -- We could simply use `subst a ; rfl`, but let's use `conv` instead
  conv => -- focus on parts of the goal
    left     -- left hand side
    intro n  -- under `λ n =>`
    -- `n+a+a+n` means `((n+a)+a)+n`, so we need to navigate inside.
    arg 1
    arg 1
    arg 2
    rw [ h1 ]
  -- `rfl` is automatically tried after `conv`

/-
  The `calc` tactic works very well when chaining relations and applying
  transitivity-like results. This can be used to chain equalities
    `… = … = … = … = … = …`
  but also other relations
    `… ≤ … = … < … = … ≤ …`

  It implicitly uses lemmas from the libraries to perform the chaining.
-/
example
  (h1: 5 ≤ 6)
  (h2: 6 < 10)
  : 5 < 10
  := by
  calc
    5 = 2+3 := rfl
    _ = 1+4 := rfl
    _ ≤ 6   := h1
    _ = 3+3 := rfl
    _ < 10  := h2

-- TODO more exercises

section A_frequent_error_message
-- TODO convert this to `=` ?
/-
  A counter-intuitive fact is that by using the recursor or substitution
  principle on `h: Equal x y` we can _not_ always change `x` into `y` inside
  an arbitrary expression.

  More precisely, this fails when dependent products are involved.

  Consider this complex context:
    `x y: τ`
    `h: Equal x y`
    `α: τ → Type`
    `w: α x`
    `P: (t: τ) → α t → Prop`
    `k: P x w`
  Here, we can not replace `x` with `y` in `k` and simply obtain
    `k': P y w`
  since the term `P y w` is _ill-typed_: `w` has type `α x`, not `α y`.

  Formally, if we try to apply substitution we can not choose
    `motive := λ a => P a w`
  but that is ill-typed (`w` has not type `α a`).

  When dealing with standard equality, attempting to use `rw [ h ] at k`
  fails with an error "motive is ill-typed" for the reason above.
  `subst` does not have the same issue since it replaces a variable
  _everywhere_.
-/

/-
  In the example above, we can not obtain `P y w` but we _can_ obtain
    `P y (Equal.subst α h w)`
  which is now well-typed:
-/
example
  (τ: Type)
  (x y: τ)
  (h: Equal x y)
  (α: τ → Type)
  (w: α x)
  (P: (t: τ) → α t → Prop)
  (k: P x w)
  : P y (Equal.subst α h w)
  := by
  cases h
  dsimp [ Equal.subst ]  -- Expand the definition and compute
  exact k

-- The same, but with standard equality
example
  (τ: Type)
  (x y: τ)
  (h: x = y)
  (α: τ → Type)
  (w: α x)
  (P: (t: τ) → α t → Prop)
  (k: P x w)
  : P y (h ▸ w)   -- The general substitution principle for `=` is `▸`
  := by
  cases h
  dsimp -- Expand the definition of `▸` and compute
  exact k

end A_frequent_error_message

end Equality

section Dependent_pattern_matching
/-
  We previously described simple pattern matching as a way to eliminate
  inductive types (and type families). Essentially,
    ```
    match t with
    | pat₁ => e₁
    ⋮
    | patₖ => eₖ
    ```
  matches the value `t` against all the forms its could have, which are
  covered by the patterns `patⱼ`. Recall that the terms `eⱼ` must all share
  a common type `τ`, which is the also result type for the whole `match`
  expression.

  We also saw how it can also be used on multiple values at once:
    ```
    match t₁ , … , tₙ with
    | pat₁₁ , … , pat₁ₙ => e₁
    ⋮
    | patₖ₁ , … , patₖₙ => eₖ
    ```
  matches all the values `t₁ , … , tₙ` against the patterns below at the
  same time.

  To better understand what the `match` actually does, it is convenient to
  think of it as a function application
    `matchFun t₁ … tₙ`
  where
    `matchFun: τ₁ → … τₙ → τ`
  is an "elimination" function which is implicitly created by the `match`
  expression and maps all the arguments `tᵢ: τᵢ` to the result type `τ`.
  The type of this function is called the `motive` of the `match` and can be
  optionally written explicitly as follows:
-/
example: String
 := match (motive := Bool → String → Nat → String) -- The motive
   true , "hello" , 42 with                        -- The values to match
 | true  , _      , .zero   => "result A"          -- The cases
 | false , _      , .succ _ => "result B"
 | _     , s      , _       => s


/-
  The key idea of _dependent_ pattern matching is to make the type of
  `matchFun` into a _telescope_
    `matchFun: (x₁: τ₁) → … → (xₙ: τₙ) → τ`
  hence:
    - each `τᵢ` can depend on the `xₘ` such that `m < i`
    - `τ` can depend on all the `xₘ`

  This makes it possible to eliminate inductive type families in a
  meaningful way. Let us see a few examples.
-/

section Patterns_affect_what_comes_after
/-
  In a dependent match `match t₁ , … , tₙ` a pattern matching `tᵢ` can
  "refine" the types of the following terms.

  Observe this example carefully:
-/
def dep_match₁ (b: Bool) (x: if b then String else Nat): String
  := match (motive := (b: Bool) → (if b then String else Nat) → String )
    b     , x with
  | true  , y       => y
  | false , .zero   => "zero"
  | false , .succ _ => "non zero"
/-
  The `match b , x` involves a `x` whose type depends on `b`.

  Matching `b` against the pattern `true` and `x` against `y` causes the
  value of `y` to be `String` instead of `if …`. Hence, returning `y` as
  the resulting string is accepted.

  Similarly, matching `b` against the pattern `false` allows `x` to be
  matched against `.zero` and `.succ _`, as if it now had the `Nat` type.
-/

/-
  Another example:
-/
def dep_match₂ (b: Bool): if b then String else Nat
  := match (motive := (b: Bool) → if b then String else Nat)
    b with
  | true  => "hello"
  | false => (42: Nat)
/-
  Here the two expressions `"hello"` and `42: Nat` do not share the same
  type: one is a `String`, the other is a `Nat`.
  However, the former is used in the `b = true` case, and the latter is used
  in the `b = false` case, so we could say they do share
    `if b then String else Nat`
-/

/-
  Effectively, when a value `t` is matched against `pat`, the types
  mentioned in the `motive` get "refined" as when applying a function in a
  dependent product type.
  In `dep_match₂` we intuitively have:
    `matchFun: (b: Bool) → if b then String else Nat)` (motive)
    `matchFun true: String`
    `matchFun false: Nat`
  Similarly, `dep_match₁` we intuitively have:
    `matchFun: (b: Bool) → (if b then String else Nat) → String` (motive)
    `matchFun true: String → String`
    `matchFun false: Nat → String`
-/
end Patterns_affect_what_comes_after

section Patterns_affect_what_comes_before
/-
  When using inductive type families, i.e. `inductive` types with _indices_
  (and not just _parameters_), a pattern can also affect the matches that
  come before. This might be surprising at first.

  Observe this example:
-/
inductive IsString: Type → Type
| str: IsString String

example
  (α: Type)
  (a: α)
  (h: IsString α)
  : String
  := match (motive := (α: Type) → α → IsString α → String)
    α , a  , h with
  | _ , a' , .str => a'
/-
  Here, matching `h` with `.str` forces the type in `h: IsString α` to be
  refined as `OnlyType String`, since that is the index mandated by
  constructor `.str`. This causes `α` to be `String` and `a'` to have type
  `String`, hence returning `a'` as the result of the match is correct.

  Note that this happens even if we did not pattern match `α` against a
  pattern. Indeed, we can _not_ really do that: writing
    `match α with | String => …`
  is forbidden by Lean since `α: Type` and `Type` is not a type which allows
  pattern matching. Also, `String` is not a pattern, but a term.

  We can only pattern match `α` with "trivial" patterns like these:
    - the wildcard `_` as done above
    - a new variable, e.g. `β`, but Lean considers this to be an error since
      `β` would be later forced to be `String`, so there is no point in
      referring to `β` later on.
    - the special "inaccessible" pattern `.(e)` where `e` is any
      _expression_ (not required to be a pattern) that will be forced later
       on by other patterns.
-/
example
  (α: Type)
  (a: α)
  (h: IsString α)
  : String
  := match (motive := (α: Type) → α → IsString α → String)
    α         , a  , h with
  | .(String) , a' , .str => a'

/-
  Fortunately, most of these technical aspects can be automatically inferred
  by Lean, so we do not have to be so pedantic in our `match`es.
  For instance, here the motive and the inaccessible pattern are inferred.
-/
def dep_match₃
  (α: Type)
  (a: α)
  (h: IsString α)
  : String
  := match
    α , a  , h with
  | _ , a' , .str => a'

/-
  We can ask Lean to print the inferred motive and patterns, by turning the
  following option on.
  (Enclosing it in a `section` makes the option revert to normal later on.)
-/
section
set_option pp.motives.all true
#print dep_match₃
end

-- TODO Examples
end Patterns_affect_what_comes_before

-- TODO
end Dependent_pattern_matching
