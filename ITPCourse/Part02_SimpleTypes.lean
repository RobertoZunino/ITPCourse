
section The_function_type
/-
  Simple types -- Function types

  In Lean, we can define a function in several different ways.

  All the definitions below are equivalent:
-/
def double₁: Nat → Nat
  := λ n => n + n

def double₂: Nat → Nat
  := fun n => n + n

def double₃: Nat → Nat
  := λ n: Nat => n + n

def double₄: Nat → Nat
  | n => n + n

def double₅ (n: Nat): Nat
  := n + n

/-
  Above we can see the _function type_: `A → B` represents the type of
  functions from `A` to `B`. (It can also be written `A -> B`)

  The arrow symbol `→` can be typed as `\to` or `\->`.

  The term `λ n => …` denotes the function mapping `n` to `…`. Here, `λ` is
  not a variable but just a notation, similar to the integral symbol `∫` or
  the derivative symbol `∂`. We used `λ` in `double₁` above.

  The notation `λ` is widely used in computer science. In Lean, it can also
  be written as `fun` (see `double₂` above).

  When using `λ` (or `fun`), we can provide the type of the argument
  variable as in `double₃`, i.e. `λ n: Nat => …`. If we omit that type, Lean
  tries to _infer_ the type from the rest of the definition. When we defined
  `double₁` we wrote the type for the function, `Nat → Nat`, so Lean can
  infer `n: Nat`. This process is known as _type inference_, and relieves us
  from writing the type of variables as long there is no ambiguity, i.e.
  there is a _unique_ type that can be assigned to each variable.

  Note in passing that, even when inference makes writing types redundant,
  it might still be a good idea to annotate some variables with their types,
  to help _humans_ read the Lean code more fluently.

  The combination `def … := λ x => …` is so common that it can be shortened
  as in `double₄`. Note now the `:=` is missing there. (This notation will
  also be used together with _pattern matching_, as we will see in the
  future.)

  In `double₅` we can see a more familiar notational style: to define a
  function we can simply take some argument like `(n: Nat)` and return a
  result (`def … : Nat`). Here we already named the argument as `n` so there
  is no need to use a `λ`.
-/

/-
  To apply a function to its argument we can simply write `f x`.
-/
def eight: Nat := double₁ 4

/-
  __Exercise__: Verify the result above using `#eval`.
-/

/-
  Note how function application `f x` has a very high precedence:
-/
def ten₁: Nat := double₁ 4 + 2
/-
  is parsed as
-/
def ten₂: Nat := (double₁ 4) + 2
/-
  and _not_ as
-/
def twelve: Nat := double₁ (4 + 2)

end The_function_type

section Higher_order_functions
/-
  In Lean, functions values can be passed to other functions as parameters:
-/
def apply10 (f: Nat → Nat): Nat
  := f 10

#eval apply10 double₁   -- Result: `20`

/-
  Functions can also be returned by functions as results:
-/
def constant_fun (k: Nat): Nat → Nat
  := λ _n => k
  -- Note, we use `_n` here instead of `n` since otherwise Lean will
  -- warn that `n` is an unused variable. Using just `_` as in `λ _ => …`
  -- is also very common for this.

def constant_10: Nat → Nat := constant_fun 10

def ten₃: Nat := constant_10 42

/-
  __Exercise__: Verify `ten₃` is indeed `10`.
-/

/-
  Since functions-returning-functions are common in Lean, we can also use a
  more convenient notation.
-/
def constant_fun₂ (k: Nat) (_n: Nat): Nat := k

/-
  The above is equivalent to the previous definition.

  We can call `constant_fun₂ 10` and obtain the constant-10 function.
  We can also call `(constant_fun₂ 10) 42` or even `constant_fun₂ 10 42`
  and obtain `10` as the final result.

  __Exercise__: Try it.
-/

/-
  Here are some more examples. All of these are equivalent
-/
def compose₁ (f: Nat → Nat) (g: Nat → Nat): Nat → Nat
  := λ n => f (g n)

def compose₂ (f: Nat → Nat) (g: Nat → Nat) (n: Nat): Nat
  := f (g n)

def compose₃: (Nat → Nat) → (Nat → Nat) → (Nat → Nat)
  := λ f => λ g => λ n => f (g n)

def compose₄: (Nat → Nat) → (Nat → Nat) → (Nat → Nat)
  := λ f g n => f (g n)

def compose₅: (Nat → Nat) → (Nat → Nat) → Nat → Nat
  := λ f g n => f (g n)

/-
  __Exercise__: Complete the definition below.
  You can do it with or without calling the functions above.
  Try both alternatives.
-/
def compose₆ (f: Nat → Nat): (Nat → Nat) → Nat → Nat
  := sorry

/-
  Important notes:

  In terms, a repeated application like `a b c d e` implicitly associates
  to the _left_.

  I.e., it means `(((a b) c) d) e`: the result of the application `a b`
  (which must be a function) is applied to `c`, and the result of that
  (which must be a function) is applied to `d`, and the result of that
  (which must be a function) is applied to `e`.

  In types, a repeated arrow like `α → β → γ → δ`  implicitly associates
  to the _right_.

  I.e., it means `α → (β → (γ → δ))`: the type of functions having domain
  `α` returning a function having domain `β` returning a function having
  domain `γ` returning a value of type `δ`.

  We also write `λ a b … => …` for `λ a => λ b => …` as we did for
  `compose₅` above.
-/

/-
  __Exercise__: Prove that the above composition operators are indeed the
  same. Here is a first step:
-/
example: compose₁ = compose₂
  := rfl

section Multiple_arguments_in_functions
/-
  Thanks to the convention above, we can express multiple arguments in
  functions.
-/
def weird₁ (a: Nat) (b: Nat) (c: Nat): Nat
  := a + 2*b + 3*c

#check weird₁
#check weird₁ 10
#check weird₁ 10 20
#check weird₁ 10 20 30

/-
  When several consecutive arguments have the same exact type, we can
  shorten the notation as follows:
-/
def weird₂ (a b c: Nat): Nat
  := a + 2*b + 3*c

#check weird₂
#check weird₂ 10
#check weird₂ 10 20
#check weird₂ 10 20 30

end Multiple_arguments_in_functions

/-
  __Exercise__: Exploiting the previously defined composition operators,
  define the left-associative composition of three functions `f, g, h`,
  as well as their right-associative composition.
  Finally prove that the two coincide.
-/
def compose_left (f: Nat → Nat) (g: Nat → Nat) (h: Nat → Nat): Nat → Nat
  := sorry
def compose_right (f: Nat → Nat) (g: Nat → Nat) (h: Nat → Nat): Nat → Nat
  := sorry

example: compose_left = compose_right
  := sorry

/-
  __Exercise__: Try to prove that the following functions are equal:
    `λ n: Nat => n`
    `λ n: Nat => n+0`
    `λ n: Nat => 0+n`
  You will see that `rfl` does not always succeed here.

  This is because only one of the terms `n+0` and `0+n` is equal to `n`
  _by definition_. The other equality also holds, of course, but does not
  directly come from the definition of `+`.

  (We will see the actual definition of `+` in the future.)
-/
example: (λ n: Nat => n) = sorry
  := sorry

/-
  __Exercise__: In the same spirit of the previous exercise, experiment
  with the following list of functions. Some pairs of functions (but not
  all) are intuitively equal: see which pairs are also _definitionally_
  equal by testing which pairs can be proved equal using `rfl`.
  You can even try to prove a false statement, equating to distinct
  functions.

    `λ n: Nat => n`
    `λ n: Nat => n*1`
    `λ n: Nat => 1*n`
    `λ n: Nat => n+n`
    `λ n: Nat => n*2`
    `λ n: Nat => 2*n`
-/
end Higher_order_functions

section More_syntax
/-
  Recall `example` can be used as `def` when no name needs to be given.
  This also allows function syntax.
-/
example: Nat := 42

example (n: Nat): Nat := n+n

example (f: Nat → Nat): Nat := f (f 9)

/-
  When dealing with large expressions, it might be beneficial to define a
  few local variables to denote intermediate results. This can be done with
  `let` or `where`, as follows:
-/
example (f: Nat → Nat) (n: Nat): Nat
  :=
  let m: Nat := 10*n*n + 2*n + 7       -- the local definition
  m * f m                              -- the final result

example (f: Nat → Nat) (n: Nat): Nat
  :=
  let m := 10*n*n + 2*n + 7  -- the type can be omitted in many cases
  m * f m

example (f: Nat → Nat) (n: Nat): Nat
  := -- using a ; we can make a `let`-definition and use it on the same line
  let m := 10*n*n + 2*n + 7 ; m * f m

-- A definition can be local to a subexpression
example: Nat
  := (let m := 13 ; m*m) + 45

-- A `where` allows defining local variables after their use
example: Nat
  := a + b
  where
  a: Nat := 12
  b: Nat := 2*a

/-
  When nesting scopes, if the same variable is defined multiple times, the
  innermost declaration _shadows_ all the others.
-/
def shadowing₁: Nat
  :=
  let n := 5
  n + (let n := 10 ; n*n)  -- `5 + 10*10`

example: shadowing₁ = 105 := rfl

/-
  Avoid mixing `let` and `where`, it can be confusing!
-/
def shadowing₂: Nat
  :=
  let n := 10
  n*n + n  -- `10+10*10`, not `3+3*3`
  where
  n := 3

example: shadowing₂ = 110 := rfl


end More_syntax

section The_fundamentals_of_types
/-
  Now it is a good time to describe types in more detail. In type theory,
  a type is characterized by the following rules.

  - __Type formation__

    This rule explains how to form a type: what requirements must be met and
    what syntax to use.

    For instance, to form a function type one must choose the domain type
    `A`, the codomain type `B`, and finally write `A → B`.

  - __Introduction__

    This rule explains how to construct a value inside the type we just
    formed.

    For instance, to create a value of type `A → B`, we can use the
    term `λ a => …`. Therefore, `λ` represents the introduction rule for
    function types.

  - __Elimination__

    This rule explain how to use a previously constructed value inside
    the type we just formed.

    For instance, to use a function value `f: A → B` we need to choose a
    value `a: A` and then apply it to obtain `f a : B`. Therefore, function
    application is the elimination rule for function types.

  - __Computation__ (or β rule)

    This rule explains how to reduce (simplify) an introduction followed by
    an elimination.

    For instance, the term `(λ n => n+n) 5` introduces a functions and then
    eliminates it. It β-reduces to `5+5`.

    In general, the term `(λ x => e) t` β-reduces to `e` where all* the
    occurrences of `x` have been replaced with `t`.

    [ (*): Technically, we should say "all the free occurrences". ]

  - __Uniqueness__ (or η rule)

    This rule explains how to reduce (simplify) an elimination followed by
    an introduction.

    For instance `(λ x => f x)` eliminates a function and then reintroduces
    it. It η-reduces to `f`.

    This requires the term `f` not to depend on `x`. In other words, `f` can
    be any expression with no occurrences of `x`.

    *Note*: the uniqueness / η is not always applied by Lean.

  The actual theory of Lean is a bit more complicated, but these notions are
  enough to understand its basics.
-/

/-
  __Exercise__: We have not yet seen the product type `A × B` in detail, but
  you can probably guess how it should work.
  Try to sketch, in an informal way, the
    - introduction
    - elimination
    - computation / β
    - uniqueness / η
  rules for the product type.
-/
end The_fundamentals_of_types
