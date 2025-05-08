/-
  We now discuss how to prove logical statements in Lean beyond basic
  equalities.
-/

section The_Curry_Howard_isomorphism
/-
  So far we focused on how to define mathematical objects in Lean.

  It turns out that the _same_ techniques can be applied to prove theorems
  as well. This is because there is a strong correspondence between
  propositions as types, known as the _Curry-Howard_ isomorphism.

  In brief, we have the following correspondences:

    Propositions            ↔ Types
    `True`                  ↔ `Unit`
    `False`                 ↔ `Empty`
    `p ∧ q` (conjunction)   ↔ `p × q` (product type)
    `p ∨ q` (disjunction)   ↔ `p ⊕ q` (sum types)
    `p → q` (implication)   ↔ `p → q` (function type)
    `∀ a:A, P a` (for all)  ↔ `(a:A) → P a` (dependent product type)

  The underlying idea is to regard a proposition as a _type_ denoting all
  the possible proofs for that proposition. Under this idea:

  - `True` has one proof, like `Unit` has one value.
  - `False` has no proofs, like `Empty` has no values.
  - A proof for `p ∧ q` is a pair `(proof_of_p, proof_of_q)`, like with
    product types.
  - A proof for `p ∨ q` is either `Or.inl proof_of_p` or `Or.inr proof_of_q`
    like with sum types.
  - A proof for `p → q` is a function that maps proofs of `p` into proofs of
    `q`, like with function types.
  - A proof for `∀ a:A, P x` is a function that maps any value `a:A` into a
    proof of `P a`.

  Propositions are therefore types, and they live in the `Prop` universe.
-/

/-
  Let's see a few examples. We recommend to move your cursor to the proofs
  blow and observe what type of variables are in scope at each point. These
  are effectively the hypotheses available at that point in the proof.

  Proving that `p → p` for any `p` essentially amounts to define the
  polymorphic identity
-/
theorem simple_implication: ∀ p: Prop, p → p
  := λ _p h => h   -- `h` is essentially an "hypothesis", here

/-
  Transitivity of `→` is proved by composing functions:
-/
theorem implication_trans: ∀ p q r: Prop, (p → q) → (q → r) → (p → r)
  := λ _p _q _r h1 h2 pr_p => h2 (h1 pr_p)

/-
  Commutativity of the `∧` corresponds to swapping pair components:
-/
theorem and_commut₁ (p q: Prop) (h: p ∧ q): q ∧ p
  := ⟨ h.2, h.1 ⟩

theorem and_commut₂ (p q: Prop) (h: p ∧ q): q ∧ p
  := match h with
  | ⟨ pr_p, pr_q ⟩ => ⟨ pr_q, pr_p ⟩

/-
  Idempotency of the `∨` is easily established:
-/
theorem or_idempot (p: Prop) (h: p ∨ p): p
  := match h with
  | .inl pr_p => pr_p  -- `Or.inl` can be shortened to `.inl`
  | .inr pr_p => pr_p  -- `Or.inr` can be shortened to `.inr`

/-
  `True` introduction is proved by `True.intro`.
-/
theorem triviality: True := True.intro

/-
  `False` elimination is done by `False.elim`
-/
theorem false_identity_for_or (p: Prop) (h: False ∨ p): p
  := match h with
  | .inl pr_false => pr_false.elim   -- This contradiciton proves anything!
  | .inr pr_p     => pr_p

/-
  A theorem involving a `∀` quantifier.
  Note that here `P: Nat → Prop` makes `P` a property on naturals.
-/
theorem all_or (P: Nat → Prop) (h: ∀ a b, P a ∨ P b): ∀ n, P n
  := λ n => or_idempot (P n) (h n n)   -- `P n` could also be `_`
/-
  Carefully inspect the types above.
  `h n n` has type `P n ∨ P n`, so `or_idempot` ends the proof.

  Note in passing that it would make sense to make the first argument of
  `or_idempot` to be implicit, so that we can hide that noise in the proof.
-/
end The_Curry_Howard_isomorphism

section Exercises
/-
  __Exercise__: Here is a list of propositions you can prove.
-/
example (p: Prop): p → (p ∧ True)
  := sorry

example (p: Prop): p → (p ∧ p)
  := sorry

example (p q r: Prop): (p → q → r) → (p ∧ q → r)
  := sorry

example (p q r: Prop): (p ∧ q → r) → (p → q → r)
  := sorry

example
  (f: Nat → Nat)
  (P Q: Nat → Prop)
  (h1: ∀ x, P x → Q (f x))
  (h2: ∀ y, P y)
  : ∀ n, Q (f n)
  := sorry

example  -- More challenging
  (f: Nat → Nat)
  (P: Nat → Prop)
  (h: ∀ x, P x → P (f x))
  : ∀ n, P n → P (f (f n))
  := sorry

example (p q: Prop): p → (q → p)
  := sorry

example (p q r: Prop): (p → q) → (p → q → r) → (p → r)
  := sorry

example (p q r: Prop): ((p → q) → p) → ((q → p) → q) → p ∧ q
  := sorry

example (p p' q q': Prop):
  (p → p') → (q → q') → (p ∧ q → p' ∧ q')
  := sorry

example (p p' q q': Prop):
  (p → p') → (q → q') → (p ∨ q → p' ∨ q')
  := sorry

example (p p' q q': Prop):
  (p' → p) → (q → q') → ((p → q) → (p' → q'))
  := sorry

end Exercises

section More_connectives
/-
  Negation `¬ p` stands for `p → False`.
-/
example (p: Prop): ¬(p ∧ ¬ p)
  := sorry

example (p q: Prop): ¬ q → (p ∨ q) → p
  := sorry

/-
  If-and-only-if `p ↔ q` is similar to `(p → q) ∧ (q → q)`.

  Check out `Iff.intro` and `Iff.elim` to understand how to use it.
  Alternatively, use the notation `⟨ … , … ⟩`, which works on all
  product-like types.
-/
theorem iff_example₁ (p: Prop): p ↔ (p ∨ p)
  := Iff.intro (.inl) (or_idempot p)
theorem iff_example₂ (p: Prop): p ↔ (p ∨ p)
  := ⟨ .inl , or_idempot p ⟩

example (p: Prop): p → p ∨ p
  := (iff_example₁ p).1
example (p: Prop): p → p ∨ p
  := (iff_example₁ p).mp
example (p: Prop): p → p ∨ p
  := match iff_example₁ p with
  | ⟨ pr , _ ⟩ => pr

/-
  __Exercise__: Prove the following.
-/
theorem yoneda (p: Prop)
  : p ↔ (∀ q: Prop, (p → q) → q)
  := sorry

example: False ↔ (∀ q: Prop, q)
  := sorry
example: True ↔ (∀ q: Prop, q)
  := sorry
example (p q: Prop)
  : p ∧ q ↔ (∀ r: Prop, p → q → r)
  := sorry
example (p q: Prop)
  : p ∨ q ↔ (∀ r: Prop, (p → r) → (q → r) → r)
  := sorry

end More_connectives

section Classical_logic
/-
  The logical system seen so far is powerful and can prove many theorems we
  can find in everyday mathematics. However, it can not prove them all.

  The logic seen so far is called _intuitionistic_, or _constructive_ logic,
  and is weaker than _classical_ logic, which lies at the foundation of
  modern mathematics. The most famous example of a classical theorem that is
  not intuitionistic is the law of excluded middle:
-/
def excluded_middle: Prop := ∀ p: Prop, p ∨ ¬ p
/-
  We will not show that `excluded_middle` is not provable with what we saw
  so far, but as an informal argument we might observe that a proof of this
  law (made under no assumptions) should intuitively reduce to one of these
  forms:
    `λ p => .inl proof_of_p`
    `λ p => .inr proof_of_¬p`
  However, if any one of these existed we could craft one of the following:
    `λ p => proof_of_p`  of type `∀ p: Prop, p`
    `λ p => proof_of_¬p` of type `∀ p: Prop, ¬p`
  and neither can exist without breaking the logic!

  However, even if it's not _provable_, we can still take it as an
  _assumption_.
-/
theorem em_example₁ (em: excluded_middle) (p q: Prop)
  : p ∨ (p → q)
  := match em p with
  | .inl pr_p  => .inl pr_p
  | .inr pr_np => .inr (λ pr_p => (pr_np pr_p).elim)

/-
  We can do even better. In Lean the law of excluded middle is already
  present in the standard library as a theorem which is proved from a few
  lower-level `axiom`s. We can use it through the name `Classical.em`. On
  use, the `axiom`s are silently added as implicit "invisible" assumptions,
  in the same spirit as much in the spirit of the previous example.
-/
theorem em_example₂ (p q: Prop)
  : p ∨ (p → q)
  := match Classical.em p with
  | .inl pr_p  => .inl pr_p
  | .inr pr_np => .inr (λ pr_p => (pr_np pr_p).elim)

#check em_example₂         -- No `em` assumption shown
#print axioms em_example₂  -- Three axioms implicitly used!

#check em_example₁         -- Explicit `em` assumption shown
#print axioms em_example₁  -- No axioms

/-
  Finally, note that adding `excluded_middle` to intuitionistic logic is
  enough to make it as powerful as classical logic.

  We can now make "proofs by cases" such as the following:
-/
example (p q r: Prop)
  (h1: p  → q)
  (h2: ¬p → r)
  : q ∨ r
  := match Classical.em p with
  | .inl pr_p  => .inl (h1 pr_p)
  | .inr pr_np => .inr (h2 pr_np)

/-
  __Exercise__: Prove the De Morgan's laws.
-/
example (p q: Prop)
  : ¬(p ∧ q) ↔ ¬ p ∨ ¬ q
  := sorry

example (p q: Prop)
  : ¬(p ∨ q) ↔ ¬ p ∧ ¬ q
  := sorry

/-
  __Exercise__: Prove the following.
-/
theorem peirce's_law (p q: Prop)
  : ((p → q) → p) → p
  := sorry

theorem double_negation (p: Prop)
  : ¬ ¬ p → p
  := sorry

theorem contrapositive (p q: Prop)
  : (p → q) ↔ (¬q → ¬p)
  := sorry

end Classical_logic

section Impredicativity
/-
  As a technical note, we remark that the type of propositions `Prop` is
  rather special, in that it is an _impredicative_ universe.

  Concretely, "for all" propositions, which are dependent product types,
  follow the following type formation rule:

    if  `x: τ` where `τ` is any type living in any universe
    and `P: τ → Prop`
    then `(x: τ) → P t` (which is the same as `∀ x: τ, P t`) is a type
         living in universe `Prop`.

  Note that `τ` can live in any universe (e.g. `Type 100`), yet the
  resulting "for all" proposition is fixed to be `Prop`. With predicative
  universes, `τ: Type u` would force the dependent product to live in
  `Type (max u …)`. Having a codomain in `Prop` keeps the universe level
  down.
-/

section Why_impredicativity?
/-
  Why is impredicativity important?

  Well, without it we could not easily write properties which quantify over
  "all the propositions" or "all the properties".
-/
def Leibniz_equality (τ: Type) (a b: τ): Prop
  := ∀ P: τ → Prop, P a → P b
/-
  If we only use predicative universes, we must place the property we are
  defining in a higher universe than the one we quantify over, as in the
  following example.
-/
def Leibniz_equality_in_type (τ: Type) (a b: τ): Type 1
  := ∀ P: τ → Type, P a → P b
/-
  Since the quantification on "all the properties `P`" is now restricted to
  universe `Type`, it does not involve those properties that are defined in
  terms of the `Leibniz_equality_in_type` property itself, which lives in
  `Type 1`.
-/

/-
  __Exercise__: (challenging)
  Try proving reflexivity and symmetry of the above equality relations.
  Note that, with the impredicative relation, we can prove symmetry by
  claiming that since `a` has the property `P` of "being equal to `a`",
  then `b` must satisfy the same property.
  The predicative relation prevents the same proof idea to be used.
  (It can still be proved symmetric, but we might not have seen enough Lean
  to handle that at this time.)
-/
end Why_impredicativity?

section Why_predicativity?
/-
  Counterpoint: if impredicativity is good to have, why don't we make `Type`
  impredicative like `Prop`?

  The issue is that impredicativity comes at a cost: in the presence of a
  few axioms like excluded middle and choice, it causes _proof irrelevance_:
  any two proofs `pr₁ pr₂: p` of the same theorem `p: Prop` are necessarily
  equal: `pr₁ = pr₂`. This is known as the Barbanera-Berardi paradox.

  This is not a significant issue in `Prop`, since when dealing with
  propositions we care only about whether a proof exists or not -- whether
  we have more than one proof, or whether two proofs are equal are legit
  questions but they are not nearly as interesting.

  Lean completely embraces proof irrelevance in `Prop`, making any two
  proofs of the same theorem to always by considered _definitionally_ equal:
-/
theorem true_or_true₁: True ∨ True := .inl True.intro
theorem true_or_true₂: True ∨ True := .inr True.intro
example: true_or_true₁ = true_or_true₂ := rfl
/-
  Proof irrelevance is fine in `Prop`, but we can not accept it in `Type`.
  If `Type` were impredicative, consequently causing proof irrelevance, we
  would have `true = false` in `Bool`, and `0 = 1` in `Nat`, since they
  would be proofs/terms of the same proposition/type.

  For these reasons, the best choice is to have an impredicative universe
  for propositions (`Prop`) and use predicative universes for everything
  else (`Type u`).
-/
end Why_predicativity?

section Proof_irrelevance_and_elimination
/-
  Since `Prop` is impredicative and because of proof irrelevance, Lean
  forbids to eliminate a proof to produce a non-proof.

  Formally, if we eliminate `t: τ` with `τ: Prop` to create a value inside
  type `σ`, then we must have `σ: Prop` as well.
  We have no such restriction with predicative universes.

  For example, we can _not_ write
    ```
    example: True ∨ True → Bool
    | .inl _ => true
    | .inr _ => false
    ```
  because `Bool` is not in `Prop`, i.e. it is not a proposition, while
  `True ∨ True` is in `Prop`.

  Instead, we _can_ write
-/
example: Bool → True ∨ True
| true  => .inl True.intro
| false => .inr True.intro

/-
  There are a few exceptions to this general rule.

  - The axiom of choice, `Classical.choose`. Using choice, we can extract a
    value (a non-proof) from a proof of existence. We will discuss it later.

  - The subsingleton exception. When proposition `p: Prop` is defined so
    that it can have at most one proof _by definition_ (a "subsingleton"),
    then there is no harm to allow elimination from `p` to any other type.

  For example, `True` and `False` are subsingletons. Instead, any `… ∨ …`
  proposition is not.

  The subsingleton exception allows to discard "impossible" cases in a
  definition, as in the following example:
-/
def extractLeft₁ (τ σ: Type) (x: τ ⊕ σ)
  -- Hypothesis: `x` is not of the form `.inr …`.
  (h: ∀ y, x = .inr y → False)
  : τ
  :=
  -- This is a form of dependent match we will discuss in the future.
  -- It does not fit within the simple pattern matching rules we saw so far.
  match x , h with
  | .inl t , _  => t
  | .inr s , h' =>
    -- Here, since `x = .inr s` we have that `h'` has the refined type
    --   `h': ∀ y, .inr s = .inr y → False`
    -- from which we can get a contradiction:
    let contr: False := h' s rfl
    -- Subsingleton elimination: from a proof of `False` we can derive `τ`.
    nomatch contr

end Proof_irrelevance_and_elimination

section The_general_dependent_product_type_formation_rule
/-
  If you are curious, the full general rule for dependent products, working
  in all universes is:

    if  `x: τ` where `τ: Sort u`
    and `f: τ → Sort v`
    then `(x: τ) → P t` is a type living in universe `Sort (imax u v)`
    where `imax u v` is `0` if `v = 0` and `max u v` otherwise.

  You can then obtain the predicative and impredicative type formation rules
  from the above and by recalling `Prop = Sort 0` and `Type u = Sort (u+1)`.
-/
end The_general_dependent_product_type_formation_rule

end Impredicativity

section Tactics
/-
  Proving theorems via plain Curry-Howard, i.e. by writing Lean terms, is
  a task that while feasible, can easily feel tiresome, especially when the
  propositions at hand become large. Even with the help of types and the
  "Lean InfoView" messages, it is easy to get lost.

  To help the human prover, _tactics_ provide a more familiar proving
  workflow, hiding the construction of the Lean term under a new vest.

  We can enter tactic mode with the keyword `by`:
-/
theorem tac₁ (p: Prop): p → p
  := by
  intro h  -- assume `p`, name the hypothesis `h`
  exact h  -- use term `h` to fill the goal type

#print tac₁  -- The underlying term can be seen here

/-
  The `intro` tactic essentially introduces the implication, creating
  an incomplete proof `λ h => …`, where the gap must still be filled.

  The `exact` tactic fills that gap with a term.
-/

/-
  We now see a few more tactics.

  The `constructor` tactic introduces certain logical connectives such as
  `∧` and `↔`. It might split the current goal in several sub-goals, all of
  which must be proved.
  The `case` tactic puts the focus on a single sub-goal, hiding all the
  information that is not relevant for it.
-/
theorem and_idem (p: Prop): p → p ∧ p
  := by
  intro h
  constructor -- Introduce the ∧
  -- Here we have _two_ goals to prove
  case left =>  -- First part of the goal
    exact h
  case right => -- Second part
    exact h

#print and_idem -- We can always see the underlying proof term

/-
  The `cases h` tactic performs pattern-matching on hypothesis `h`,
  producing a sub-goal for each of the forms it might have.
  For instance, on an `∨` it produces two sub-goals for the `inl` and `inr`
  cases. On an `∧` only one case is produced. On `False`, no cases are
  produced, effectively closing the current goal because the assumpions
  contain a contradiction.

  After `cases`, the `case` tactic can focus on each sub-goal, and add a few
  new hypotheses relative to each case, as it happens in pattern matching.

  When the goal is an `∨`, the tactics `left` and `right` correspond to the
  two introduction rules for the disjunction.

  Finally, when some of the hypothesis is an implication (or dependent
  product)
    `h: … → … → … → … → α`
  such that `α` is the current goal (or can be made such by suitably
  choosing the "dependent" variables) the tactic `apply h` proves the
  goal and creates a sub-goal for each of the arguments/assumptions of `h`.
  This is called _backward reasoning_, since it is driven by the goal.
-/
example (p q r: Prop)
  (h1: p → r)
  (h2: p ∨ q)
  : q ∨ r
  := by
  cases h2
  case inl h3 => -- `h3` is a new hypothesis
    right
    apply h1 -- backward reasoning
    exact h3
  case inr h3 => -- `h3` is a new hypothesis
    left
    exact h3

/-
  __Exercise__: The tactics `exact?` and `apply?` ask Lean to check if there
  is a simple way to close the goal, or to reduce it to some sub-goals
  through `apply`. These can suggest exploiting some assumption or some
  previous theorems, often from the Lean libraries.
  Try them!
  Note that they can fail to find a proof even when there is one -- they do
  not completely relieve the human prover from their task.
  When a solution is found, clicking it in the Lean InfoView pastes it in
  our code, which is quite convenient.
-/

/-
  Beyond _backward reasoning_, we can also use _forward reasoning_, i.e.
  proving intermediate results from the hypotheses at hand.
  `have h : τ := …` can prove such lemmas.
  Let's prove the transitivity of implication in both ways.
-/
example (p q r: Prop)
  (h1: p → q)
  (h2: q → r)
  : p → r
  := by
  intro h3
  apply h2  -- backward
  apply h1  -- backward
  exact h3

example (p q r: Prop)
  (h1: p → q)
  (h2: q → r)
  : p → r
  := by
  intro h3
  have h4: q := h1 h3   -- forward
  have h5: r := h2 h4   -- forward
  exact h5

/-
  Mixing term-style and tactic-style is also allowed:
-/
example (p q r: Prop)
  (h1: p → q)
  (h2: q → r)
  : p → r
  := by
  intro h3
  have h4: q := h1 h3   -- forward
  exact h2 h4

example (p q r: Prop)
  (h1: p → q)
  (h2: q → r)
  : p → r
  := by
  intro h3
  exact h2 (h1 h3)

example (p q r: Prop)
  (h1: p → q)
  (h2: q → r)
  : p → r
  := by
  exact λ h3 => h2 (h1 h3)

example (p q r: Prop)
  (h1: p → q)
  (h2: q → r)
  : p → r
  :=
  λ h3 => h2 (h1 h3)

/-
  After  `have … :=` a term is expected, but we can also use `by` there and
  exploit tactics.
-/
example (p q r: Prop)
  (h1: p → q)
  (h2: q → r)
  : p → r
  := by
  intro h3
  have h4: q := by
    -- sub-proof using tactics
    apply h1
    exact h3
  have h5: r := by
    -- sub-proof using tactics
    apply h2
    exact h4
  exact h5

/-
  Conjunction `∧` can be eliminated in several ways using tactics:
-/
example (p q: Prop): p ∧ q → q
  := by
  intro h
  exact h.2 -- Projection

example (p q: Prop): p ∧ q → q
  := by
  intro h
  cases h
  case intro h1 h2 => -- Pattern matching
    exact h2

example (p q: Prop): p ∧ q → q
  := by
  intro h
  have ⟨ h1 , h2 ⟩ := h  -- Matching `have`
  exact h2

example (p q: Prop): p ∧ q → q
  :=
  -- Term-style
  λ h => match h with
  | .intro _h1 h2 => h2

/-
  A few examples with `∀`:
-/
example (τ: Type) (f: τ → τ) (P: τ → Prop)
  (h1: ∀ x, P x → P (f x))
  (h2: ∀ y, ¬ P (f (f y))) -- Recall `¬` means `… → False`.
  : ∀ z, ¬ P z
  := by
  intro z h3 -- Introducing `∀` and `¬`
  have h4: P (f (f z)) := by
    apply h1 -- Uses x = f z
    apply h1 -- Uses x = z
    exact h3
  exact h2 z h4  -- Uses y = z

/-
  __Exercise__: Prove the following by backward reasoning.
  You only need `intro` and `apply`.
-/
example (τ: Type) (f g: τ → τ) (P: τ → Prop)
  (h1: ∀ x, P x → P (f x))
  (h2: ∀ y, P (f (g y)) → P (g (f y)))
  (h3: ∀ z, P (g z))
  : ∀ a, P (g (f a))
  := by
  sorry

/-
  __Exercise__: Prove the following.
-/
example (τ: Type) (P Q: τ → Prop)
  (h1: ∀ x, P x → Q x)
  (h2: ∀ y, P y)
  : ∀ z, Q z
  := by
  sorry

/-
  __Exercise__: Prove the following.
-/
example (τ: Type) (P: τ → Prop)
  (h1: ∀ x y, P x ∨ P y)
  : ∀ z, P z
  := by
  sorry

/-
  We can even use tactics to rule out impossible cases in a definition.
  (This will implicitly use dependent pattern matching, under the hood.)
-/
def extractLeft₂ (τ σ: Type) (x: τ ⊕ σ)
  -- Hypothesis: `x` is not of the form `.inr …`.
  (h: ∀ y, x = .inr y → False)
  : τ
  := by
  cases x
  case inl t =>
    exact t
  case inr s =>
    exfalso  -- Prove False instead of the current goal
    apply h s
    rfl      -- Same as exact rfl

end Tactics

-- TODO tactics for definitions
-- TODO propext, funext
