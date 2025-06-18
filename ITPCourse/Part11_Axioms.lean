
section Axioms
/-
  Beyond the standard introduction / elimination principles of types, Lean
  features a few axioms.

  One of these is the law of excluded middle, whcih we have already
  discussed.
-/
#check Classical.em

section Choice
/-
  Another famous axiom is classical choice:
-/
#check Classical.choose
#check Classical.choose_spec
/-
  Essentially, given a proof of an existential quantified formula `∃x, …`,
  `Classical.choose` can be used to extract a witness `x` satisfying the
  property at hand. The axiom `Classical.choose_spec` ensures that the
  extracted value indeed satisfies the property.

  A typical use is to swap the order of quantifiers `∀x∃y` turning `y` into
  a choice function which depends on the value of `x`.
-/
example
  (τ σ: Type)
  (P: τ → σ → Prop)
  (h: ∀ x: τ,      ∃ y: σ , P x y)
  :   ∃ yf: τ → σ, ∀ x,     P x (yf x)
  := by
  -- `let` is like `have`, but remembers the actual definition and not just
  -- the type.
  let yf (x: τ): σ := Classical.choose (h x)
  exists yf
  intro x
  exact Classical.choose_spec (h x)
/-
  Note that we do not need to use choice to extract a witness when we do so
  to construct another _proof_ (i.e., a value inside some `p: Prop`). We can
  use plain elimination for that.
  We need choice when we need to use the witness to construct a non-proof
  (a value inside some `σ: Type`).
-/
example
  (τ: Type)
  (P Q: τ → Prop)
  (h1: ∀x, P x → Q x)
  (h2: ∃x, P x)
  : ∃x, Q x
  := by
  have ⟨ x, px ⟩ := h2  -- Elimination, no choice needed
  exists x
  apply h1
  exact px
/-
  In a sense, the axiom of classical choice can be used as a "workaround"
  for the limitation that we can not eliminate a proof to construct a
  non-proof.

  Note however that using axioms, like excluded middle and choice, prevents
  one to effectively compute the witness value:
-/
def HardConjecture: Prop
  := sorry  -- Think of your favorite conjecture here.

theorem easy:
  ∃n: Nat, (n = 0 ∧ HardConjecture) ∨ (n = 1 ∧ ¬ HardConjecture)
  := by
  by_cases hc: HardConjecture
  case pos =>
    exists 0
    left
    trivial -- USe assumptions and trivial properties
  case neg =>
    exists 1
    right
    trivial

noncomputable def witness: Nat
  := Classical.choose easy
/-
  We can not realistically use `#eval witness` and hope to see `0` or `1`
  printed.

  Also note that Lean forces us to declare this `def` as `noncomputable`
  since it involves choice.
-/
end Choice

section Functional_extensionality
/-
  Two functions are equal when they agree on all the points in the domain.

  This can not be proved by using introduction / elimination alone, so it is
  an axiom.
-/
#check funext
/-
  Usually, this axiom is invoked though the `funext x` tactic.
-/
example
  : (λ n m: Nat => n + m) = (λ n m: Nat => m + n)
  := by
  funext n
  funext m
  apply Nat.add_comm

end Functional_extensionality

section Propositional_extensionality
/-
  In Lean, two logically equivalent propositions are also considered
  _equal_.

  This is the `propext` axiom.
-/
#check propext

example: ("hello" = "hello") = True
  := by
  apply propext
  case a =>
  constructor
  case mp =>
    intro _
    constructor
  case mpr =>
    intro _
    rfl

/- __Exercise__: use excluded middle and `propext` to prove the following.
-/
example (p: Prop): p = True ∨ p = False
  := sorry

end Propositional_extensionality

end Axioms

section Quotient_types
/-
  A main feature of Lean are quotient types, i.e. types up-to some
  equivalence relation.

  Given an equivalence relation `r: α → α → Prop`, the type `Quot r`
  represents `α` up-to the relation `r`.

  (In Lean we can also take `r` to be an arbitrary relation. `Quot r`
  implicitly closes `r` under reflexivity, symmetry, and transitivity.)

  As a simple example, we identify the two `String`s `"a"` and `"b"`:
-/
def equivAB (x y: String): Prop
  := x=y ∨ (x="a" ∧ y="b") ∨ (x="b" ∧ y="a")

def QuotAB: Type := Quot equivAB

/-
  Introduction is performed using 'Quot.mk`:
-/
def str_hello: QuotAB := Quot.mk equivAB "hello"
def str_a: QuotAB     := Quot.mk equivAB "a"
def str_b: QuotAB     := Quot.mk equivAB "b"

/-
  Elimination requires, of course, a function which yields the same result
  on equivalent values.

  This is done using `Quot.lift`.
-/
def StringAB.length (s: QuotAB): Nat
  := Quot.lift String.length stable s
  where
  stable : ∀ s₁ s₂, equivAB s₁ s₂ → String.length s₁ = String.length s₂
    := by
    intro s₁ s₂ h1
    cases h1
    case inl eq =>
      subst eq
      rfl
    case inr h2 =>
      cases h2
      case inl h3 =>
        have ⟨ s₁_def , s₂_def ⟩ := h3
        rw [ s₁_def , s₂_def ]
        rfl
      case inr h3 =>
        have ⟨ s₁_def , s₂_def ⟩ := h3
        rw [ s₁_def , s₂_def ]
        rfl

/-
  As a computation/β rule,
    `Quot.lift f equiv stable_f (Quot.mk equiv x)`
  reduces to
    `f x`.
  There two terms are _definitionally_ equal.
-/

/-
  Introduction and elimination alone do not prove the main property of
  quotients: when `equiv x y` we want `Quot.mk equiv x = Quot.mk equiv y`.

  This is taken as an axiom:
-/
#check Quot.sound

example: str_a = str_b
  := by
  apply Quot.sound
  right
  left
  trivial

/-
  Note that the converse implication only holds when `equiv` is an actual
  equivalence relation. In such case we have that
  `Quot.mk equiv x = Quot.mk equiv y` implies `equiv x y`.

  (This is not an easy proof at first.)
-/
theorem quot_exact
  (α: Type)
  (equiv: α → α → Prop)
  (refl: ∀ x, equiv x x)
  (symm: ∀ {x y}, equiv x y → equiv y x)
  (trans: ∀ {x y z}, equiv x y → equiv y z → equiv x z)
  (x y: α)
  (h_eq: Quot.mk equiv x = Quot.mk equiv y)
  : equiv x y
  := by
  let P: α → Prop := equiv x
  have stable_P : ∀ (a b : α), equiv a b → P a = P b
    := by
    intro a b h1
    apply propext
    case a =>
    constructor
    case mp =>
      intro h2
      exact trans h2 h1
    case mpr =>
      intro h2
      exact trans h2 (symm h1)

  have h2: P x := refl x
  -- We perform a computation/β step backwards:
  change Quot.lift P stable_P (Quot.mk equiv x) at h2
  -- Now we can change the equivalence class.
  rw [h_eq] at h2
  -- We then perform a computation/β step forwards:
  dsimp at h2
  exact h2

/-
  An alternative to `Quot` types are `Quotient` types.

  `Quotient` is a wrapper around `Quot` that ensures that the relation
  used in `Quot` is indeed an equivalence relation.

  Using `Quotient` involves a few additional types: `Equivalence` and
  `Setoid`. The proposition `Equivalence r` states that `r` is an
  equivalence relation. A `Setoid α` instead is a structure that contains
  both a relation `r` and a proof of `Equivalence r`.
-/
#print Equivalence
#print Setoid

theorem AB_equivalence: Equivalence equivAB
  := sorry -- Left as an exercise.

def AB_setoid: Setoid String :=
  { r := equivAB
  , iseqv := AB_equivalence
  }

def QuotientAB := Quotient AB_setoid

/-
  Introduction is done using `Quotient.mk`. Now we use the setoid instead
  of the arbitrary relation.
-/
def qstr_hello: QuotientAB := Quotient.mk AB_setoid "hello"
def qstr_a: QuotientAB     := Quotient.mk AB_setoid "a"
def qstr_b: QuotientAB     := Quotient.mk AB_setoid "b"

/-
  Elimination is done via `lift`, as for `Quot`.
-/
#check Quotient.lift

/-
  These two theorems ensure that two equivalence classes are equal if and
  only if their representatives are equivalent.

  They are analogous to the ones for `Quot`.
-/
#check Quotient.sound
#check Quotient.exact

example: qstr_a = qstr_b
  := by
  apply Quotient.sound
  case a =>
  change (equivAB _ _)
  right
  left
  trivial

/-
  It is recommended to use `Quotient` instead of `Quot` in everyday usage,
  since in virtually all cases we are using equivalences anyway.

  `Quot` is seen as a low-level primitive, while `Quotient` is considered
  the "normal" tool to use.
-/

/-
  __Exercise__: Define integers as a quotient of `Nat × Nat`.
  Intuitively, a pair `(a,b)` represents the integer `a-b`.
  Consistently, let `(a,b) ≈ (c,d)` iff `a+d = c+b` (in `Nat`).
  Define some operations on integers such as addition.
  Optionally prove a few properties of additions exploiting the existing
  results on `Nat`.
  Also inspect the library `Int` type.

  __Exercise__: (challenging)
  Define rationals exploiting a suitable quotient of `Int × Nat`.

  __Exercise__: (challenging)
  Define real numbers.
  Start by defining Cauchy-converging sequences of rationals.
    ```
    structure CauchyConverging where
      seq: ℕ → ℚ
      seq_converges: ∀ …   -- property of seq
    ```
  Then take a suitable quotient.
  Note: you might want to require an exponentially fast convergence. This is
  convenient if you then want to define, say, addition.
-/
end Quotient_types

section Dependencies_among_axioms
/-
  It turns out that the axioms shown above are not independent: some of them
  actually imply the others.

  For instance, quotient types imply `funext`, so in Lean the latter is
  actually a theorem. This can be observed if we ask Lean to print the
  axioms it depends on.
-/
#print axioms funext   -- `Quot.sound`

/-
  Further, choice + `funext` (or quotients) + `propext` imply the law of
  excluded middle. This is known as Diaconescu's theorem.

  So, `Classical.em` is actually a theorem in Lean.
-/
#print axioms Classical.em     -- `propext`, `choice`, `Quot.sound`

end Dependencies_among_axioms

section Recap_exercises
/-
  __Exercise__: Prove the following property of the reflexive and transitive
  closure of a relation `r`.
  Use `funext` and `propext` as needed.
-/
inductive Refl_trans_closure {α: Type} (r: α → α → Prop): α → α → Prop
| refl: ∀ a, Refl_trans_closure r a a
| trans: ∀ a₁ a₂ a₃,
  Refl_trans_closure r a₁ a₂ →
  Refl_trans_closure r a₂ a₃ →
  Refl_trans_closure r a₁ a₃
| incl: ∀ a₁ a₂, r a₁ a₂ → Refl_trans_closure r a₁ a₂

theorem Rtc_idempotent {α: Type} (r: α → α → Prop)
  : Refl_trans_closure (Refl_trans_closure r) = Refl_trans_closure r
  := sorry

/-
  __Exercise__: Redo the previous exercise, adding symmetry to the
  properties. In this way, the closure is the smallest equivalence relation
  that includes `r`.
-/
end Recap_exercises
