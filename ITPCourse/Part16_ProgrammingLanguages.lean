
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

section A_simple_functional_language
/-
  We formalize a simple functional language, which can be thought of a small
  subset of Lean itself.

  Our language is typed, and only uses the following types:
-/
inductive Ty
-- basic types
| nat: Ty               -- `ℕ`
-- simple types
| fn: Ty → Ty → Ty      -- `τ → σ`
-- product types
| prod: Ty → Ty → Ty    -- `τ × σ`

/-
  The meaning of a type `τ: Ty` (its "semantics") can be easily defined by
  mapping `τ` to an actual Lean type.
-/
def Ty.sem: Ty → Type
| .nat      => ℕ
| .fn τ σ   => τ.sem → σ.sem
| .prod τ σ => τ.sem × σ.sem

/-
  In Lean, each term is typed _in a context_. That is we have typings of the
  form
    `x₁: τ₁ , … , xₙ: τₙ ⊢ t : τ`
  representing the fact that term `t` has type `τ` under the assumptions
  `x₁: τ₁ , … , xₙ: τₙ` that assign types to variables. These assumptions
  are known as _the context_. For instance, in Lean we have
    `x: ℕ → ℕ × ℕ , y: ℕ , z : ℕ ⊢ x y: ℕ × ℕ`
  Note how each variable occurring in the term must be "declared" in the
  context. The context can have additional variables (e.g. `z`).

  To simplify our treatment, we avoid variable names. We will instead refer
  to variables in a context using their position, starting from the _right_.

  Coherently, we model a context as a sequence of types, omitting variable
  names.
-/
inductive Ctx
| nil: Ctx
| and: Ctx → Ty → Ctx

/-
  The semantics of a context `Γ = τ₁ , τ₂ , …` is the Lean type obtained by
  `((Unit × τ₁.sem) × τ₂.sem) × ⋯`
-/
def Ctx.sem: Ctx → Type
| .nil => Unit
| .and Γ τ => Γ.sem × τ.sem

/-
  We now define a "variable within a context". Any `x: Var Γ τ` represents a
  variable found in the context `Γ` and having type `τ`.

  Note that in this way we essentially forbid, by definition, "undeclared"
  variables, so that we will never have deal with those later on.
-/
inductive Var: Ctx → Ty → Type
| last: ∀ {Γ: Ctx} {τ: Ty}, Var (Γ.and τ) τ
| next: ∀ {Γ: Ctx} {σ: Ty} {τ: Ty}, Var Γ σ → Var (Γ.and τ) σ
/-
  Intuitively, `.last` is the last variable in the context, `.last.next` is
  the next-to-last, `.last.next.next` the one before that, and so on.
-/

/-
  The semantics of a variable is the projection that, given the semantics of
  a context, extracts the relevant component (which has the right type by
  construction).
-/
def Var.sem {Γ: Ctx} {τ: Ty}: Var Γ τ → Γ.sem → τ.sem
| .last   , (_ , v) => v
| .next x , (ρ , _) => x.sem ρ

/-
  Finally, we define "terms within a context". A `t: Term Γ τ` represents a
  term whose (free) variables occur in `Γ` and whose value has type `τ`.
-/
inductive Term: Ctx → Ty → Type
| var: ∀ {Γ τ},               -- Variable `x`
  Var Γ τ → Term Γ τ
-- basic types
| lit: ∀ {Γ},                 -- Literal `42`
  ℕ → Term Γ .nat
| add: ∀ {Γ},                 -- Addition `t₁ + t₂`
  Term Γ .nat → Term Γ .nat → Term Γ .nat
-- simple types
| lam: ∀ {Γ σ} (τ),           -- Lambda `λ x => t`
  Term (Γ.and τ) σ → Term Γ (τ.fn σ)
| app: ∀ {Γ τ σ},             -- Application `t₁ t₂`
  Term Γ (τ.fn σ) → Term Γ τ → Term Γ σ
-- product types
| cons: ∀ {Γ τ σ},            -- Pair `(t₁, t₂)`
  Term Γ τ → Term Γ σ → Term Γ (τ.prod σ)
| π₁: ∀ {Γ} {τ σ: Ty},        -- Projection `π₁(t)`
  Term Γ (τ.prod σ) → Term Γ τ
| π₂: ∀ {Γ} {τ σ: Ty},        -- Projection `π₂(t)`
  Term Γ (τ.prod σ) → Term Γ σ

/-
  The evaluation of a term (the "semantics") takes a `t: Term Γ τ`,
  a `ρ: Γ.sem` that provides a value of all the (free) variables in `t`, and
  returns a value of type `τ.sem`.
-/
def Term.sem {Γ: Ctx} {τ: Ty}: Term Γ τ → Γ.sem → τ.sem
| .var x   , ρ  => x.sem ρ
-- basic types
| .lit n   , ρ => n
| .add t u , ρ => Nat.add (t.sem ρ) (u.sem ρ)
-- simple types
| .lam τ t , ρ  => λ v => t.sem (ρ , v)
| .app t u , ρ  => t.sem ρ (u.sem ρ)
-- product types
| .cons t u , ρ => (t.sem ρ , u.sem ρ)
| .π₁ t     , ρ => (t.sem ρ).fst
| .π₂ t     , ρ => (t.sem ρ).snd

/-
  Finally, an example:
    `λ n m: ℕ => (n+m , n)` of type `ℕ → (ℕ → (ℕ × ℕ)`
-/
def myTerm: Term .nil (Ty.nat.fn (Ty.nat.fn (Ty.nat.prod .nat)))
  := Term.lam .nat      -- `λ n`
    (Term.lam .nat      -- `λ m`
    (Term.cons          -- `(… , …)`
      ((Term.var Var.last.next).add (.var Var.last))    -- `n + m`
      (.var Var.last.next)                              -- `n`
    ))

/-
  We can prove it has the intended semantics!
-/
example: myTerm.sem () = λ n m: ℕ => (n+m, n)
  := by
  funext n
  funext m
  simp [myTerm, Term.sem, Var.sem]

/-
  __Exercise__: Add sum types, and their related terms, to the language
  above.
-/

/-
  As a final remark, we note that the functional language above lacks
  several important features which are common in real-world languages.

  For instance, the language does not allow any form of recursion.
  Some kinds of recursion, such as the so-called "primitive recursion" could
  be added with some effort. Instead, adding general recursion, and allowing
  non-terminating terms, requires a more complex semantics. We can no longer
  simply use Lean functions, since those are always terminating.

  Further, the language does not involve more complex types, such as
  polymorphic or dependent types. Again, adding these would  make the
  semantics significantly come complex.
-/
end A_simple_functional_language

section An_imperative_language
/-
  We now define a simple imperative language, a much simplified variant of
  Python / Java / C / …

  We only use global variables (whose names are a `String`), and only allow
  integer-valued expressions of the following forms:
-/
inductive Exp
| lit: ℤ → Exp            -- Literal (e.g. `42`)
| var: String → Exp         -- Variable `x`
| add: Exp → Exp → Exp      -- `e₁ + e₂`
| sub: Exp → Exp → Exp      -- `e₁ - e₂`
| times: Exp → Exp → Exp    -- `e₁ * e₂`

/-
  To evaluate an expression, we need a `State` providing the values for the
  variables. We denote states with `σ`.
-/
def State := String → ℤ

def State.update (σ: State) (x: String) (v: ℤ): State
  := Function.update σ x v

/-
  The evaluation of an expression (the "semantics") is easily defined by
  recursion.
-/
def Exp.sem (σ: State): Exp → ℤ
| .lit v       => v
| .var x       => σ x
| .add e₁ e₂   => e₁.sem σ + e₂.sem σ
| .sub e₁ e₂   => e₁.sem σ - e₂.sem σ
| .times e₁ e₂ => e₁.sem σ * e₂.sem σ

/-
  The statements, or _commands_, of our language are defined as follows:
-/
inductive Com
| skip: Com                   -- `skip`, i.e. "do nothing"
| let_: String → Exp → Com    -- `let x = e`
| comp: Com → Com → Com       -- `c₁ ; c₂`
| if_: Exp → Com → Com → Com  -- `if e ≠ 0 then c₁ else c₂`
| while_: Exp → Com → Com     -- `while e ≠ 0 do c`

/-
  The execution of commands (the "semantics") is provided through the
  following relation. This relation is known as the "big-step operational
  semantics" and we have `Com.sem c σ σ'` when the execution of command `c`
  starting from the initial state `σ` terminates in the final state `σ'`.
-/
inductive Com.sem: Com → State → State → Prop
| skip: ∀ {σ},
  sem .skip σ σ     -- Don't change the state
| let_: ∀ {σ x e},
  sem (.let_ x e) σ (σ.update x (e.sem σ))  -- Update the value of `x`
| comp: ∀ {σ₁ σ₂ σ₃ c₁ c₂},
  sem c₁ σ₁ σ₂ →    -- Run `c₁` first
  sem c₂ σ₂ σ₃ →    -- Then run `c₂`
  sem (c₁.comp c₂) σ₁ σ₃
| ifTrue: ∀ {σ₁ σ₂ e c₁ c₂},
  (e.sem σ₁ ≠ 0) →  -- Ensure the guard is true
  sem c₁ σ₁ σ₂ →    -- Run `c₁`, the "then" branch
  sem (.if_ e c₁ c₂) σ₁ σ₂
| ifFalse: ∀ {σ₁ σ₂ e c₁ c₂},
  (e.sem σ₁ = 0) →  -- Ensure the guard is false
  sem c₂ σ₁ σ₂ →    -- Run `c₂`, the "else" branch
  sem (.if_ e c₁ c₂) σ₁ σ₂
| whileTrue: ∀ {σ₁ σ' σ₂ e c},
  (e.sem σ₁ ≠ 0) →            -- Ensure the guard is true
  sem c σ₁ σ' →               -- Run `c`, the loop body
  sem (.while_ e c) σ' σ₂ →   -- Rerun the loop again
  sem (.while_ e c) σ₁ σ₂
| whileFalse: ∀ {σ e c},
  (e.sem σ = 0) →         -- Ensure the guard is false
  sem (.while_ e c) σ σ   -- Don't change the state

/-
  The semantics of commands is deterministic, i.e., it admits at most one
  final state.
-/
theorem Com.sem_deterministic
  (c: Com) (σ σ₁ σ₂: State)
  (h1: c.sem σ σ₁)
  (h2: c.sem σ σ₂)
  : σ₁ = σ₂
  := by
  revert σ₂
  induction h1 <;> clear c σ σ₁
  case skip σ =>
    intro σ₂ h1
    cases h1
    rfl
  case let_ σ x e =>
    intro σ₂ h1
    cases h1
    rfl
  case comp σ σ' σ'' c₁ c₂ sem₁ sem₂ ih₁ ih₂ =>
    clear sem₁ sem₂
    intro σ₂ h
    cases h
    case comp σₘ sem₁ sem₂ =>
    have h1 := ih₁ _ sem₁
    subst σₘ
    exact ih₂ _ sem₂
  case ifTrue σ σ' e c₁ c₂ esem csem ih =>
    clear csem
    intro σ₂ h
    cases h
    case ifTrue esem₂ csem₂ =>
      exact ih _ csem₂
    case ifFalse esem₂ csem₂ =>
      contradiction
  case ifFalse σ σ' e c₁ c₂ esem csem ih =>
    clear csem
    intro σ₂ h
    cases h
    case ifTrue esem₂ csem₂ =>
      contradiction
    case ifFalse esem₂ csem₂ =>
      exact ih _ csem₂
  case whileTrue σ σ' σ'' e c esem csem₁ csem₂ ih₁ ih₂ =>
    clear csem₁ csem₂
    intro σ₂ h
    cases h
    case whileTrue σ'' esem' csem₁ csem₂ =>
      have h := ih₁ _ csem₁
      subst σ''
      exact ih₂ _ csem₂
    case whileFalse esem2 =>
      contradiction
  case whileFalse σ e c esem  =>
    intro σ₂ h
    cases h
    case whileTrue esem2 csem2 =>
      contradiction
    case whileFalse esem2 =>
      rfl

/-
  The semantics of commands is not total, i.e., it might happen that for
  some command `c` and initial state `σ` there is no final state `σ'`.
  Intuitively, this happens when `c` "runs forever", as it happens when `c`
  is the command `while 1 ≠ 0 do skip`.
-/
lemma Com.sem_non_total'
  {c: Com} {σ σ': State}
  (h: c.sem σ σ')
  : c ≠ (.while_ (.lit 1) .skip)
  := by
  intro eq
  induction h <;> try contradiction
  -- Almost all cases generate a `contradiction`, so only one survives!
  case whileFalse σ₁ e₁ c₁ esem =>
    clear c σ σ'
    cases eq
    case refl =>
    dsimp [Exp.sem] at esem
    contradiction

theorem Com.sem_non_total
  : ∃ (c: Com) (σ: State),
    ¬∃ (σ': State), c.sem σ σ'
  := by
  exists (.while_ (.lit 1) .skip)
  exists (λ _ => 0)
  intro h
  replace ⟨ σ' , h ⟩ := h
  replace h := Com.sem_non_total' h
  contradiction

end An_imperative_language

section Correctness_of_imperative_programs
/-
  We formalize a well-known technique to prove imperative programs correct
  without having to directly involve the definition of `Com.sem` and work
  with complex inductive proofs.

  We start by defining the form of correctness we are interested in. Given
  two sets of states `P` and `Q` ("assertions") and `c: Com`, we say that
  the triple `P, c, Q` is _valid_ if it satisfies the definition below:
-/
abbrev Assert: Type := Set State

def validTriple (P: Assert) (c: Com) (Q: Assert): Prop
  := ∀ σ₁ σ₂, σ₁ ∈ P → c.sem σ₁ σ₂ → σ₂ ∈ Q
/-
  In other words, a valid triple guarantees that if we execute `c` from an
  initial state `σ₁ ∈ P`, and we terminate in a final state `σ₂`, then we
  have that `σ₂ ∈ Q`.

  (Note that this does not ensures that `c` terminates -- for this reason it
  is sometimes called "partial validity".)
-/

/-
  Below, we formalize the notion of Hoare triple `hoare P c Q`, where `P`
  and `Q` are set of states ("assertions"), and `c: Com`. We will see that
  the relation `hoare` is constructed so to only include triples that are
  _valid_.
-/
inductive hoare: Assert → Com → Assert → Prop
| skip: ∀ P,
  hoare P .skip P
| let_: ∀ P x e,
  hoare {σ | (σ.update x (e.sem σ)) ∈ P}
        (.let_ x e)
        P
| comp: ∀ {P Q R c₁ c₂},
  hoare P c₁ Q →
  hoare Q c₂ R →
  hoare P (c₁.comp c₂) R
| if_: ∀ e c₁ c₂ P Q,
  hoare {σ | σ ∈ P ∧ e.sem σ ≠ 0} c₁ Q →
  hoare {σ | σ ∈ P ∧ e.sem σ = 0} c₂ Q →
  hoare P (.if_ e c₁ c₂) Q
| while_: ∀ {e c P},
  hoare {σ | σ ∈ P /\ e.sem σ ≠ 0} c P →
  hoare P (.while_ e c) {σ | σ ∈ P ∧ e.sem σ = 0}
| prepost: ∀ {P₁ P₂ Q₁ Q₂: Assert} {c},
  P₂ ⊆ P₁ → Q₁ ⊆ Q₂ →
  hoare P₁ c Q₁ → hoare P₂ c Q₂

/-
  A small but convenient simplification of `hoare.prepost`.
-/
theorem hoare.pre: ∀ {P P' Q c},
  P ⊆ P' →
  hoare P' c Q →
  hoare P c Q
  := by
  intro P P' Q c h1 h2
  exact hoare.prepost h1 (by rfl) h2

/-
  We can prove, by induction, that all the triples `hoare P c Q` are
  indeed valid.

  The proof of this result involves `Com.sem`.
-/
theorem hoare.correctness {P c Q}
  : hoare P c Q → validTriple P c Q
  := by
  intro h
  induction h <;> clear P c Q
  case skip P =>
    unfold validTriple
    intro σ₁ σ₂ p₁ sem
    cases sem
    case skip =>
    exact p₁
  case let_ P x e =>
    unfold validTriple
    intro σ₁ σ₂ p₁ sem
    cases sem
    case let_ =>
    exact p₁
  case comp P Q R c₁ c₂ h₁ h₂ ih₁ ih₂ =>
    unfold validTriple
    intro σ₁ σ₂ p₁ sem
    cases sem
    case comp σ' sem₁ sem₂ =>
    have q': σ' ∈ Q := ih₁ σ₁ σ' p₁ sem₁
    exact ih₂ σ' σ₂ q' sem₂
  case if_ e c₁ c₂ P Q h₁ h₂ ih₁ ih₂ =>
    unfold validTriple
    intro σ₁ σ₂ p₁ sem
    cases sem
    case ifTrue sem_e sem₁ =>
      apply ih₁ σ₁ σ₂ _ sem₁
      exact ⟨ p₁ , sem_e ⟩
    case ifFalse sem_e sem₂ =>
      apply ih₂ σ₁ σ₂ _ sem₂
      exact ⟨ p₁ , sem_e ⟩
  case while_ e c P h ih =>
    intro σ₁ σ₂ p₁ sem
    -- Name the while command as `w`, so that we can use induction.
    generalize w_def: Com.while_ e c = w at sem
    -- We need a nested induction for the while case.
    induction sem <;> try contradiction
    -- Most cases cause a `contradiction`! Only two survive.
    case whileTrue σ'₁ σ' σ'₂ e' c' esem csem wsem ih₁ ih₂ =>
      cases w_def
      case refl =>
      clear ih₁ -- Useless
      unfold validTriple at ih
      have p' := ih _ _ ⟨ p₁ , esem ⟩ csem
      exact ih₂ p' rfl
    case whileFalse σ' e' c' esem =>
      cases w_def
      case refl =>
      exact ⟨ p₁ , esem ⟩
  case prepost P₁ P₂ Q₁ Q₂ c subP subQ h ih =>
    unfold validTriple
    intro σ₁ σ₂ p₁ sem
    apply subQ
    apply ih σ₁ σ₂ _ sem
    apply subP
    exact p₁

section Hoare_example_double
/-
  We showcase the correctness theorem with a basic example.

  Here is a simple command that doubles the value of `x`, assuming `x ≥ 0`.
  ```python
    y = 0
    while x ≠ 0:
      y = y + 2
      x = x - 1
    x = y
  ```
  When formalized using `Com`, this results into:
-/
def double: Com
  :=  -- (Yes, it's barely human-readable)
  (Com.let_ "y" (.lit 0)).comp
  ((Com.while_ (Exp.var "x")
    ((Com.let_ "y" (.add (.var "y") (.lit 2))).comp
     (Com.let_ "x" (.sub (.var "x") (.lit 1))))
  ).comp
  (Com.let_ "x" (.var "y")))

/-
  We now prove `double` is correct.

  We first establish the Hoare triple.
  (Again, we are neglecting the case where `doubles` does not halt, i.e.,
  the case `x < 0`, since partial validity does not care.)
-/
theorem double.hoareTriple₁ (X: ℤ):
  hoare {σ | σ "x" = X} double {σ | σ "x" = 2 * X}
  := by
  unfold double

  -- We make a skeleton proof first, following the structure of `double`.
  apply hoare.comp ?let1 (hoare.comp ?while_ ?let2)

  -- If we inspect the cases now, we observe a bunch of unknown assertions
  -- that Lean denotes with `?m.…`. These are called _metavariables_, and
  -- represent the intermediate assertions that were not fixed by the above
  -- `apply`. We can fix them later, choosing any value we want for them, as
  -- long as each metavariable has the same value in all the cases.

  -- We can prove the three subgoals in any order, but it is convenient to
  -- start from `?while_`, so to fix the invariant immediately.
  -- That will make the invariant available in the other cases, replacing
  -- its metavariable.
  case while_ =>
    -- Here's the invariant:
    apply hoare.while_ (P := {σ | σ "y" = 2*(X - σ "x")})
    apply hoare.comp ?c1 ?c2
    -- We start from `c2` so that the intermediate assertion is then
    -- available in the other case `c1`.
    case c2 =>
      apply hoare.let_
    case c1 =>
      apply hoare.pre ?pre ?c1
      -- Again, we start from `c1` to fix the assertion.
      case c1 =>
        apply hoare.let_
      case pre =>
        intro σ
        simp [State.update, Exp.sem]
        intro h_y h_x
        rw [h_y]
        ring
  case let2 =>
    apply hoare.pre ?pre ?c
    case c =>
      apply hoare.let_
    case pre =>
      intro σ
      simp [State.update, Exp.sem]
      intro h_y h_x
      rw [h_y, h_x]
      ring
  case let1 =>
    apply hoare.pre ?pre ?c
    case c =>
      apply hoare.let_
    case pre =>
      intro σ
      simp
      intro x_eq
      simp [Exp.sem, State.update]
      rw [x_eq]
      simp only [Int.sub_self]

/-
  Finally, we invoke `hoare.correctness` to prove that `double` indeed
  doubles the value of the variable `x`.
-/
theorem double.correct (X σ σ')
  : σ "x" = X
  → double.sem σ σ'
  → σ' "x" = 2 * X
  := by
  apply hoare.correctness (double.hoareTriple₁ X)

section More_automation
/-
  We can set up some automation so that proving `hoare P c Q` can be done
  using `calc` in an arguably more natural way.

  We start by defining an alternative `hoare` relation with reordered
  arguments. We also use the `notation` command so that we can write
    `Q <~c~ P`
  instead of `hoare P c Q`.
-/
abbrev hoare.flip (c: Com) (Q P: Assert) := hoare P c Q

notation Q " <~" c "∼ " P => hoare.flip c Q P

/-
  We then set up a few `Trans` type class instances.
  The first is used to combine
    `R <~c₂~ Q`
    `Q <~c₁~ P`
  into
    `R <~(c₁;c₂)~ P`
  This is based on `hoare.comp`.
-/
instance instTransHoareComp (c₁ c₂: Com)
  : Trans (hoare.flip c₂) (hoare.flip c₁) (hoare.flip (c₁.comp c₂)) where
  trans := λ h₂ h₁ => hoare.comp h₁ h₂

/-
  The second instance combines
    `Q <~c~ P`
    `P ⊇ P'`
  into
    `Q <~c~ P'`
  This is based on `hoare.prepost`.
-/
instance instTransHoarePre (c: Com)
  : Trans (hoare.flip c) Superset (hoare.flip c) where
  trans := by
    intro P' P Q h supP
    exact hoare.prepost supP (by rfl) h

/-
  One more instance, similar to the previous one.
-/
instance instTransHoarePost (c: Com)
  : Trans Superset (hoare.flip c) (hoare.flip c) where
  trans := by
    intro P' P Q subP h
    exact hoare.prepost (by rfl) subP h

/-
  Finally, we can exploit the above machinery to re-establish our triple.

  Using `¢alc`, we compute hoare assertions bottom-up, starting from the
  "last line of code" of `double` and moving upwards. So, the first item
  inside `calc` corresponds to the last `.let_`, and so on.

  We never have to explicitly write commands and assertions, except for
  the assertion immediately after the `.while_`, which can not be computed
  automatically.
-/
theorem double.hoareTriple₂ (X: ℤ):
  hoare {σ | σ "x" = X} double {σ | σ "x" = 2 * X}
  := by
  unfold double

  let inv: Assert := {σ | σ "y" = 2*(X - σ "x")}
  let guard: Exp := (.var "x")

  calc
    _ <~_∼ _ := by apply hoare.let_
    _ ⊇ {σ | σ ∈ inv ∧ guard.sem σ = 0} := by
      simp [Exp.sem, State.update, guard, inv]
      intro σ h1 h2 ; rw [h1,h2] ; ring
    _ <~_∼ _ := by
      apply hoare.while_
      calc
        _ <~_∼ _ := by apply hoare.let_
        _ <~_∼ _ := by apply hoare.let_
        _ ⊇ _ := by
          simp [Exp.sem, State.update, inv] ; intro σ h1 h2 ; rw [h1] ; ring
    _ <~_∼ _ := by apply hoare.let_
    _ ⊇ _ := by
      simp [Exp.sem, State.update, inv] ; intro σ h ; rw [h] ; ring

end More_automation
end Hoare_example_double

section Hoare_example_power
/-
  A simple algorithm to compute the power `a ^ b`.

  ```python
  x = 0
  r = 1
  while x-b ≠ 0:
    r = r * a
    x = x + 1
  ```
-/
def power: Com :=
  (Com.let_ "x" (.lit 0)).comp
  ((Com.let_ "r" (.lit 1)).comp
  (.while_ (.sub (.var "x") (.var "b"))
    ((Com.let_ "r" (.times (.var "r") (.var "a"))).comp
    (.let_ "x" (.add (.var "x") (.lit 1))))
  ))

theorem power.hoareTriple (A B: ℕ)
  : hoare {σ | σ "a" = A ∧ σ "b" = B} power {σ | σ "r" = A^B }
  := by
  unfold power

  let inv: Assert :=
    {σ | σ "x" ≥ 0 ∧ σ "r" = A ^ (σ "x").natAbs
       ∧ σ "a" = A ∧ σ "b" = B }
  let guard: Exp := .sub (.var "x") (.var "b")

  calc
    _ ⊇ {σ | σ ∈ inv ∧ guard.sem σ = 0} := by
      simp [Exp.sem, inv, guard] ; intro σ hx hr ha hb h
      rw [hr,←ha]
      congr
      case e_a =>
      rw [← Nat.cast_inj (R := ℤ), Int.natAbs_of_nonneg hx, ←hb]
      linarith
    _ <~_∼ _ := by
      apply hoare.while_
      calc
        _ <~_∼ _ := by apply hoare.let_
        _ <~_∼ _ := by apply hoare.let_
        _ ⊇ _ := by
          simp [inv, Exp.sem, State.update]
          intro σ hx hr ha hb h1
          rw [hr,ha,hb]
          simp
          constructor
          case left =>
            linarith
          case right =>
            rw [←Int.pow_succ]
            congr
            case e_a =>
            rw [← Nat.cast_inj (R := ℤ)]
            push_cast
            have h: 0 ≤ σ "x" + 1 := by linarith
            rw [abs_of_nonneg hx, abs_of_nonneg h]
    _ <~_∼ _  := by apply hoare.let_
    _ <~_∼ _  := by apply hoare.let_
    _ ⊇ _ := by simp [State.update, Exp.sem, inv]

theorem power.correct (A B: ℕ) (σ σ': State)
  : σ "a" = A → σ "b" = B →
    power.sem σ σ' →
    σ' "r" = A^B
  := by
  intro ha hb
  apply hoare.correctness (power.hoareTriple A B)
  simp [ha,hb]

end Hoare_example_power


/-
  __Exercise__: (long)
  Define a factorial program and prove it correct using Hoare triples.
  Use `Finset.prod` (`∏ x ∈ s, f x`) for finite products. The notation is
  similar to that for finite sums (`∑ x ∈ s, f x`).
  Import `Mathlib.Algebra.BigOperators.Group.Finset.Defs` to use that.

  You can leave the "arithmetical" parts of the proof as `sorry`s.
  Or, for an additional challenge, solve them.
-/

/-
  __Exercise__: (long)
  Add more complex guards to commands. Define a language of boolean
  expressions. Adapt the semantics and the HAore triples accordingly.
-/
end Correctness_of_imperative_programs
