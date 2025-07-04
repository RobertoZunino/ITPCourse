
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-
  This file describes some "standard" kinds of questions you are likely to
  find at the final exam.

  Exam questions can be divided in two categories:

  - _On-paper_ exercises: tasks to be solved without the help of a computer.
    These would often be trivial to answer by querying Lean, but you must be
    able to show your understanding of the underlying theory by solving them
    on paper.
    The complexity of these questions is tuned to compensate for the lack of
    software help (InfoView, tactics, `exact?`, Loogle, …).
    Usually, the answer must use _terms_, not _tactics_.
    Minor syntactical mistakes are forgiven, as long as there is no
    ambiguity. The point is to test your understanding of the fundamentals,
    not your memory of minor details.

  - _On-Lean_ exercises: tasks to be solved with Lean, on a computer.
    Lean provides an arsenal of tools to help you, including tactics and
    library theorems. Further, Lean automatically type-checks the answer,
    providing instant feedback in the InfoView window.
    Mastering the available tools is paramount to success.
    Answers must be precise here, lest they be rejected by Lean.
    The complexity of these questions is tuned considering the weapons at
    your disposal.
-/

section Main_rule
/-
  When solving a task "on Lean", you can use tactics and library theorems,
  but **only as long as they do not trivialize the task**.

  For instance, using `tauto` to instantly solve a whole exercise is
  forbidden. On the other hand, if you already wrote a non-trivial proof
  draft with a few `sorry` inside, and you could close one of these with
  `tauto` (or `simp`, or …), that is allowed.
-/

/-
  For instance, the following one-liners are _not_ allowed.
-/
example (a b: ℕ): a+b = b+a
  := by ring
example (p q: Prop): (p → q) → (p → (p ∧ q))
  := by tauto
/-
  In the above exercises, the point is obviously to produce an explicit
  proof, such as one by induction or by working with introduction and
  elimination terms or tactics. By contrast, if the same propositions
  arose as a subgoal of a significantly larger task, using any automation
  is allowed.
-/
end Main_rule

section Find_the_type
/-
  Given a Lean context and term, find its type.
    `a₁ : α₁ , … ⊢ t : ?`

  Usually, this is to be solved on paper, since on Lean it would be too
  simple.
-/

/-
  A very simple example of this kind of task:
  (expect more complex ones at the exam)
-/
example := λ τ σ (f: τ → σ) (x: τ) => (x, f x)
/-
  Lean suggests the universe-polymorphic type
    `(τ: Type u_1) → (σ: Type u_2) → (τ → σ) → τ → τ × σ`
  The simpler type
    `(τ: Type) → (σ : Type) → (τ → σ) → τ → τ × σ`
  would also be a perfect answer, like the following alternative forms:
    `(τ σ: Type) → (τ → σ) → τ → τ × σ`
    `∀ (τ σ: Type), (τ → σ) → τ → τ × σ`
-/

/-
  Another (but related) on-paper exercise could involve
    `λ … (f: …) (x: …) => (x, f x)`
  and ask you to fill the `…` so to make the above term type-check.
  You can then be asked to find the type of the resulting term.
-/
end Find_the_type

section Find_the_term
/-
  Given a Lean context and type, find a term with that type.
    `a₁ : α₁ , … ⊢ ? : τ`

  You might be asked to solve this on paper or on Lean, depending on the
  complexity.

  When using Lean, the use of tactics can be forbidden or allowed on a
  case-by-case fashion.
-/

/-
  A very simple example of this kind of task:
  (expect more complex ones at the exam)
-/
example
  (τ γ: Type) (σ: ℕ → Type)
  (f: τ → (n: ℕ) → σ n)
  (g: σ 1 × σ 2 → γ)
  : τ → γ
  := sorry
/-
  You could be asked to solve the above using both a term-style and a
  tactics-style solution.
-/
end Find_the_term

section Prove_a_statement
/-
  Given some hypotheses, prove a given proposition.

  From a theoretical point of view, this is essentially the same task as
  "find the term", thanks to Curry-Howard, but it can feel different in
  practice.

  You might be asked to solve this on paper or on Lean, depending on the
  complexity.

  When using Lean, you might be suggested to use specific tactics, or
  theorems from the library. Alternatively, some tactics (like `simp` and
  `tauto`) can be forbidden or constrained, depending on the case.
-/

/-
  A very simple example of this kind of task:
  (expect more complex ones at the exam)
-/
example
  (P Q: ℕ → Prop)
  : (∀ n, P n ∧ Q n) ↔ (∀ n, P n) ∧ (∀ n, Q n)
  := sorry

/-
  Here is another example.

  Suggested tactics and theorems:
    `ring_nf`, `¢alc`, `gcongr`, `Nat.zero_le`
  (Other tactics and theorems are not forbidden, unless they make the task
  trivial.)
-/
example
  : ∀ n: ℕ, n ≤ n*n
  := sorry
/-
  An acceptable solution:
-/
example
  : ∀ n: ℕ, n ≤ n*n
  := by
  intro n
  induction n
  case zero =>
    exact Nat.zero_le _
  case succ n' ih =>
    ring_nf
    calc 1+n'
    _ = 1+n'+0 := by rfl
    _ ≤ 1+n'+(n'+n'^2) := by gcongr ; exact Nat.zero_le _
    _ = _ := by ring_nf
/-
  A *not* acceptable solution:
-/
example
  : ∀ n: ℕ, n ≤ n*n
  := by
  intro n
  exact Nat.le_mul_self n  -- Trivialized!

end Prove_a_statement

section Clarify_how_pattern_matching_works
/-
  Given a `match … with` expression, modify it so to expose the underlying
  details that make Lean accept it.

  Checklist:
  - Make the match `motive` explicit.
  - Add additional matched expressions, if needed.
    For instance, change `match c with` into `match a,b,c with` if the
    motive requires that. Adapt the patterns according to these extra terms.
  - Remove any wildcard `_` in patterns.
    This might involve replacing them with fresh variables or inaccessible
    patterns (`.(term)`).
  - Ensure the new match expression is accepted by Lean.

  Note: the provided original match expression might intentionally contain
  a few type errors for you to fix.

  You might be asked to solve this on paper or on Lean, depending on the
  complexity.
-/

/-
  A very simple example of this kind of task:
  (expect more complex ones at the exam)
-/
inductive T (f: ℕ → ℕ): ℕ → ℕ → Type
| k₁: ∀ n, T f n n
| k₂: ∀ n, T f n (f n)

example
  (f: ℕ → ℕ)
  (a: ℕ)
  (t: T f a a)
  : String
  := sorry
  /- Fix and clarify this pattern matching
  match t with
  | .k₁ _ => "k₁"
  | .k₂ _ => "k₂"
  -/

-- Partial solution: (wildcards are still present)
example
  (f: ℕ → ℕ)
  (a: ℕ)
  (t: T f a a)
  : String
  := match
    (motive := (i j: ℕ) → T f i j → String)
    a , a , t with
  | _ , _ , .k₁ _ => "k₁"
  | _ , _ , .k₂ _ => "k₂"

-- Full solution: (alternative 1)
example
  (f: ℕ → ℕ)
  (a: ℕ)
  (t: T f a a)
  : String
  := match
    (motive := (i j: ℕ) → T f i j → String)
    a    , a      , t with
  | .(i) , .(i)   , .k₁ i => "k₁"
  | .(i) , .(f i) , .k₂ i => "k₂"

-- Full solution: (alternative 2)
example
  (f: ℕ → ℕ)
  (a: ℕ)
  (t: T f a a)
  : String
  := match
    (motive := (i j: ℕ) → T f i j → String)
    a , a      , t with
  | i , .(i)   , .k₁ .(i) => "k₁"
  | i , .(f i) , .k₂ .(i) => "k₂"

end Clarify_how_pattern_matching_works
