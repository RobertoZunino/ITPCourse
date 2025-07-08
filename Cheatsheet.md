# Lean 4 cheatsheet

Below you can find a summary of the syntax of the most common Lean 4 terms
and tactics.

Remember you can use `by` and `exists` to switch between the two styles as
needed.

| Formula | as thesis <br> (term-style) | as thesis <br> (tactic-style) | as hypothesis <br> (term-style) | as hypothesis <br> (tactic-style) |
|---|---|---|---|---|
| conjunction `p ∧ q` <br> product `τ × σ` <br> dependent sum `(t: τ) × σ t` <br> existential `∃ t, P t` | `⟨ … , … ⟩` | `constructor` <br> `apply And.intro _ _` <br> `use …` <br> `exists …` | `h.1`, `h.2` <br> `match h with \| ⟨ x , y ⟩ => …` | `have ⟨ x , y ⟩ := h` |
| `structure S` | `{ field₁ := … , … : S }` | `constructor` <br> `apply S.mk` | `h.field₁`, `h.1`, … | `have ⟨ x₁ , … ⟩ := h` |
| disjunction `p ∨ q`, sum `τ ⊕ σ` | `.inl …`, `.inr …` | `left`, `right` | `match h with \| .inl x => … \| .inr …` | `cases h` (followed by `case tag x₁ … => `) |
| implication `p → q` <br> function `τ → σ` <br> dependent product `(t: τ) → σ t` <br> universal `∀ t, P t` | `λ t => …` | `intro t` | `h …` | `apply h`, `have h2 := h …` |
| unit `Unit` <br> true `True` | `()`, `True.intro` | `trivial` | --- | --- |
| empty `Empty` <br> false `False` | --- | --- | `nomatch …` | `contradiction`, `apply False.elim` |
| `inductive T` | `T.cᵢ …` | apply `T.cᵢ` | `match h with \| .c₁ … => … \| …` <br> (possibly dependent, with multiple matched terms, and together with recursion) | `cases h`, `induction h` (followed by `case tag x₁ … => `) |

## More formulas

Remember that some constructs are defined in terms of others, so that can be
handled accordingly. For instance:

- Equivalence `p ↔ q` is defined as a structure with fields `mp: p → q` and
  `mpr: q → p`
- Negation `¬ p` is defined as `p → False`

## Equality

In term-style, we can work with equality exploiting the constructor
`Eq.refl` (to prove a thesis), and dependent pattern matching (to exploit an
hypothesis). Usually, this is not very convenient.

In tactic-style, we have a large array of tools at our disposal.

When we want to prove an equality thesis `a = b`, we can use:

- `rfl` when `b` is the same as `a`
- `symm` to apply symmetry
- `¢alc` to build a chain of equations
- `congr` / `gcongr` to remove the common part of the two expressions, and
  focus on the differences.

When we want to exploit an equality hypothesis `h: a = b`, we can use:

- `subst x` when `a` is a variable we want to replace with term `b`
- `rw [h]` to rewrite the current thesis (possibly after some `conv` to
  choose the rewriting point)
- `rw [ ←h1 , h2 , ←h3 ] at h4` to chain multiple rewritings, some of them
  backwards (`←`), to be performed on hypothesis `h4`

For numerical equations, you might want to try:

- `ring`, `ring_nf`
- `linarith`
- `simp +arith`, `simp_all`
- `repeat rw [add_assoc]` to associate all the additions in the same
  direction

## General tactics

A few more automatic tools:

- `exact?`, `apply?` suggest known lemmas
- `aesop` try some complex heuristics
- `tauto` solve propositional tautologies
- `simp` general simplification

Searching on [Loogle][loogle] is also very useful.

[loogle]: https://loogle.lean-lang.org/

## Beyond the basics

The above list of terms and tactics is _not_ meant to be exhaustive.

You can find more tactics by accessing the [Lean 4 Language Reference][leanRef].

[leanRef]:[https://lean-lang.org/doc/reference/latest/]