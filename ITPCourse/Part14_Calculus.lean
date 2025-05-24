-- import Mathlib.Data.Real.Basic
-- import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.RealVectorSpace

section Arithmetics
-- TODO some basic arith formula manipulations
end Arithmetics

section Continuity
/-
  Let's prove that a few basic functions are continuous.

  We start from a line `λ x => α*x + β`.

  Of course, its continuity can be solved with an automated tactic:
-/
example (α β: ℝ) : Continuous (λ x => α*x + β)
  := by continuity

/-
  Let's ignore the automation, and write an actual proof.

  Here we exploit several lemmas from the library. Remember you can search
  for them in several ways.
-/
theorem line_cont (α β: ℝ) : Continuous (λ x => α*x + β)
  := by
  -- This lemma provides the usual "ε and δ" criterion for continuity.
  apply Metric.continuous_iff.mpr
  intro x ε εpos
  by_cases α = 0
  case pos αzero =>
    subst α
    exists 1
    simp
    intro a h
    exact εpos
  case neg αnonzero =>
    exists (ε / |α|)
    constructor
    . apply div_pos εpos
      exact abs_pos.mpr αnonzero
    . intro y h
      simp [ dist ] at *
      conv =>
        left
        conv =>
          arg 1
          rw [ ← mul_sub_left_distrib ]
        rw [ abs_mul ]
      calc
      _ = |y-x| * |α|     := mul_comm _ _
      _ < (ε / |α|) * |α| := by gcongr
      _ ≤ ε               := by simp [αnonzero]
/-
  Above, `gcongr` takes a goal of the form
    `f x y z < f x' y' z'`
  and tries to reduce it to some properties of the arguments
    `x < x'`, `y < y'`, , `z < z'`
  provided `f` is monotonic.
  It works on `<` but also on other relations such as `≤`, `=`, … .
  It also tries to close simple subgoals.
-/


/-
  We now prove that the sum of two continuous functions is continuous.
  (Again, without relying on the `continuity` tactic)

  In Lean, `+` uses a type class so it works on all numeric types. It also
  works on functions: `f + g` stands for `λ x => f x + g x`.
-/
theorem add_cont
  (f g: ℝ → ℝ)
  (f_cont: Continuous f)
  (g_cont: Continuous g)
: Continuous (f + g)
  := by
  apply Metric.continuous_iff.mpr
  intro x ε εpos
  have ⟨ δf , ⟨ δf_pos , h_f ⟩ ⟩
    := Metric.continuous_iff.mp f_cont x (ε / 2) (half_pos εpos)
  have ⟨ δg , ⟨ δg_pos , h_g ⟩ ⟩
    := Metric.continuous_iff.mp g_cont x (ε / 2) (half_pos εpos)
  let δ := min δf δg
  exists δ
  constructor
  . positivity
  . intro a a_dist
    have h_f_a := h_f a (by
      calc
      _ < δ  := a_dist
      _ ≤ δf := min_le_left _ _ )
    have h_g_a := h_g a (by
      calc
      _ < δ  := a_dist
      _ ≤ δg := min_le_right _ _ )
    simp [ dist ]
    convert_to (|(f a - f x) + (g a - g x)| < ε )
    . congr
      linarith
    . calc
      _ ≤ |f a - f x| + |g a - g x| := by exact abs_add_le _ _
      _ < ε := by simp [ dist ] at h_f_a h_g_a ; linarith

/-
  Another simple result. We exploit that the composition of continuous
  functions is continuous.
-/
theorem neg_cont (f: ℝ → ℝ) (f_cont: Continuous f)
  : Continuous (-f)
  := by
  convert_to Continuous ((λ x => (-1)*x + 0) ∘ f)
  . funext x
    simp
  . apply Continuous.comp
    case hg =>
      exact line_cont (-1) 0
    case hf =>
      exact f_cont

/-
  __Exercise__: Complete this proof.
-/
theorem sub_cont
  (f g: ℝ → ℝ)
  (f_cont: Continuous f)
  (g_cont: Continuous g)
  : Continuous (f - g)
  := sorry

end Continuity
