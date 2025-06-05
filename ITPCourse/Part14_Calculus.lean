-- import Mathlib.Data.Real.Basic
-- import Mathlib.Topology.Basic
-- import Mathlib.Analysis.Calculus.Deriv.Slope
-- import Mathlib.Analysis.Asymptotics.Defs
-- import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

section General_note
/-
  Below, we will see a few proofs for a few familiar properties like
  continuity and differentiability, which are defined in the Lean libraries.

  Note, however, that the definitions found in the libraries might be more
  general than the ones you expect. Much more general.

  Continutity for a basic function `f: Real → Real`, for instance, is
  defined in terms of _topology_. A few theorems from the library must then
  be used to restate continuity in terms of distance in a _metric space_,
  and from there simplify the goal so to see the usual `ε` and `δ` property.

  Differentiability is also defined in very general terms, involving the
  Fréchet derivative, neighborhoods, filters, Landau's little-o notation,
  and more. Again, a few theorems from the library must be used to rephrase
  differentiability in more usual terms.

  Being very general is a common trend in the Lean libraries, which strive
  not to repeat the same proof in different contexts. This is accomplished
  by proving the most general statement and then add the common cases as
  corollaries.
-/
end General_note

section Arithmetics
-- TODO some basic arith formula manipulations

/-
  __Exercise__: Prove the following.
-/
theorem forall_x_y_h
  (P: Real → Real → Prop)
  : (∀ x y, P x y) ↔ (∀ x h, P x (x+h))
  := by
  sorry

theorem forall_x_y_h_left
  (P: Real → Real → Prop)
  : (∀ x h, P x (x+h)) → (∀ x y, P x y)
  := (forall_x_y_h P).mpr

/-
  __Exercise__: Prove the following.
-/
theorem forall_ε (a b: Real)
  : (a ≤ b) ↔ (∀ ε>0, a ≤ b + ε)
  := by
  sorry

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

section Derivatives
/-
  We start by proving that the derivative of `x^2` is `2*x`.

  Of course, we can exploit the library theorems and make this almost
  trivial.
-/
theorem deriv_x_squared₁:
  deriv (λ x: Real => x^2) = λ x => 2*x
  := by
  -- We reduce to `HasDerivAt`
  apply deriv_eq
  -- Name the point at which we are taking the derivative
  intro a
  -- Recall the derivative of x
  have d_id : HasDerivAt (λ x => x) 1 a
    := hasDerivAt_id' a
  -- Deduce the derivative of the product x*x
  have d_square : HasDerivAt (λ x => x*x) (1*a + a*1) a
    := HasDerivAt.mul d_id d_id
  ring_nf at d_square
  ring_nf
  exact d_square

/-
  We prove the same result again, but without relying on the theorem for the
  derivative of the product.
-/
theorem deriv_x_squared₂:
  deriv (λ x: Real => x^2) = λ x => 2*x
  := by
  -- We reduce to `HasDerivAt`
  apply deriv_eq
  intro x
  -- We reduce to Landau's little-o notation
  -- Here `nhds x` are the neighborhoods of `x`
  apply hasDerivAt_iff_isLittleO.mpr
  case h =>
  -- We reduce to "for all close enough" quantification `∀ᶠ`
  apply Asymptotics.IsLittleO.of_bound
  intro c c_pos
  -- We finally reduce to norms
  apply Metric.eventually_nhds_iff.mpr
  case a =>
  -- We choose `x` and `y` to have distance `< c`
  exists c
  constructor
  case left =>
    positivity
  case right =>
    intro y h_dist
    simp_all [ dist ]
    calc
      _ = |(y - x)^2|          := by ring
      _ = |(y - x) * (y - x)|  := by ring
      _ = |y - x| * |y - x|    := abs_mul _ _
      _ ≤ c * |y - x|          := by gcongr


/-
  Proving that the derivative of x^3 is 3*x^2 in an explicit way is a bit
  more challenging.
-/
theorem deriv_x_cubed:
  deriv (λ x: Real => x^3) = λ x => 3*x^2
  := by
  apply deriv_eq
  intro x
  apply hasDerivAt_iff_isLittleO.mpr
  case h =>
  apply Asymptotics.IsLittleO.of_bound
  intro c c_pos
  apply Metric.eventually_nhds_iff.mpr
  case a =>
  -- We pick the distance between `x` and `y` to be smaller than the
  -- quantities we will meet later on.
  exists min 1 (c / (3*|x|+1))
  constructor
  case left =>
    positivity
  case right =>
    intro y h_dist
    simp_all [ dist ]
    revert h_dist x y
    apply forall_x_y_h_left
    intro x h h_dist
    simp at h_dist
    have ⟨ h1, h2 ⟩ := h_dist
    clear h_dist
    ring_nf
    calc
      _ = |x * h ^ 2 * 3 + h ^ 3|  := by ring
      _ = |(3*x + h)*h^2|     := by ring
      _ = |3*x+h| * |h^2|     := abs_mul _ _
      _ ≤ |3*x+h| * |h|^2     := by simp only [abs_pow, sq_abs, le_refl]
      _ = |3*x+h| * |h| * |h| := by ring
      _ ≤ (3*|x|+1) * |h| * |h| := by
        gcongr
        calc
          _ ≤ |3*x|+|h|  := by simp [abs_add]
          _ = 3*|x|+|h|  := by simp [abs_mul]
          _ ≤ 3*|x|+1    := by gcongr
      _ ≤ c * |h|        := by
        gcongr
        calc
          _ ≤ (3 * |x| + 1) * (c / (3*|x| + 1))  := by gcongr
          _ = c   := by
            apply mul_div_cancel₀ c
            -- Ensure we did not divide by zero
            positivity

end Derivatives
