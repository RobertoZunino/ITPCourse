import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import ITPCourse.Part13_Arithmetic

open Topology -- This enables the 𝓝 notation for neighborhoods

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

  Asymptotics (limits, Landau's little-o notation, …) is defined in terms of
  _filters_: these are families of sets that model "closedness" to a value.
  For instance the set of all neighborhoods of `x`, written `𝓝 x`, is a
  filter.

  Differentiability is also defined in very general terms, involving the
  Fréchet derivative, neighborhoods, filters, little-o notation, and more.
  Again, a few theorems from the library must be used to rephrase
  differentiability in more usual terms.

  Being very general is a common trend in the Lean libraries, which strive
  not to repeat the same proof in different contexts. This is accomplished
  by proving the most general statement and then add the common cases as
  corollaries.
-/
end General_note

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
    `x < x'`, `y < y'`, `z < z'`
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

section Asymptotics

section Filters
/-
  We start with some reasoning on _filters_. Filters are families of sets
  modelling "closedness" to something, and appear in many places when
  working with calculus (limits, little-o notation, …).

  Here are a few examples of filters and what they represent:
  - `𝓝 x` being close or even equal to `x` (neighborhood)
  - `𝓝[≠] x` being close but not equal to `x` (punctured neighborhood)
  - `𝓝[s] x` being close to `x` and inside set `s`
  - `Filter.atTop` diverging towards `+∞`
  - `Filter.atBot` diverging towards `-∞`

  Note that `𝓝[≠] x` is defined as `𝓝[{x}ᶜ] x`:
-/
example (x: Real)
  : 𝓝[≠] x = 𝓝[{x}ᶜ] x
  := rfl
/-
  Technically, a filter `F` is a family of sets such that
  - the whole real line belongs to `F`
  - if `a,b ∈ F` then `a ∩ b ∈ F`
  - if `a ∈ F` and `a ⊆ b` then `b ∈ F`

  You can verify that the families of neighborhoods mentioned above all
  satisfy these properties. (Note that `𝓝[s] x` is defined as the family of
  supersets of `s ∩ a` for some `a ∈ 𝓝 x`.)

  In practice, a filter is commonly used to state that a property `P x`
  holds "eventually", i.e. for all `x` "close enough according to the
  filter".

  For instance, the following proves "all `x` close enough to `0` are less
  than `1`"
-/
example
  : ∀ᶠ x: Real in 𝓝 0 , x < 1
  := by
  apply eventually_lt_nhds
  simp only [zero_lt_one]
/-
  More formally, `P` is true eventually on filter `F` iff
    `{ x | P x } ∈ F`
-/

/-
  As an exercise, we prove equality between the following filters.
  - `𝓝[≠] 0`, representing being close but not equal to `0`
  - `𝓝[ Set.Ioo (-ε) ε \ {0} ] 0` representing being close to `0` and inside
    the open real interval `(-ε, ε)` with the `0` removed

  Intuition suggests these are the same: being "close" to `0` according to
  one filter clearly implies also being "close" according to the other
  filter.

  We establish equality by proving the double inequality between filters
    `F₁ ≤ F₂ ∧ F₂ ≤ F₁`
  where `F₁ ≤ F₂` models the intuitive relation "if we are `F₁`-close, then
  we are also `F₂`-close".
  (Note that this means that if a property `P` holds when we are `F₂`-close
  enough, then `P` also holds when we are on the points `F₁`-close enough.
  It might be counterintuitive at first that the direction is reversed.)

  We start by proving the first inequality:
-/
theorem nhdsNE_le_nhdsWithinIoo
  (ε: Real)
  (ε_pos: ε > 0)
  : 𝓝[≠] 0 ≤ 𝓝[ Set.Ioo (-ε) ε \ {0} ] 0
  := by
  apply nhdsWithin_le_iff.mpr
  simp [ nhdsWithin , min , Filter.instInf ]
  exists Set.Ioo (-ε) ε
  constructor
  case left =>
    apply Ioo_mem_nhds
    case ha =>
      linarith
    case hb =>
      exact ε_pos
  case right =>
    exists {0}ᶜ

/-
  The equality of filters then follows by antisymmetry and a library lemma.
-/
theorem nhdsNE_eq_nhdsWithinIoo
  (ε: Real)
  (ε_pos: ε > 0)
  : 𝓝[≠] 0 = 𝓝[ Set.Ioo (-ε) ε \ {0} ] 0
  := by
  apply le_antisymm
  case a =>
    exact nhdsNE_le_nhdsWithinIoo ε ε_pos
  case a =>
    apply nhdsWithin_mono
    simp

/-
  Here is an example of strict inequality between filters: approaching `0`
  from the right implies approaching `0`, but not vice versa.
-/
example
  : 𝓝[ Set.Ioi 0 ] 0 < 𝓝[≠] (0: Real)
  := by
  apply lt_of_le_not_le
  case hab =>
    apply nhdsWithin_mono
    simp only [Set.subset_compl_singleton_iff, Set.mem_Ioi,
      lt_self_iff_false, not_false_eq_true]
  case hba =>
    apply Filter.not_le.mpr
    exists Set.Ioi 0
    constructor
    case left =>
      exact self_mem_nhdsWithin
    case right =>
      intro h
      rw [ nhdsWithin ] at h
      simp [ min ] at h
      replace ⟨ a , h_a , b , h1 , h2 ⟩ := h
      clear h
      have ⟨ ε , ε_pos , h_ball ⟩  := Metric.mem_nhds_iff.mp h_a
      have h3: -ε/2 ∈ a ∩ b
        := by
        constructor
        case left =>
          apply h_ball
          have ε_abs: |ε| = ε := abs_of_pos ε_pos
          simp only [Metric.mem_ball, dist_zero_right, norm_div, norm_neg,
            Real.norm_eq_abs, Real.norm_ofNat, gt_iff_lt]
          rw [ε_abs]
          simp only [Nat.abs_ofNat, half_lt_self_iff, ε_pos]
        case right =>
          apply h1
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
            div_eq_zero_iff, neg_eq_zero, OfNat.ofNat_ne_zero, or_false]
          linarith
      rw [ ←h2 ] at h3
      simp at h3
      linarith

end Filters

section Limits
/-
  We now study a limit, proving that the function
    `λ x => 1 / |x|`
  tends to `+∞` when `x` approaches `0`.

  Since we don't want to evaluate the function at `0`, we chose `x` to be
  close to the filter `𝓝[≠] 0` (and not just `𝓝 0`). The result the function
  tends to is instead `+∞`, i.e. the filter `Filter.atTop`.

  `Filter.Tendsto` is the the relation for limits:
-/
theorem abs_diverges₁
  : Filter.Tendsto (λ x: Real => 1 / |x|) (𝓝[≠] 0) Filter.atTop
  := by
  -- We reduce to a set property: for all `s` close to `+∞`, we have to find
  -- a close enough argument to `0` so that the result is in `s`.
  apply Filter.tendsto_iff_forall_eventually_mem.mpr
  intro s h1
  -- The set `s` contains all the points larger than a given `a`.
  simp only [Filter.mem_atTop_sets, ge_iff_le] at h1
  replace ⟨ a , h1 ⟩ := h1
  -- We are given `a`, so we compute a radius and a neighborhood of `0` in
  -- terms of it: `Set.Ioo (-r) r \ {0}`.
  let r := 1 / (|a|+1)
  have r_pos: r > 0 := by positivity
  apply Filter.eventually_of_mem (U := Set.Ioo (-r) r \ {0})
  case hU =>
    -- We prove we did choose a neighborhood
    apply diff_mem_nhdsWithin_compl _ {0}
    apply Ioo_mem_nhds <;> linarith
  case h =>
    -- We prove the result is in `s` if `x` is in our neighborhood
    intro x h_x
    simp at h_x
    replace ⟨ ⟨ x_gt , x_lt ⟩ , x_nonzero ⟩  := h_x
    clear h_x
    apply h1
    calc a
    _ ≤ |a| := le_abs_self a
    _ ≤ |a| + 1 := by simp only [le_add_iff_nonneg_right, zero_le_one]
    _ ≤ 1 / r   := by simp only [r, one_div, div_inv_eq_mul, one_mul,
                        le_refl]
    _ = 1 / |r| := by rw [ abs_eq_self.mpr ] ; positivity
    _ ≤ _
      := by
      ring_nf
      have abs_x_pos: 0 < |x| := by positivity
      have abs_r_pos: 0 < |r| := by positivity
      apply (inv_le_inv₀ abs_r_pos abs_x_pos).mpr
      apply abs_le_abs
      . linarith
      . linarith

/-
  An alternative proof, involving our lemma `nhdsNE_eq_nhdsWithinIoo`.
-/
theorem abs_diverges₂
  : Filter.Tendsto (λ x: Real => 1 / |x|) (𝓝[≠] 0) Filter.atTop
  := by
  apply Filter.tendsto_iff_forall_eventually_mem.mpr
  intro s h1
  simp only [Filter.mem_atTop_sets, ge_iff_le] at h1
  replace ⟨ a , h1 ⟩ := h1
  rw [ nhdsNE_eq_nhdsWithinIoo (1/(|a|+1)) (by positivity) ]
  apply eventually_nhdsWithin_of_forall
  case h =>
    intro y h_y
    apply h1
    simp at h_y
    have ⟨ ⟨ y_gt , y_lt ⟩  , y_nonzero ⟩ := h_y
    clear h_y
    have y_pos: |y| > 0 := by positivity
    calc a
    _ ≤ |a| := by exact le_abs_self a
    _ ≤ _
      := by
      have y_bound: |y| ≤ (|a|+1)⁻¹
        := by
        apply abs_le.mpr
        constructor
        case left =>
          linarith
        case right =>
          linarith
      apply (le_div_iff₀ y_pos).mpr
      calc |a| * |y|
      _ ≤ |a| * (|a| + 1)⁻¹ := by gcongr
      _ ≤ _
        := by
        change (|a| / (|a| + 1) ≤ _)
        apply (le_div_iff₀ _).mp
        . simp only [div_inv_eq_mul, one_mul, le_add_iff_nonneg_right,
            zero_le_one]
        . positivity

/-
  Yet another proof, involving little-o notation, norms, beyond our lemma
  `nhdsNE_eq_nhdsWithinIoo`.
-/
theorem abs_diverges₃
  : Filter.Tendsto (λ x: Real => 1 / |x|) (𝓝[≠] 0) Filter.atTop
  := by
  -- We want to introduce the norm to exploit a library theorem
  conv =>
    arg 1
    intro x
    tactic =>
      change (_ = Norm.norm (1 / |x|))
      simp only [one_div, norm_inv, Real.norm_eq_abs, abs_abs]
  -- We move to little-o notation
  apply (Asymptotics.isLittleO_one_left_iff Real).mp
  apply Asymptotics.IsLittleO.of_bound
  case a =>
  intro c c_pos
  simp only [norm_one, one_div, norm_inv, Real.norm_eq_abs, abs_abs]
  rw [ nhdsNE_eq_nhdsWithinIoo c c_pos ]
  apply eventually_nhdsWithin_of_forall
  simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, and_imp]
  intro x x_gt x_lt x_nonzero
  calc
  _ = c * c⁻¹
    := by
    symm ; apply mul_inv_cancel₀ ; exact Ne.symm (ne_of_lt c_pos)
  _ ≤ c * |x|⁻¹
    := by gcongr ; apply abs_le.mpr ; constructor <;> linarith

end Limits

section LittleO
/-
  We now prove that the exponential function
    `λ x => exp (- 1 / |x|)`
  approaches `0` faster than the square function
    `λ x => x^2`
  when the argument approaches `0`.
-/
theorem exp_is_faster_than_square
  : (λ x: Real => Real.exp (- 1 / |x|)) =o[𝓝[≠] 0] λ x: Real => x^2
  := by
  have h1: (λ x => Real.exp (-1 * x)) =o[Filter.atTop] λ x => x ^ (-2: Real)
    := isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by positivity) (-2)

  have h2:
    ((λ x => Real.exp (-1 * x)) ∘ λ x => 1 / |x|)
    =o[𝓝[≠] 0]
    ((λ x => x ^ (-2: Real)) ∘ λ x => 1 / |x|)
    :=
    Asymptotics.IsLittleO.comp_tendsto
      h1
      (k := λ x: Real => 1 / |x|) (l' := 𝓝[≠] 0) (l := Filter.atTop)
      abs_diverges₁

  simp only [neg_mul, one_mul] at h2
  have h6 : ∀ x: Real, (1 / |x|) ^ (- 2: Real) = x^2
    := by
    intro x
    simp_all only [neg_mul, one_mul, one_div, inv_nonneg, abs_nonneg,
      Real.rpow_neg, Real.rpow_two, inv_pow, sq_abs, inv_inv]

  conv at h2 =>
    right
    intro x
    dsimp
    rw [h6]

  ring_nf at h2
  ring_nf
  exact h2

/-
  Here is another example of the little-o notation.
-/
example
  : (λ x: Real => x^2 + Real.exp (- 1/x^2))
    =o[𝓝[≠] 0]
    (λ x: Real => x)
  := by
  apply Asymptotics.IsLittleO.add
  case h₁ =>
    conv =>
      args
      . rfl
      . intro x ; tactic => change (_ = x*x) ; ring
      . intro x ; tactic => change (_ = 1*x) ; ring
    apply Asymptotics.IsLittleO.mul_isBigO
    . apply (Asymptotics.isLittleO_one_iff ℝ).mpr
      apply tendsto_nhdsWithin_of_tendsto_nhds
      exact λ ⦃U⦄ a => a
    . exact Asymptotics.isBigO_refl _ _
  case h₂ =>
    calc
      _ =O[𝓝[≠] 0] (λ x: Real => Real.exp (-1 / |x|))
        := by
        apply Real.isBigO_exp_comp_exp_comp.mpr
        apply Filter.isBoundedUnder_of_eventually_le (a := 0)
        dsimp
        have h_filter : 𝓝[≠] (0: Real) ≤ 𝓝[ Set.Ioo (-1) 1 \ {0} ] 0
          := nhdsNE_le_nhdsWithinIoo 1 (by positivity)
        apply Filter.Eventually.filter_mono h_filter
        apply eventually_nhdsWithin_of_forall
        simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff,
          and_imp]
        intro x x_gt x_lt x_nonzero
        simp only [tsub_le_iff_right, zero_add]
        apply (div_le_div_iff₀ _ _).mpr
        . simp only [neg_mul, one_mul, neg_le_neg_iff]
          apply le_abs.mpr
          cases le_total x 0
          case inl x_npos =>
            right
            convert_to (x*x ≤ _)
            . ring
            have x_neg: x < 0 := lt_of_le_of_ne x_npos x_nonzero
            have mx_pos : -x > 0 := by simp [x_neg]
            convert_to ((-x)*(-x) ≤ -x)
            . simp only [mul_neg, neg_mul, neg_neg]

            apply (mul_le_iff_le_one_left mx_pos).mpr
            linarith
          case inr x_nneg =>
            left
            convert_to (x*x ≤ _)
            . ring
            have x_pos: x > 0 := by positivity
            simp [ x_pos ]
            linarith
        . exact pow_two_pos_of_ne_zero x_nonzero
        . exact abs_pos.mpr x_nonzero
      _ =o[𝓝[≠] 0] λ x => x^2
        := exp_is_faster_than_square
      _ =o[𝓝[≠] 0] λ x => x
        := by
        conv =>
          right
          intro x
          rw [← pow_one x]

        have h_filter: 𝓝[≠] (0: Real) ≤ 𝓝 0 := nhdsWithin_le_nhds
        apply Asymptotics.IsLittleO.mono _ h_filter
        apply Asymptotics.isLittleO_pow_pow (n:=2) (m:=1)
        decide

end LittleO

end Asymptotics

section Derivatives
/-
  We start by proving that the derivative of `x^2` is `2*x`.

  Of course, we can exploit the library theorems and make this almost
  trivial.
-/
theorem deriv_x_squared₁
  : deriv (λ x: Real => x^2) = λ x => 2*x
  := by
  -- We reduce to `HasDerivAt`
  apply deriv_eq
  -- Name the point at which we are taking the derivative
  intro a
  -- Recall the derivative of x
  have d_id: HasDerivAt (λ x => x) 1 a
    := hasDerivAt_id' a
  -- Deduce the derivative of the product x*x
  have d_square: HasDerivAt (λ x => x*x) (1*a + a*1) a
    := HasDerivAt.mul d_id d_id
  ring_nf at d_square
  ring_nf
  exact d_square

/-
  We prove the same result again, but without relying on the theorem for the
  derivative of the product.
-/
theorem deriv_x_squared₂
  : deriv (λ x: Real => x^2) = λ x => 2*x
  := by
  -- We reduce to `HasDerivAt`
  apply deriv_eq
  intro x
  -- We reduce to Landau's little-o notation
  -- Here `𝓝 x` is a filter denoting the neighborhoods of `x`
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
theorem deriv_x_cubed
  : deriv (λ x: Real => x^3) = λ x => 3*x^2
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
          _ ≤ |3*x|+|h|  := by simp only [abs_add]
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

section Integrals
/-
  Below we compute the integral of `sin` over the interval `[0,π]`.

  We exploit several library results, including the fundamental theorem of
  calculus. (We do not attempt to prove the result by relying only on the
  definitions.)

  Note that the Lean library also has much more complex forms of integrals,
  involving arbitrary measures and the associated measurable functions and
  measurable sets.
-/
example:
  ∫ (x: ℝ) in 0..Real.pi, Real.sin x = 2
  := by
  calc
    _ = ∫ (x: ℝ) in 0..Real.pi, - deriv Real.cos x
      := by
      congr
      funext x
      rw [Real.deriv_cos]
      ring
    _ = - ∫ (x: ℝ) in 0..Real.pi, deriv Real.cos x
      := by
      rw [intervalIntegral.integral_neg]
    _ = - (Real.cos Real.pi - Real.cos 0)
      := by
      -- The fundamental theorem of calculus
      rw [intervalIntegral.integral_deriv_eq_sub]
      case hderiv =>
        intro x x_in
        exact Real.differentiableAt_cos
      case hint =>
        apply Continuous.intervalIntegrable _
        continuity
    _ = 2
      := by
      simp only [Real.cos_pi, Real.cos_zero, neg_sub, sub_neg_eq_add]
      ring

end Integrals

section Recap_exercises
/-
  __Exercise__: Prove the following.
  You might need the following results from the library:
  `Filter.tendsto_atTop`, `Filter.eventually_atTop`.
-/
example
  (a b: ℕ → ℝ)
  (b_mon: Monotone b)
  (b_dominates_a: ∀ n, ∃ m, a n ≤ b m)
  : Filter.Tendsto a Filter.atTop Filter.atTop
  → Filter.Tendsto b Filter.atTop Filter.atTop
  := by
  sorry

end Recap_exercises
