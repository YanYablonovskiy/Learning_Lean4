import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory Filter
#check Adapted
#check MeasureTheory.Adapted
#check NNReal
#check NNReal.toReal
#check Real.toNNReal

-- Define a Brownian motion as a stochastic process
structure BrownianMotion (Ω : Type*) [Preorder Ω] [E:MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (𝓕 : Filtration ℝ _) (B : ℝ → Ω → ℝ) where
  adapted : Adapted (m:=E) 𝓕 B
  continuous_paths : ∀ ω, Continuous (fun t ↦ B t ω)
  gaussian_increments : ∀ t s, t < s → μ.map (B s - B t) = ProbabilityTheory.gaussianReal 0 (s - t).toNNReal
  independent_increments : ∀ t₁ t₂ s₁ s₂, t₁ < t₂ → s₁ < s₂ → t₂ ≤ s₁ →
    IndepFun (B t₂ - B t₁) (B s₂ - B s₁) μ
  zero_start : ∀ ω, B 0 ω = 0

-- Example usage
variable (Ω : Type*) [MeasurableSpace Ω] [Preorder Ω]  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (𝓕 : Filtration ℝ _) (B : ℝ → Ω → ℝ)

-- Assume we have a Brownian motion
variable (Br:BrownianMotion Ω μ 𝓕 B)

-- Now we can use the properties of Brownian motion in proofs or computations
