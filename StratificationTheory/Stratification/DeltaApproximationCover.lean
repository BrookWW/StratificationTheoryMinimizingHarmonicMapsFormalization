module

public import StratificationTheory.Frozen.FlatCover
public import StratificationTheory.Frozen.DeltaApproximation

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped Topology
namespace StratificationTheory

/-- The original whole covering joint uses the literal source approximation
predicate, with the same exponent function and all original set quantifiers. -/
theorem deltaApproximation_hausdorffMeasure_zero {n : ℕ} (j : ℕ) (hj : j ≤ n) :
    ∃ β : PositiveRadius → ℝ,
      (∀ δ : PositiveRadius, 0 < β δ) ∧
      Tendsto β atBot (𝓝 (0 : ℝ)) ∧
      ∀ (δ : PositiveRadius) (A : Set (Domain n)),
        HasDeltaApproximation j δ A → μH[(j : ℝ) + β δ] A = 0 := by
  obtain ⟨β, hPositive, hLimit, hNull⟩ := flatApproximation_hausdorffMeasure_zero j hj
  refine ⟨β, hPositive, hLimit, ?_⟩
  intro δ A hApprox
  exact hNull δ A hApprox

end StratificationTheory
