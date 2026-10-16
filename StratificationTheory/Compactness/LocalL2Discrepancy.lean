module

public import HarmonicMaps.Analysis.VariableMollificationL2

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory.Compactness

/-- Actual L2 convergence on a region gives convergence of the original
squared discrepancy integral on every contained region. -/
theorem tendsto_integral_square_discrepancy_on_subset {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f : ℕ → α → E} {g : α → E} {K U : Set α}
    (hf : ∀ k, MemLp (f k) 2 (μ.restrict K)) (hg : MemLp g 2 (μ.restrict K))
    (hUK : U ⊆ K)
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2 (μ.restrict K)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in U, ‖f k x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hμ : μ.restrict U ≤ μ.restrict K := Measure.restrict_mono_set μ hUK
  have hL : ∀ k, MemLp (f k - g) 2 (μ.restrict U) :=
    fun k => ((hf k).sub hg).mono_measure hμ
  apply tendsto_integral_norm_sq_zero_of_eLpNorm_two hL
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hμ)

end StratificationTheory.Compactness
