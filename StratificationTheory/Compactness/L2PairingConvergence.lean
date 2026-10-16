module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

public section

open MeasureTheory Filter
open scoped Topology

namespace StratificationTheory.Compactness

private theorem L2_inner_toLp_eq_integral {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

/-- Strong L2 convergence preserves the integral pairing with every fixed
L2 test function on the same measure space. -/
theorem tendsto_integral_inner_of_L2_convergence {α E ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {l : Filter ι} {f : ι → α → E} {u v : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) l (𝓝 0)) :
    Tendsto (fun k => ∫ x, inner ℝ (f k x) (v x) ∂μ) l
      (𝓝 (∫ x, inner ℝ (u x) (v x) ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  have hp := hLp.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hv.toLp v))
  simpa only [L2_inner_toLp_eq_integral] using hp

end StratificationTheory.Compactness
