module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

open Filter
open scoped Topology

namespace StratificationTheory.Compactness

/-- Convergence of the squared norm and the pairing with the limit implies
strong convergence in a real inner product space. -/
theorem tendsto_of_norm_sq_and_inner {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {l : Filter ι} {f : ι → H} {u : H}
    (hnorm : Tendsto (fun k => ‖f k‖ ^ 2) l (𝓝 (‖u‖ ^ 2)))
    (hinner : Tendsto (fun k => inner ℝ (f k) u) l (𝓝 (inner ℝ u u))) :
    Tendsto f l (𝓝 u) := by
  have hzero : ‖u‖ ^ 2 - 2 * inner ℝ u u + ‖u‖ ^ 2 = 0 := by
    rw [real_inner_self_eq_norm_sq]
    ring
  have hsq : Tendsto (fun k => ‖f k - u‖ ^ 2) l (𝓝 0) := by
    have h := (hnorm.sub (hinner.const_mul 2)).add_const (‖u‖ ^ 2)
    rw [hzero] at h
    simpa only [norm_sub_sq_real] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

end StratificationTheory.Compactness
