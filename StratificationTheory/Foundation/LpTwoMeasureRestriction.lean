module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

public section

open MeasureTheory Filter
open scoped ENNReal

namespace StratificationTheory

/-- The actual continuous change-of-measure operator sends an original
L2 class to the same original function on the smaller measure. -/
theorem lp_two_measure_restriction_toLp {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ ν : Measure X}
    (hμν : μ ≤ ν) (f : X → E) (hf : MemLp f 2 ν) (hsmall : MemLp f 2 μ) :
    Lp.LpToLpOfMeasureLeSMul (p := 2) (c := (1 : ℝ≥0∞))
      (by norm_num) (by simpa only [one_smul] using hμν) (hf.toLp f) = hsmall.toLp f := by
  apply Lp.ext
  have hcoe := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := (1 : ℝ≥0∞))
    (by norm_num) (show μ ≤ (1 : ℝ≥0∞) • ν by simpa only [one_smul] using hμν) (hf.toLp f)
  exact hcoe.trans (((Measure.absolutelyContinuous_of_le hμν).ae_eq hf.coeFn_toLp).trans hsmall.coeFn_toLp.symm)

end StratificationTheory
