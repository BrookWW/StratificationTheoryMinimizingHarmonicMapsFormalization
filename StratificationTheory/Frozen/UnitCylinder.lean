module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section
open HarmonicMaps Metric Set
namespace StratificationTheory

/-- The actual closed unit cylinder in Euclidean spatial-time coordinates. -/
@[expose] def unitCylinder (n : ℕ) (a b : ℝ) : Set (Domain (n + 1)) :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  {y | (e y).1 ∈ sphere (0 : Domain n) 1 ∧ (e y).2 0 ∈ Icc a b}

end StratificationTheory
