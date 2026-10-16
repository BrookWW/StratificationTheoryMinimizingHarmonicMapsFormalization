module

public import HarmonicMaps.Sobolev

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- Every finite native coordinate cube is its actual open Euclidean
carrier, including zero dimension and empty or reversed intervals. -/
theorem isOpen_native_coordinate_cube (d : ℕ) (a b : ℝ) :
    IsOpen (⋂ k : Fin d, (fun x : Domain d => x k) ⁻¹' Ioo a b) :=
  isOpen_iInter_of_finite fun k : Fin d =>
    isOpen_Ioo.preimage (EuclideanSpace.proj k : Domain d →L[ℝ] ℝ).continuous

end StratificationTheory
