module

public import StratificationTheory.Foundation.ConicalNormalTrace

/-!
# Literal spatial normal maps with an independent time coordinate

The normal vector, parallel embedding and tangential shift are total
Euclidean formulas. Each has a zero or unchanged independent time coordinate.
-/

public section
open HarmonicMaps
namespace StratificationTheory

@[expose] noncomputable def spatialConeNormalVector (n : ℕ) : Domain (n + 1 + 1 + 1) :=
  let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
  let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
  eF.symm (e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
    EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹),0)

@[expose] noncomputable def spatialConeParallelSlice (n : ℕ) (δ : ℝ)
    (y : Domain (n + 1 + 1)) : Domain (n + 1 + 1 + 1) :=
  let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
  let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
  eF.symm (e.symm (b.symm ((b (e y).1).1,
    EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0 - δ)),
      EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0)),(e y).2)

@[expose] noncomputable def spatialConeNormalTangentialShift (n : ℕ) (η : ℝ) :
    Domain (n + 1 + 1) :=
  let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
  e.symm (b.symm (0,EuclideanSpace.single (0 : Fin 1) (η / Real.sqrt 2)),0)

theorem spatialConeNormalVector_eq (n : ℕ) :
    spatialConeNormalVector n =
      let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
      let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
      eF.symm (e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
        EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹),0) := rfl

theorem spatialConeParallelSlice_eq (n : ℕ) (δ : ℝ) (y : Domain (n + 1 + 1)) :
    spatialConeParallelSlice n δ y =
      let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
      let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
      eF.symm (e.symm (b.symm ((b (e y).1).1,
        EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0 - δ)),
          EuclideanSpace.single (0 : Fin 1) ((b (e y).1).2 0)),(e y).2) := rfl

theorem spatialConeNormalTangentialShift_eq (n : ℕ) (η : ℝ) :
    spatialConeNormalTangentialShift n η =
      let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
      e.symm (b.symm (0,EuclideanSpace.single (0 : Fin 1) (η / Real.sqrt 2)),0) := rfl

end StratificationTheory
