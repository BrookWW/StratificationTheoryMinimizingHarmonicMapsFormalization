module

public import StratificationTheory.Foundation.IntervalSobolevProductBase
public import StratificationTheory.Interpolation.CubicalEdgeInterpolationTrace
public import StratificationTheory.Foundation.UnitCubeFaceL2Trace

/-!
# The literal unit-time chord at an original vertex

The endpoint values at a physical vertex define one affine unit-time
map and its actual constant weak derivative.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The affine time chord of the two original values at one physical vertex. -/
@[expose] noncomputable def rawVertexUnitChord {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m) (x : Domain 1) : Ambient q :=
  (1 - (x 0 + 1) / 2) • u 0 y + ((x 0 + 1) / 2) • u 1 y

/-- The constant native unit-time derivative in the native unit-time coordinate. -/
@[expose] noncomputable def rawVertexUnitGradient {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m)
    (_x : Domain 1) (_i : Fin 1) : Ambient q :=
  (1 / 2 : ℝ) • (u 1 y - u 0 y)

theorem rawVertexUnitChord_eq {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m) (x : Domain 1) :
    rawVertexUnitChord u y x =
      (1 - (x 0 + 1) / 2) • u 0 y + ((x 0 + 1) / 2) • u 1 y := rfl

theorem rawVertexUnitGradient_eq {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m)
    (x : Domain 1) (i : Fin 1) :
    rawVertexUnitGradient u y x i = (1 / 2 : ℝ) • (u 1 y - u 0 y) := rfl

end StratificationTheory
