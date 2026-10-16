module

public import StratificationTheory.Frozen.SphereGradientWellDefined

public section
open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

/-- The unique native angular L2-gradient class of the actual sphere Sobolev map. -/
@[expose] noncomputable def sphereGradient {n q : ℕ} (hn : 2 ≤ n)
    (v : sphere (0 : Domain n) 1 → Ambient q) (hv : MemSphereW12 hn v) :
    Fin n → Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) :=
  Classical.choose (sphere_gradient_existsUnique hn v hv).exists

end StratificationTheory
