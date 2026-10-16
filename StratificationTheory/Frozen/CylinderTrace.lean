module

public import StratificationTheory.Frozen.CylinderTraceWellDefined

public section
open HarmonicMaps MeasureTheory Metric Set
namespace StratificationTheory

/-- The unique continuous native-L2 trace curve of a full cylinder Sobolev map. -/
@[expose] noncomputable def cylinderTrace {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) :
    C(Icc a b, Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))) :=
  Classical.choose (cylinder_trace_existsUnique hn hab v hv).exists

end StratificationTheory
