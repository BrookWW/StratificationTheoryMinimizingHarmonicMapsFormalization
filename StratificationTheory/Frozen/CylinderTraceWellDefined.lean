-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.CylinderSobolev
public import StratificationTheory.Foundation.CylinderPointCoordinates
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra

import StratificationTheory.Providers.CylinderTraceWellDefined

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff Topology
namespace StratificationTheory

/-- A full cylinder Sobolev map has one closed-interval continuous native
L2 time representative, determined by its original interior slice classes. -/
theorem cylinder_trace_existsUnique {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun p =>
      ⟨e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val), unitCylinder_param_mem p.1 p.2⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.CylinderTraceWellDefined.result hn hab v hv
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
