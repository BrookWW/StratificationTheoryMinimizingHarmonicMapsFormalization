module

public import StratificationTheory.Frozen.DensityWellDefined

public section

open HarmonicMaps

namespace StratificationTheory

/-- The unique finite density of a locally minimizing map at a point of its
open domain. -/
@[expose] noncomputable def density {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) (a : Ω.val) : ℝ :=
  Classical.choose (density_wellDefined hn hmin hu hN a.val a.property)

end StratificationTheory
