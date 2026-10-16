module

public import StratificationTheory.Frozen.SpineWellDefined

public section
open HarmonicMaps MeasureTheory Set

namespace StratificationTheory

/-- The unique real subspace with the full density-equality carrier of the
given homogeneous minimizer. -/
@[expose] noncomputable def spine {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u) : Subspace ℝ (Domain n) :=
  Classical.choose (spine_wellDefined hn hmin hu hN hhom).exists

end StratificationTheory
