-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import HarmonicMaps.Minimizer
public import StratificationTheory.Frozen.DensityCharacterization
public import Mathlib.Analysis.InnerProductSpace.Subspace

import StratificationTheory.Providers.SpineWellDefined

public section
open HarmonicMaps MeasureTheory Set

namespace StratificationTheory

/-- A globally local homogeneous minimizer determines one real subspace with
its full density-equality carrier, global density maximum and translation
invariance of the same almost-everywhere map class. -/
theorem spine_wellDefined {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u) :
    ∃! V : Subspace ℝ (Domain n),
      (∀ y : Domain n, y ∈ V ↔
        density hn hmin hu hN ⟨y, mem_univ y⟩ = density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
      (∀ y : Domain n,
        density hn hmin hu hN ⟨y, mem_univ y⟩ ≤ density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
      ∀ y : Domain n, y ∈ V → (fun x => u (x + y)) =ᵐ[volume] u :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SpineWellDefined.result hn hmin hu hN hhom
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
