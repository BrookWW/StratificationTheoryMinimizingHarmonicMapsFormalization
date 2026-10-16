-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.Spine

import StratificationTheory.Providers.SpineCharacterization

public section
open HarmonicMaps MeasureTheory Set

namespace StratificationTheory

/-- Complete source characterization and carrier uniqueness of the same
chosen spine, including density maximum and translation invariance. -/
theorem spine_characterization {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u) :
    (∀ y : Domain n, y ∈ spine hn hmin hu hN hhom ↔
      density hn hmin hu hN ⟨y, mem_univ y⟩ = density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
    (∀ y : Domain n,
      density hn hmin hu hN ⟨y, mem_univ y⟩ ≤ density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
    (∀ y : Domain n, y ∈ spine hn hmin hu hN hhom →
      (fun x => u (x + y)) =ᵐ[volume] u) ∧
    ∀ V : Subspace ℝ (Domain n),
      (∀ y : Domain n, y ∈ V ↔
        density hn hmin hu hN ⟨y, mem_univ y⟩ = density hn hmin hu hN ⟨0, mem_univ 0⟩) →
      V = spine hn hmin hu hN hhom :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SpineCharacterization.result hn hmin hu hN hhom
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
