module

public import StratificationTheory.Frozen.Spine

public section
open HarmonicMaps MeasureTheory Set

namespace StratificationTheory.Providers.SpineCharacterization

/-- Complete source characterization and carrier uniqueness of the same
chosen spine, including density maximum and translation invariance. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
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
      V = spine hn hmin hu hN hhom := by
  have hs := Classical.choose_spec (spine_wellDefined hn hmin hu hN hhom).exists
  change
    (∀ y : Domain n, y ∈ spine hn hmin hu hN hhom ↔
      density hn hmin hu hN ⟨y, mem_univ y⟩ = density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
    (∀ y : Domain n,
      density hn hmin hu hN ⟨y, mem_univ y⟩ ≤ density hn hmin hu hN ⟨0, mem_univ 0⟩) ∧
    ∀ y : Domain n, y ∈ spine hn hmin hu hN hhom →
      (fun x => u (x + y)) =ᵐ[volume] u at hs
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  intro V hV
  ext y
  exact (hV y).trans (hs.1 y).symm

end StratificationTheory.Providers.SpineCharacterization
