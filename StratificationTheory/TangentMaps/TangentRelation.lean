module

public import HarmonicMaps.Energy

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal
namespace StratificationTheory

/-- A tangent is an actual strong local L2 limit of the original rescaled
map and every displayed rescaled weak-gradient column along positive scales
converging to zero. No weak equation, target, minimality, energy identity or
homogeneity of the limit is part of this relation. -/
@[expose] def IsTangentAt {n q : ℕ} (u : Domain n → Ambient q)
    (Du : Domain n → Gradient n q) (a : Domain n)
    (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q) : Prop :=
  LocallyMemL2 ⟨univ, isOpen_univ⟩ φ ∧
    (∀ i : Fin n, LocallyMemL2 ⟨univ, isOpen_univ⟩ (fun x => Dφ x i)) ∧
    ∃ ρ : ℕ → PositiveRadius,
      Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ)) ∧
      ∀ K : Set (Domain n), IsCompact K →
      (∀ᶠ k in atTop,
        MemLp (fun x => u (a + (ρ k).val • x)) 2 (volume.restrict K) ∧
        ∀ i : Fin n, MemLp (fun x => (ρ k).val • Du (a + (ρ k).val • x) i)
          2 (volume.restrict K)) ∧
      Tendsto (fun k => eLpNorm
        ((fun x => u (a + (ρ k).val • x)) - φ) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun x => (ρ k).val • Du (a + (ρ k).val • x) i - Dφ x i)
          2 (volume.restrict K)) atTop (𝓝 0)

end StratificationTheory
