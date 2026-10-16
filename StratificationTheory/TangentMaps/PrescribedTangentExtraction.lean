-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.TangentMaps.TangentRelation
public import StratificationTheory.Foundation.DensityBounds
public import StratificationTheory.TangentMaps.RescaledNestedBallFamily
public import StratificationTheory.TangentMaps.NestedBallStrongGluing
public import StratificationTheory.Foundation.GlobalMinimizerBallAssembly
public import StratificationTheory.Foundation.RadialHomogeneity

import StratificationTheory.Providers.PrescribedTangentExtraction

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- Every prescribed positive shrinking scale sequence admits one global
locally minimizing tangent, with one common subsequence on all compact sets,
all-radius source-density energy and degree-zero AE homogeneity. -/
theorem exists_tangent_along_prescribed_scales {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ))) :
    ∃ (κ : ℕ → ℕ) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ ∧
      TakesValuesIn N ⟨univ, isOpen_univ⟩ φ ∧
      IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ ∧
      (∀ K : Set (Domain n), IsCompact K →
        Tendsto (fun k => eLpNorm
          ((fun x => u (a.val + (ρ (κ k)).val • x)) - φ) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ i : Fin n, Tendsto (fun k => eLpNorm
          (fun x => (ρ (κ k)).val • Du (a.val + (ρ (κ k)).val • x) i - Dφ x i)
            2 (volume.restrict K)) atTop (𝓝 0)) ∧
      (∀ R : PositiveRadius,
        (normalizedEnergy Dφ (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a) ∧
      (∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ) ∧
      IsTangentAt u Du a.val φ Dφ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by
  exact StratificationTheory.Providers.PrescribedTangentExtraction.result hn N Ω u Du hu hTarget hMinimizer a ρ hρ
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
