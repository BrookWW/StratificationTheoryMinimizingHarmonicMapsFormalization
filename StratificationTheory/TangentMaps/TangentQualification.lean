-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.TangentMaps.PrescribedTangentExtraction
public import StratificationTheory.Foundation.MinimizerAECongruence
public import HarmonicMaps.Analysis.SobolevAECongruence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

import StratificationTheory.Providers.TangentQualification

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal
namespace StratificationTheory

/-- Every actual raw strong tangent limit has the original global weak,
target, minimizing, density-energy and homogeneity properties. -/
theorem IsTangentAt.qualification {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hT : IsTangentAt u Du a.val φ Dφ) :
    MemW12Loc ⟨univ, isOpen_univ⟩ φ Dφ ∧
      TakesValuesIn N ⟨univ, isOpen_univ⟩ φ ∧
      IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ φ Dφ ∧
      (∀ R : PositiveRadius,
        (normalizedEnergy Dφ (0 : Domain n) R).toReal = density hn hMinimizer hu hTarget a) ∧
      ∀ l : ℝ, 0 < l → (fun x => φ (l • x)) =ᵐ[volume] φ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by
  exact StratificationTheory.Providers.TangentQualification.result hn N Ω u Du hu hTarget hMinimizer a φ Dφ hT
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
