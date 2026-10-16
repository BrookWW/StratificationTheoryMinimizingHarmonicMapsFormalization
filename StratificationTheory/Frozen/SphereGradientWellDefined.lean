-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SphereSobolev
public import Mathlib.MeasureTheory.Function.L2Space

import StratificationTheory.Providers.SphereGradientWellDefined

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff BigOperators

namespace StratificationTheory

theorem sphere_gradient_existsUnique {n q : ℕ} (hn : 2 ≤ n)
    (v : sphere (0 : Domain n) 1 → Ambient q) (hv : MemSphereW12 hn v) :
    ∃! G : Fin n → Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)),
      (∃ w : Domain n → Ambient q, ∃ D : Domain n → Gradient n q,
        MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D ∧
        (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
          w (ρ.val • θ.val) = v θ) ∧
        ∀ (ρ : PositiveRadius) (i : Fin n),
          (fun θ : sphere (0 : Domain n) 1 => ρ.val • D (ρ.val • θ.val) i) =ᵐ[
            (Measure.euclideanHausdorffMeasure (n - 1) :
              Measure (sphere (0 : Domain n) 1))] (fun θ => (G i) θ)) ∧
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)), (∑ i : Fin n, θ.val i • (G i) θ) = 0) ∧
      ∀ (U : OpenDomain n), sphere (0 : Domain n) 1 ⊆ U.val →
        (0 : Domain n) ∉ U.val →
        ∀ (z : Domain n → Ambient q) (Dz : Domain n → Gradient n q),
          MemW12 U z Dz →
          (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
            ρ.val • θ.val ∈ U.val → z (ρ.val • θ.val) = v θ) →
          ∀ᵐ x ∂volume.restrict U.val, ∀ hx : x ≠ 0, ∀ i : Fin n,
            Dz x i = ‖x‖⁻¹ • (G i) ((homeomorphUnitSphereProd (Domain n)
              ⟨x, hx⟩).1) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SphereGradientWellDefined.result hn v hv
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
