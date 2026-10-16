-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SphereGradient
import StratificationTheory.Providers.SphereGradientCharacterization

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped BigOperators
namespace StratificationTheory

/-- Full characterization, coherent-carrier uniqueness and a.e. class invariance of one native gradient family. -/
theorem sphereGradient_characterization {n q : ℕ} (hn : 2 ≤ n)
    (v : sphere (0 : Domain n) 1 → Ambient q) (hv : MemSphereW12 hn v) :
    ((∃ w : Domain n → Ambient q, ∃ D : Domain n → Gradient n q,
        MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D ∧
        (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
          w (ρ.val • θ.val) = v θ) ∧
        ∀ (ρ : PositiveRadius) (i : Fin n),
          (fun θ : sphere (0 : Domain n) 1 => ρ.val • D (ρ.val • θ.val) i) =ᵐ[
            (Measure.euclideanHausdorffMeasure (n - 1) :
              Measure (sphere (0 : Domain n) 1))] (fun θ => ((sphereGradient hn v hv) i) θ)) ∧
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)), (∑ i : Fin n, θ.val i • ((sphereGradient hn v hv) i) θ) = 0) ∧
      ∀ (U : OpenDomain n), sphere (0 : Domain n) 1 ⊆ U.val →
        (0 : Domain n) ∉ U.val →
        ∀ (z : Domain n → Ambient q) (Dz : Domain n → Gradient n q),
          MemW12 U z Dz →
          (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
            ρ.val • θ.val ∈ U.val → z (ρ.val • θ.val) = v θ) →
          ∀ᵐ x ∂volume.restrict U.val, ∀ hx : x ≠ 0, ∀ i : Fin n,
            Dz x i = ‖x‖⁻¹ • ((sphereGradient hn v hv) i) ((homeomorphUnitSphereProd (Domain n)
              ⟨x, hx⟩).1)) ∧
    (∀ H : Fin n → Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
      (∃ w : Domain n → Ambient q, ∃ D : Domain n → Gradient n q,
        MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D ∧
        (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
          w (ρ.val • θ.val) = v θ) ∧
        ∀ (ρ : PositiveRadius) (i : Fin n),
          (fun θ : sphere (0 : Domain n) 1 => ρ.val • D (ρ.val • θ.val) i) =ᵐ[
            (Measure.euclideanHausdorffMeasure (n - 1) :
              Measure (sphere (0 : Domain n) 1))] (fun θ => ((H) i) θ)) → H = sphereGradient hn v hv) ∧
    ∀ (v' : sphere (0 : Domain n) 1 → Ambient q) (hv' : MemSphereW12 hn v'),
      v =ᵐ[(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1))] v' →
      sphereGradient hn v' hv' = sphereGradient hn v hv :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SphereGradientCharacterization.result hn v hv
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
