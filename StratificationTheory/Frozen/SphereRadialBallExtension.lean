-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SphereGradientCharacterization
public import HarmonicMaps.Energy
import StratificationTheory.Providers.SphereRadialBallExtension

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The same degree-zero radial weak extension has finite ball Sobolev data,
exact native gradient energy, and all native-a.e. value constraints in
ambient dimension at least three. -/
theorem exists_radial_ball_sobolev_extension {n q : ℕ} (hn : 3 ≤ n)
    (v : sphere (0 : Domain n) 1 → Ambient q)
    (hv : MemSphereW12 (by omega : 2 ≤ n) v) {R : ℝ} (hR : 0 < R) :
    ∃ (w : Domain n → Ambient q) (D : Domain n → Gradient n q),
      MemW12 (ballDomain 0 R) w D ∧
      (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
        w (ρ.val • θ.val) = v θ) ∧
      (∀ (ρ : PositiveRadius) (i : Fin n),
        (fun θ : sphere (0 : Domain n) 1 => ρ.val • D (ρ.val • θ.val) i) =ᵐ[
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))]
            (fun θ => (sphereGradient (by omega : 2 ≤ n) v hv i) θ)) ∧
      Integrable (fun x => hsNormSq (D x)) (volume.restrict (ball (0 : Domain n) R)) ∧
      (∫ x in ball (0 : Domain n) R, hsNormSq (D x)) =
        (R ^ (n - 2) / (n - 2)) *
          ∫ θ : sphere (0 : Domain n) 1, hsNormSq
            (fun i => (sphereGradient (by omega : 2 ≤ n) v hv i) θ)
            ∂Measure.euclideanHausdorffMeasure (n - 1) ∧
      ∀ P : Ambient q → Prop,
        (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1)), P (v θ)) →
        ∀ᵐ x ∂volume.restrict (ball (0 : Domain n) R), P (w x) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SphereRadialBallExtension.result hn v hv hR
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
