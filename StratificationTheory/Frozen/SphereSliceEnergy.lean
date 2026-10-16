-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SphereSlices
public import StratificationTheory.Frozen.SphereGradientCharacterization
import StratificationTheory.Providers.SphereSliceEnergy

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace StratificationTheory

/-- Sphere membership and the native intrinsic-gradient energy
bound share the same radial full-measure set and the same actual slice. -/
theorem ae_sphereSobolev_and_gradientEnergy {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ} (hR : 0 < R) (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      ∃ hv : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)),
        Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq
          (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) hv i) θ))
            (Measure.euclideanHausdorffMeasure (n - 1) :
              Measure (sphere (0 : Domain n) 1)) ∧
        Integrable (fun x => hsNormSq (Du x))
          ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
            (sphere a r)) ∧
        (∫ θ : sphere (0 : Domain n) 1, hsNormSq
          (fun i => (sphereGradient hn (fun η => u (a + r • η.val)) hv i) θ)
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ≤
          r ^ (3 - (n : ℤ)) * ∫ x in sphere a r, hsNormSq (Du x)
            ∂Measure.euclideanHausdorffMeasure (n - 1) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.SphereSliceEnergy.result hn hu hR hball
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
