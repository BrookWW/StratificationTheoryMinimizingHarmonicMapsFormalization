module

public import StratificationTheory.Frozen.SphereSlices
public import StratificationTheory.Frozen.SphereGradientCharacterization
import StratificationTheory.Foundation.SphereSurfaceIntegral
import StratificationTheory.Foundation.SphereSobolevSliceClosure

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace StratificationTheory.Providers.SphereSliceEnergy

/-- Sphere membership and the native intrinsic-gradient energy
bound share the same radial full-measure set and the same actual slice. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
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
            ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  have hnpos : 0 < n := by omega
  obtain ⟨m, hm, _hmW, κ, _hκ, hae⟩ :=
    exists_smooth_subseq_ae_angular_graph_approximation hnpos hu hR hball
  filter_upwards [hae, ae_sphere_slice_gradient_class_surface_energy_le hn hu hR hball]
    with r hr he
  have hmk (k : ℕ) : MemLp
      (fun θ : sphere (0 : Domain n) 1 => m (κ k) (a + r • θ.val))
        2 (volume : Measure (Domain n)).toSphere := (hr.2.2.1 (κ k)).1
  have hDmk (k : ℕ) (i : Fin n) : MemLp
      (fun θ : sphere (0 : Domain n) 1 =>
        coordinateDerivative (m (κ k)) (hm (κ k)) i (a + r • θ.val))
          2 (volume : Measure (Domain n)).toSphere := (hr.2.2.1 (κ k)).2 i
  have hv : MemSphereW12 hn
      (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) :=
    @memSphereW12_of_smooth_angular_graph_limit n q hn u Du
      (fun k => m (κ k)) (fun k => hm (κ k)) a r hr.1 hr.2.1 hmk hDmk
        hr.2.2.2.2.1 hr.2.2.2.2.2
  let G := sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) hv
  have hG (i : Fin n) : MemLp (fun θ => (G i) θ) 2
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)) := Lp.memLp (G i)
  have hGI : Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (fun i => (G i) θ))
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)) :=
    integrable_finsetSum Finset.univ
      (fun i _ => (hG i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hnorm := sum_column_Lp_norm_sq_eq_integral_angular_hsNormSq hG
  simp only [Lp.toLp_coeFn] at hnorm
  obtain ⟨w, D, hW, hw, hD⟩ :=
    (sphereGradient_characterization hn (fun θ => u (a + r • θ.val)) hv).1.1
  refine ⟨hv, hGI, he.1, ?_⟩
  rw [← hnorm]
  exact he.2 w D G hW hw hD

end StratificationTheory.Providers.SphereSliceEnergy
