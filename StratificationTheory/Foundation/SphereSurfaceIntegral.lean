module

public import StratificationTheory.Foundation.AngularL2Membership
public import HarmonicMaps.Analysis.SphereSurfaceMeasure
public import StratificationTheory.Foundation.SphereSliceGradientData
import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators

namespace StratificationTheory

/-- Translation preserves the actual normalized Hausdorff restriction on
every sphere, with no change to its radius or dimension. -/
theorem map_euclidean_sphereArea_add {n : ℕ} (d : ℕ) (a : Domain n) (r : ℝ) :
    Measure.map (fun x : Domain n => a + x)
      ((Measure.euclideanHausdorffMeasure d : Measure (Domain n)).restrict (sphere 0 r)) =
        (Measure.euclideanHausdorffMeasure d : Measure (Domain n)).restrict (sphere a r) := by
  have hi : Isometry (fun x : Domain n => a + x) :=
    Isometry.of_dist_eq (fun x y => by simp)
  have hs : Function.Surjective (fun x : Domain n => a + x) := by
    intro y
    refine ⟨y - a, ?_⟩
    abel_nf
  have hm : Measure.map (fun x : Domain n => a + x)
      (Measure.euclideanHausdorffMeasure d : Measure (Domain n)) =
        (Measure.euclideanHausdorffMeasure d : Measure (Domain n)) := by
    rw [hi.map_euclideanHausdorffMeasure, hs.range_eq, Measure.restrict_univ]
  have hp : (fun x : Domain n => a + x) ⁻¹' sphere a r = sphere 0 r := by
    ext x
    simp
  have h := Measure.restrict_map hi.continuous.measurable (isClosed_sphere.measurableSet)
    (s := sphere a r)
    (μ := (Measure.euclideanHausdorffMeasure d : Measure (Domain n)))
  rw [hm, hp] at h
  exact h.symm

/-- The affine unit-sphere parametrization carries the genuine dimensional
weight to normalized Hausdorff area on the actual centered sphere. -/
theorem map_native_unitSphere_weighted_affine {n : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) :
    Measure.map (fun θ : sphere (0 : Domain n) 1 => a + R.val • θ.val)
      (ENNReal.ofReal (R.val ^ (n - 1)) •
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))) =
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
        (sphere a R.val) := by
  have hnpos : 0 < n := by omega
  rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos]
  have htrans := map_euclidean_sphereArea_add (n - 1) a R.val
  rw [← poisson_scaledPolar_eq_euclideanSphereArea hn R] at htrans
  have hm : Measurable (fun x : Domain n => a + x) :=
    (continuous_const.add continuous_id).measurable
  have hR : Measurable (fun θ : sphere (0 : Domain n) 1 => R.val • θ.val) :=
    (continuous_subtype_val.const_smul R.val).measurable
  rw [Measure.map_map hm hR] at htrans
  exact htrans

/-- Actual surface integrals have the exact positive-radius scaling factor.
This is an integral transport identity; finite energy requires integrability. -/
theorem integral_euclidean_sphereArea_affine {n : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (g : Domain n → ℝ) :
    (∫ x in sphere a R.val, g x ∂Measure.euclideanHausdorffMeasure (n - 1)) =
      R.val ^ (n - 1) * ∫ θ : sphere (0 : Domain n) 1,
        g (a + R.val • θ.val) ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  have hc : Topology.IsClosedEmbedding
      (fun θ : sphere (0 : Domain n) 1 => a + R.val • θ.val) :=
    (Homeomorph.addLeft a).isClosedEmbedding.comp
      ((Homeomorph.smul (Units.mk0 R.val R.property.ne')).isClosedEmbedding.comp
        isClosed_sphere.isClosedEmbedding_subtypeVal)
  rw [← map_native_unitSphere_weighted_affine hn a R, hc.integral_map,
    integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg R.property.le _), smul_eq_mul]

/-- Finite integrability is preserved by the same actual positive-radius
surface transport; the positive finite weight cannot mask infinite energy. -/
theorem integrable_euclidean_sphereArea_affine_iff {n : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (g : Domain n → ℝ) :
    Integrable g ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (Domain n)).restrict (sphere a R.val)) ↔
      Integrable (fun θ : sphere (0 : Domain n) 1 => g (a + R.val • θ.val))
        (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1)) := by
  have hc : Topology.IsClosedEmbedding
      (fun θ : sphere (0 : Domain n) 1 => a + R.val • θ.val) :=
    (Homeomorph.addLeft a).isClosedEmbedding.comp
      ((Homeomorph.smul (Units.mk0 R.val R.property.ne')).isClosedEmbedding.comp
        isClosed_sphere.isClosedEmbedding_subtypeVal)
  rw [← map_native_unitSphere_weighted_affine hn a R,
    hc.measurableEmbedding.integrable_map_iff]
  exact integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos R.property _)) ENNReal.ofReal_ne_top

/-- The coherent native gradient class of the actual Sobolev slice satisfies
the physical-surface scaling estimate with finite original HS energy. -/
theorem ae_sphere_slice_gradient_class_surface_energy_le {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun x => hsNormSq (Du x))
        ((Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (Domain n)).restrict (sphere a r)) ∧
      ∀ (w : Domain n → Ambient q) (D : Domain n → Gradient n q)
        (G : Fin n → Lp (Ambient q) 2
          (Measure.euclideanHausdorffMeasure (n - 1) :
            Measure (sphere (0 : Domain n) 1))),
        MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D →
        (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
          w (ρ.val • θ.val) = u (a + r • θ.val)) →
        (∀ (ρ : PositiveRadius) (i : Fin n),
          (fun θ : sphere (0 : Domain n) 1 => ρ.val • D (ρ.val • θ.val) i)
            =ᵐ[(Measure.euclideanHausdorffMeasure (n - 1) :
              Measure (sphere (0 : Domain n) 1))] (fun θ => (G i) θ)) →
        (∑ i : Fin n, ‖G i‖ ^ 2) ≤ r ^ (3 - (n : ℤ)) *
          ∫ x in sphere a r, hsNormSq (Du x)
            ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  have hnpos : 0 < n := by omega
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_exists_sphere_slice_radial_gradient_data hnpos hu hR hball,
    ae_sphere_slice_gradient_class_energy_le hnpos hu hR hball] with r hr hdata henergy
  let ρ : PositiveRadius := ⟨r, hr.1⟩
  have hDu (i : Fin n) := hdata.1 i
  have hHS : Integrable
      (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Du (a + r • θ.val)))
        (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1)) :=
    integrable_finsetSum Finset.univ
      (fun i _ => (hDu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  refine ⟨(integrable_euclidean_sphereArea_affine_iff hn a ρ
    (fun x => hsNormSq (Du x))).mpr hHS, ?_⟩
  intro w D G hW hw hD
  have hscale : r ^ (3 - (n : ℤ)) * r ^ (n - 1) = r ^ 2 := by
    rw [← zpow_natCast r (n - 1), ← zpow_add₀ hr.1.ne']
    have hdim : (3 - (n : ℤ)) + ((n - 1 : ℕ) : ℤ) = 2 := by omega
    rw [hdim]
    norm_num only [zpow_ofNat]
  rw [integral_euclidean_sphereArea_affine hn a ρ (fun x => hsNormSq (Du x))]
  change (∑ i : Fin n, ‖G i‖ ^ 2) ≤ r ^ (3 - (n : ℤ)) *
    (r ^ (n - 1) * ∫ θ : sphere (0 : Domain n) 1,
      hsNormSq (Du (a + r • θ.val)) ∂Measure.euclideanHausdorffMeasure (n - 1))
  rw [← mul_assoc, hscale]
  exact henergy w D G hW hw hD

end StratificationTheory
