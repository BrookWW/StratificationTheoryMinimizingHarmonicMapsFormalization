module

public import StratificationTheory.Foundation.SobolevAngularApproximation
public import StratificationTheory.Foundation.SphereRadialGradientExistence
public import StratificationTheory.Foundation.RadialWeakGradientLocality
public import StratificationTheory.Foundation.AngularGradientUniqueness
public import StratificationTheory.Foundation.AngularGradientEnergy

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff BigOperators

namespace StratificationTheory

/-- At almost every radius, the actual Sobolev slice has a punctured weak
extension whose angular columns are the scaled tangential projection of the
same original weak gradient. All radii of the extension share this field. -/
theorem ae_exists_sphere_slice_radial_gradient_data {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      (∀ i : Fin n, MemLp (fun θ : sphere (0 : Domain n) 1 => Du (a + r • θ.val) i)
        2 (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1))) ∧
      ∃ w : Domain n → Ambient q, ∃ D : Domain n → Gradient n q,
        MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D ∧
        (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
          w (ρ.val • θ.val) = u (a + r • θ.val)) ∧
        ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
          D (ρ.val • θ.val) i = ρ.val⁻¹ •
            (r • tangentialColumns θ (Du (a + r • θ.val)) i) := by
  obtain ⟨m, hm, _hmW, κ, _hκ, hae⟩ :=
    exists_smooth_subseq_ae_angular_graph_approximation hn hu hR hball
  filter_upwards [hae] with r hr
  obtain ⟨huL, hDuL, hmL, _herr, hconv, hDconv⟩ := hr
  obtain ⟨D, hW, hDRay⟩ := exists_radial_weak_gradient_of_smooth_angular_graph_limit
    hn (u := u) (Du := Du) (f := fun k => m (κ k)) (fun k => hm (κ k)) a r
      huL hDuL (fun k => (hmL (κ k)).1) (fun k i => (hmL (κ k)).2 i)
      hconv hDconv
  let w : Domain n → Ambient q := fun x => u (a + r • (‖x‖⁻¹ • x))
  let A : sphere (0 : Domain n) 1 → Gradient n q :=
    fun θ i => r • tangentialColumns θ (Du (a + r • θ.val)) i
  have hwRay (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) :
      w (ρ.val • θ.val) = u (a + r • θ.val) :=
    radial_smooth_pullback_ray u a r ρ.property θ
  have hA (i : Fin n) : MemLp (fun θ => A θ i) 2
      (volume : Measure (Domain n)).toSphere :=
    (memLp_two_tangential_column hDuL i).const_smul r
  have hD (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n) :
      D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i := by
    rw [hDRay ρ θ i]
    simp only [A, smul_smul, div_eq_mul_inv, mul_comm r ρ.val⁻¹]
  refine ⟨?_, w, D, memW12Loc_punctured_of_radial_collar hn huL hA hwRay hD hW,
    hwRay, hD⟩
  intro i
  rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
  exact hDuL i

/-- Every native L2 gradient class with an actual coherent weak extension of
the same slice satisfies the original-field energy bound on the same radial
full-measure set. No gradient class is assumed to exist as an outer input. -/
theorem ae_sphere_slice_gradient_class_energy_le {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
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
        (∑ i : Fin n, ‖G i‖ ^ 2) ≤ r ^ 2 *
          ∫ θ : sphere (0 : Domain n) 1, hsNormSq (Du (a + r • θ.val))
            ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  classical
  have haeSphere : ae (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)) = ae (volume : Measure (Domain n)).toSphere :=
    congrArg ae (euclideanHausdorffMeasure_unitSphere_eq_toSphere hn)
  filter_upwards [ae_exists_sphere_slice_radial_gradient_data hn hu hR hball] with r hr
  obtain ⟨hDuL, wA, DA, hWA, hwA, hDA⟩ := hr
  intro w D G hW hw hDG
  let A : sphere (0 : Domain n) 1 → Gradient n q :=
    fun θ i => r • tangentialColumns θ (Du (a + r • θ.val)) i
  have hDuVol (i : Fin n) : MemLp
      (fun θ : sphere (0 : Domain n) 1 => Du (a + r • θ.val) i) 2
        (volume : Measure (Domain n)).toSphere := by
    rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    exact hDuL i
  have hA (i : Fin n) : MemLp (fun θ => A θ i) 2
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)) := by
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    exact (memLp_two_tangential_column hDuVol i).const_smul r
  have hDFormula (ρ : PositiveRadius) (i : Fin n) :
      (fun θ : sphere (0 : Domain n) 1 => D (ρ.val • θ.val) i)
        =ᵐ[(volume : Measure (Domain n)).toSphere]
          (fun θ => ρ.val⁻¹ • (G i) θ) := by
    have h := hDG ρ i
    rw [haeSphere] at h
    filter_upwards [h] with θ hθ
    have heq := congrArg (fun z : Ambient q => ρ.val⁻¹ • z) hθ
    simpa only [smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul] using heq
  have hAFormula (ρ : PositiveRadius) (i : Fin n) :
      (fun θ : sphere (0 : Domain n) 1 => DA (ρ.val • θ.val) i)
        =ᵐ[(volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • A θ i) :=
    Eventually.of_forall (fun θ => hDA ρ θ i)
  have hAG := angular_radial_gradient_ae_eq_of_ae_formula hn
    (A := A) (B := fun θ i => (G i) θ) hWA hW hwA hw hAFormula hDFormula
  have hclasses (i : Fin n) : (hA i).toLp (fun θ => A θ i) = G i := by
    apply Lp.ext
    apply (hA i).coeFn_toLp.trans
    rw [haeSphere]
    exact hAG i
  calc
    (∑ i : Fin n, ‖G i‖ ^ 2) = ∑ i : Fin n, ‖(hA i).toLp (fun θ => A θ i)‖ ^ 2 := by
      simp_rw [hclasses]
    _ = ∫ θ : sphere (0 : Domain n) 1, hsNormSq (A θ)
        ∂Measure.euclideanHausdorffMeasure (n - 1) :=
      sum_column_Lp_norm_sq_eq_integral_angular_hsNormSq hA
    _ ≤ r ^ 2 * ∫ θ : sphere (0 : Domain n) 1, hsNormSq (Du (a + r • θ.val))
        ∂Measure.euclideanHausdorffMeasure (n - 1) :=
      integral_native_hsNormSq_scaled_tangentialColumns_le hn hDuL r

end StratificationTheory
