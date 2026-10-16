module

public import StratificationTheory.Interpolation.AffineCylinderRayGradient
import StratificationTheory.Foundation.CylinderIntegralTransport

/-!
# Native energy with all-radius weak-column coherence

The native energy comparison uses radius one of the same actual weak pair.
Every positive-radius column identity is retained for annular transport.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal
namespace StratificationTheory

/-- One affine cylinder weak pair retains all positive-radius columns and
the native integrable energy bound in the original named sphere gradients. -/
theorem exists_cylinder_affine_all_radius_native_energy {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let U : OpenDomain n := ⟨{x : Domain n | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩
    ∃ w : Domain (n + 1) → Ambient q, ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
      MemW12
        ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
          (U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩ w Dw ∧
      (∀ (ρ : PositiveRadius) (c : unitCylinder n a b),
        (e c.val).2 0 ∈ Ioo a b → ρ.val • (e c.val).1 ∈ U.val →
          w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) =
            (1 - ((e c.val).2 0 - a) / (b - a)) • u ⟨(e c.val).1, c.property.1⟩ +
              (((e c.val).2 0 - a) / (b - a)) • v ⟨(e c.val).1, c.property.1⟩) ∧
      (∀ ρ : PositiveRadius, ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
        ∀ t : ℝ, Dw (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn u hu i) θ) +
              ((t - a) / (b - a)) • (ρ.val⁻¹ • (sphereGradient hn v hv i) θ))
            (fun _ => (b - a)⁻¹ • (v θ - u θ))) ∧
      Integrable (fun c : unitCylinder n a b => hsNormSq (Dw c.val))
        (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) ∧
      (∫ c : unitCylinder n a b, hsNormSq (Dw c.val) ∂Measure.euclideanHausdorffMeasure n) ≤
        ((b - a) / 2) *
          (∫ θ : sphere (0 : Domain n) 1,
            ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
              ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂Measure.euclideanHausdorffMeasure (n - 1)) +
          (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
            ∂Measure.euclideanHausdorffMeasure (n - 1)) := by
  intro e U
  obtain ⟨w, Dw, hW, hraw, hD⟩ := exists_cylinder_affine_all_radius_gradient hn hab u v hu hv
  have hDone : ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t : ℝ, Dw (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
        Fin.addCases
          (fun i => (1 - (t - a) / (b - a)) • (sphereGradient hn u hu i) θ +
            ((t - a) / (b - a)) • (sphereGradient hn v hv i) θ)
          (fun _ => (b - a)⁻¹ • (v θ - u θ)) := by
    simpa only [one_smul, inv_one] using hD ⟨1, by norm_num⟩
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let μ := σ.prod (volume.restrict (Icc a b))
  let Gu : sphere (0 : Domain n) 1 → Fin n → Ambient q :=
    fun θ i => (sphereGradient hn u hu i) θ
  let Gv : sphere (0 : Domain n) 1 → Fin n → Ambient q :=
    fun θ i => (sphereGradient hn v hv i) θ
  let E : sphere (0 : Domain n) 1 × ℝ → ℝ := fun p =>
    (∑ i : Fin n, ‖(1 - (p.2 - a) / (b - a)) • Gu p.1 i +
      ((p.2 - a) / (b - a)) • Gv p.1 i‖ ^ 2) +
      ‖(b - a)⁻¹ • (v p.1 - u p.1)‖ ^ 2
  let F : sphere (0 : Domain n) 1 × ℝ → ℝ := fun p =>
    hsNormSq (Dw (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)))
  have henergy := native_linear_cylinder_field_energy hab hu.1 hv.1
    (fun i => Lp.memLp (sphereGradient hn u hu i))
    (fun i => Lp.memLp (sphereGradient hn v hv i))
  have hFE : F =ᵐ[μ] E := by
    have hp : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
        ∀ t : ℝ, Dw (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases
            (fun i => (1 - (t - a) / (b - a)) • Gu p.1 i + ((t - a) / (b - a)) • Gv p.1 i)
            (fun _ => (b - a)⁻¹ • (v p.1 - u p.1)) :=
      Measure.quasiMeasurePreserving_fst.ae hDone
    filter_upwards [hp] with p hp
    dsimp only [F]
    rw [hp p.2]
    simp only [hsNormSq, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Fin.sum_univ_one, E]
  have hFI : Integrable F μ := henergy.1.congr hFE.symm
  have htransport := integrable_unitCylinder_of_param_and_integral (by omega : 0 < n)
    (fun c : unitCylinder n a b => hsNormSq (Dw c.val)) F hFI (fun _ _ => rfl)
  refine ⟨w, Dw, hW, hraw, hD, htransport.1, ?_⟩
  calc
    (∫ c : unitCylinder n a b, hsNormSq (Dw c.val) ∂Measure.euclideanHausdorffMeasure n) =
        ∫ p, F p ∂μ := htransport.2
    _ = ∫ p, E p ∂μ := integral_congr_ae hFE
    _ ≤ _ := henergy.2.2.2

end StratificationTheory
