module

public import StratificationTheory.Frozen.SphereGradientCharacterization
public import StratificationTheory.Foundation.RadialSobolevRemoval
import StratificationTheory.Foundation.SphereAEClasses

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
open StratificationTheory
namespace StratificationTheory.Providers.SphereRadialBallExtension

theorem result {n q : ℕ} (hn : 3 ≤ n)
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
        ∀ᵐ x ∂volume.restrict (ball (0 : Domain n) R), P (w x) := by
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Domain n) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hσ := euclideanHausdorffMeasure_unitSphere_eq_toSphere (n := n) hnpos
  have haeSphere := congrArg ae hσ
  let G := sphereGradient hn2 v hv
  obtain ⟨w, D, hP, hwRay, hD⟩ := (sphereGradient_characterization hn2 v hv).1.1
  have hvLp : MemLp v 2 (volume : Measure (Domain n)).toSphere := by
    simpa only [hσ] using hv.1
  have hwLp := (memLp_two_radial_ball_and_norm hnpos hvLp hwRay hR).1
  have hG (i : Fin n) : MemLp (fun θ => (G i) θ) 2
      (volume : Measure (Domain n)).toSphere := by
    rw [← hσ]
    exact Lp.memLp (G i)
  have hDi (i : Fin n) :
      MemLp (fun x => D x i) 2 (volume.restrict (ball (0 : Domain n) R)) ∧
      (∫ x in ball (0 : Domain n) R, ‖D x i‖ ^ 2) =
        (R ^ (n - 2) / (n - 2)) *
          ∫ θ : sphere (0 : Domain n) 1, ‖(G i) θ‖ ^ 2
            ∂(volume : Measure (Domain n)).toSphere := by
    have hm : AEStronglyMeasurable (fun x => D x i) volume := by
      have hm := (hP.1.2.1 i).aestronglyMeasurable
      rwa [restrict_compl_singleton] at hm
    apply memLp_two_inverse_radial_ball_and_energy_of_ae_ray hn (hG i) hR
      (hm.mono_measure Measure.restrict_le_self)
    intro ρ
    have h := hD ρ i
    rw [haeSphere] at h
    filter_upwards [h] with θ hθ
    have he := congrArg (fun z : Ambient q => ρ.val⁻¹ • z) hθ
    simpa only [G, smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul] using he
  have hinvLp : MemLp (fun x => ‖x‖⁻¹ • w x) 2
      (volume.restrict (ball (0 : Domain n) R)) := by
    apply (memLp_two_inverse_radial_ball_and_energy hn hvLp ?_ hR).1
    intro ρ θ
    have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    rw [hwRay, norm_smul, Real.norm_of_nonneg ρ.property.le, hθ, mul_one]
  have hW : MemW12 (ballDomain 0 R) w D :=
    ⟨hasWeakGradient_ball_of_punctured_and_integrable_inverse hnpos hP.1
      (hwLp.integrable (by norm_num))
      (fun i => (hDi i).1.integrable (by norm_num))
      (hinvLp.integrable (by norm_num)), hwLp, fun i => (hDi i).1⟩
  have hDI (i : Fin n) : Integrable (fun x => ‖D x i‖ ^ 2)
      (volume.restrict (ball (0 : Domain n) R)) :=
    (hDi i).1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hGI (i : Fin n) : Integrable (fun θ : sphere (0 : Domain n) 1 => ‖(G i) θ‖ ^ 2)
      (volume : Measure (Domain n)).toSphere :=
    (hG i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have henergy : (∫ x in ball (0 : Domain n) R, hsNormSq (D x)) =
      (R ^ (n - 2) / (n - 2)) *
        ∫ θ : sphere (0 : Domain n) 1, hsNormSq (fun i => (G i) θ)
          ∂Measure.euclideanHausdorffMeasure (n - 1) := by
    have hm := congrArg (fun μ : Measure (sphere (0 : Domain n) 1) =>
      ∫ θ, hsNormSq (fun i => (G i) θ) ∂μ) hσ
    rw [hm]
    simp only [hsNormSq]
    rw [integral_finsetSum _ (fun i _ => hDI i),
      integral_finsetSum _ (fun i _ => hGI i)]
    simp_rw [(hDi _).2]
    rw [Finset.mul_sum]
  refine ⟨w, D, hW, hwRay, hD,
    integrable_finsetSum Finset.univ (fun i _ => hDI i), henergy, ?_⟩
  intro P hvalues
  rw [hσ] at hvalues
  have hp := ae_polar_angle_of_ae_sphere hvalues
  have hp' : ∀ᵐ x ∂volume.restrict ({(0 : Domain n)}ᶜ), P (w x) := by
    apply (ae_restrict_iff_subtype (measurableSet_singleton (0 : Domain n)).compl).mpr
    filter_upwards [hp] with x hx
    let p := homeomorphUnitSphereProd (Domain n) x
    have he : p.2.val • p.1.val = x.val := by
      have he := congrArg (fun z : ({(0 : Domain n)}ᶜ : Set (Domain n)) => z.val)
        ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply x)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using he
    rw [← he, hwRay ⟨p.2.val, p.2.property⟩ p.1]
    exact hx
  rw [restrict_compl_singleton] at hp'
  exact ae_restrict_of_ae hp'

end StratificationTheory.Providers.SphereRadialBallExtension
