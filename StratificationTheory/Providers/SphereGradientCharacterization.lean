module

public import StratificationTheory.Frozen.SphereGradient
import StratificationTheory.Foundation.AngularGradientAEClasses

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped BigOperators
namespace StratificationTheory.Providers.SphereGradientCharacterization

private theorem coherent_native_gradient_classes_eq {n q : ℕ} (hn : 0 < n)
    {v v' : sphere (0 : Domain n) 1 → Ambient q}
    (hvv' : v =ᵐ[(Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1))] v')
    {w w' : Domain n → Ambient q} {D D' : Domain n → Gradient n q}
    {G H : Fin n → Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))}
    (hW : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w D)
    (hW' : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w' D')
    (hw : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w (ρ.val • θ.val) = v θ)
    (hw' : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w' (ρ.val • θ.val) = v' θ)
    (hDG : ∀ (ρ : PositiveRadius) (i : Fin n),
      (fun θ : sphere (0 : Domain n) 1 => ρ.val • D (ρ.val • θ.val) i) =ᵐ[
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))]
          (fun θ => (G i) θ))
    (hDH : ∀ (ρ : PositiveRadius) (i : Fin n),
      (fun θ : sphere (0 : Domain n) 1 => ρ.val • D' (ρ.val • θ.val) i) =ᵐ[
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))]
          (fun θ => (H i) θ)) : G = H := by
  have haeSphere : ae (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)) = ae (volume : Measure (Domain n)).toSphere :=
    congrArg ae (euclideanHausdorffMeasure_unitSphere_eq_toSphere hn)
  have hvvVol : v =ᵐ[(volume : Measure (Domain n)).toSphere] v' := by
    rw [← haeSphere]
    exact hvv'
  have hDFormula (ρ : PositiveRadius) (i : Fin n) :
      (fun θ : sphere (0 : Domain n) 1 => D (ρ.val • θ.val) i) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • (G i) θ) := by
    have h := hDG ρ i
    rw [haeSphere] at h
    filter_upwards [h] with θ hθ
    have heq := congrArg (fun z : Ambient q => ρ.val⁻¹ • z) hθ
    simpa only [smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul] using heq
  have hD'Formula (ρ : PositiveRadius) (i : Fin n) :
      (fun θ : sphere (0 : Domain n) 1 => D' (ρ.val • θ.val) i) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • (H i) θ) := by
    have h := hDH ρ i
    rw [haeSphere] at h
    filter_upwards [h] with θ hθ
    have heq := congrArg (fun z : Ambient q => ρ.val⁻¹ • z) hθ
    simpa only [smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul] using heq
  have hGH := angular_radial_gradient_ae_eq_of_ae_values hn hvvVol
    hW hW' hw hw' hDFormula hD'Formula
  funext i
  apply Lp.ext
  rw [haeSphere]
  exact hGH i

/-- Full characterization, coherent-carrier uniqueness and a.e. class invariance of one native gradient family. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
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
by
  have hnpos : 0 < n := by omega
  have hChosen : (∃ w : Domain n → Ambient q, ∃ D : Domain n → Gradient n q,
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
              ⟨x, hx⟩).1) :=
    Classical.choose_spec (sphere_gradient_existsUnique hn v hv).exists
  refine ⟨hChosen, ?_, ?_⟩
  · intro H hH
    obtain ⟨wH, DH, hWH, hwH, hDH⟩ := hH
    obtain ⟨w, D, hW, hw, hD⟩ := hChosen.1
    exact coherent_native_gradient_classes_eq hnpos (Filter.EventuallyEq.refl _ _)
      hWH hW hwH hw hDH hD
  · intro v' hv' hvv'
    have hChosen' := Classical.choose_spec (sphere_gradient_existsUnique hn v' hv').exists
    obtain ⟨w', D', hW', hw', hD'⟩ := hChosen'.1
    obtain ⟨w, D, hW, hw, hD⟩ := hChosen.1
    exact coherent_native_gradient_classes_eq hnpos hvv'.symm hW' hW hw' hw hD' hD

end StratificationTheory.Providers.SphereGradientCharacterization
