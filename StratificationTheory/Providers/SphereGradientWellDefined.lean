module

public import StratificationTheory.Foundation.SphereGradientData
public import StratificationTheory.Foundation.AngularGradientUniqueness
public import StratificationTheory.Foundation.RadialGradientCharacterization

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff BigOperators

namespace StratificationTheory.Providers.SphereGradientWellDefined

theorem result {n q : ℕ} (hn : 2 ≤ n)
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
              ⟨x, hx⟩).1) := by
  classical
  have hnpos : 0 < n := by omega
  have haeSphere : ae (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)) = ae (volume : Measure (Domain n)).toSphere :=
    congrArg ae (euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos)
  obtain ⟨w, D, A, hw, hwray, hA, hDray, hAtangent⟩ :=
    exists_sphere_radial_weak_gradient_data hn hv
  let G : Fin n → Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)) :=
    fun i => (hA i).toLp (fun θ => A θ i)
  have hGA (i : Fin n) : (fun θ => (G i) θ) =ᵐ[
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1))] (fun θ => A θ i) :=
    (hA i).coeFn_toLp
  have hAG (i : Fin n) : (fun θ => A θ i) =ᵐ[
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1))] (fun θ => (G i) θ) := (hGA i).symm
  have hAGvol (i : Fin n) : (fun θ => A θ i) =ᵐ[
      (volume : Measure (Domain n)).toSphere] (fun θ => (G i) θ) := by
    rw [← haeSphere]
    exact hAG i
  have hDGray (ρ : PositiveRadius) (i : Fin n) :
      (fun θ : sphere (0 : Domain n) 1 => D (ρ.val • θ.val) i) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • (G i) θ) := by
    filter_upwards [hAGvol i] with θ hθ
    rw [hDray ρ θ i, hθ]
  refine ⟨G, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨w, D, hw, hwray, ?_⟩
    intro ρ i
    filter_upwards [hAG i] with θ hθ
    rw [hDray ρ θ i, smul_smul, mul_inv_cancel₀ ρ.property.ne', one_smul, hθ]
  · have hall : ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)), ∀ i : Fin n, A θ i = (G i) θ :=
      ae_all_iff.mpr hAG
    filter_upwards [hall] with θ hθ
    simp_rw [← hθ]
    exact hAtangent θ
  · intro U _hSphere h0 z Dz hz hzray
    have hDz := radial_representative_weakGradient_ae_eq hw hwray U h0 hz.1 hzray
    have hD := radial_column_formula_of_angular_ae_eq
      (B := fun θ i => (G i) θ) hAGvol hDray U h0
    filter_upwards [hDz, hD] with x hx hformula
    intro hx0 i
    rw [congrFun hx i]
    exact hformula hx0 i
  · intro H hH
    obtain ⟨⟨wH, DH, hWH, hHray, hDHray⟩, _hTH, _hUH⟩ := hH
    have hDHformula (ρ : PositiveRadius) (i : Fin n) :
        (fun θ : sphere (0 : Domain n) 1 => DH (ρ.val • θ.val) i) =ᵐ[
          (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • (H i) θ) := by
      have hi : (fun θ : sphere (0 : Domain n) 1 => ρ.val • DH (ρ.val • θ.val) i)
          =ᵐ[(volume : Measure (Domain n)).toSphere] (fun θ => (H i) θ) := by
        rw [← haeSphere]
        exact hDHray ρ i
      filter_upwards [hi] with θ hθ
      have heq := congrArg (fun a : Ambient q => ρ.val⁻¹ • a) hθ
      simpa only [smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul] using heq
    have hGH := angular_radial_gradient_ae_eq_of_ae_formula hnpos
      (A := fun θ i => (G i) θ) (B := fun θ i => (H i) θ)
      hw hWH hwray hHray hDGray hDHformula
    funext i
    apply Lp.ext
    rw [haeSphere]
    exact (hGH i).symm

end StratificationTheory.Providers.SphereGradientWellDefined

