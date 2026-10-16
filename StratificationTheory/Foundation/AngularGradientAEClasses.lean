module

public import StratificationTheory.Foundation.AngularGradientUniqueness
public import StratificationTheory.Foundation.SphereAEClasses

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- Surface-a.e. equal radial values determine volume-a.e. equal actual
radial representatives on the punctured domain. -/
theorem radial_representatives_ae_eq_of_angular_ae_eq {n q : ℕ}
    {v v' : sphere (0 : Domain n) 1 → Ambient q}
    (hvv' : v =ᵐ[(volume : Measure (Domain n)).toSphere] v')
    {w w' : Domain n → Ambient q}
    (hwray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w (ρ.val • θ.val) = v θ)
    (hw'ray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w' (ρ.val • θ.val) = v' θ) :
    w =ᵐ[volume.restrict ({(0 : Domain n)}ᶜ)] w' := by
  have hp := ae_polar_angle_of_ae_sphere hvv'
  apply (ae_restrict_iff_subtype (measurableSet_singleton (0 : Domain n)).compl).mpr
  filter_upwards [hp] with x hx
  let p := homeomorphUnitSphereProd (Domain n) x
  have heq : p.2.val • p.1.val = x.val := by
    have h := congrArg (fun y : ({(0 : Domain n)}ᶜ : Set (Domain n)) => y.val)
      ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply x)
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using h
  rw [← heq, hwray ⟨p.2.val, p.2.property⟩ p.1, hw'ray ⟨p.2.val, p.2.property⟩ p.1]
  exact hx

/-- Coherent weak gradients of radial representatives depend only on the
actual angular a.e. map class, not on exceptional sphere values. -/
theorem angular_radial_gradient_ae_eq_of_ae_values {n q : ℕ} (hn : 0 < n)
    {v v' : sphere (0 : Domain n) 1 → Ambient q}
    (hvv' : v =ᵐ[(volume : Measure (Domain n)).toSphere] v')
    {w w' : Domain n → Ambient q} {D D' : Domain n → Gradient n q}
    {A B : sphere (0 : Domain n) 1 → Gradient n q}
    (hw : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w D)
    (hw' : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w' D')
    (hwray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w (ρ.val • θ.val) = v θ)
    (hw'ray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w' (ρ.val • θ.val) = v' θ)
    (hDray : ∀ (ρ : PositiveRadius) (i : Fin n),
      (fun θ : sphere (0 : Domain n) 1 => D (ρ.val • θ.val) i) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • A θ i))
    (hD'ray : ∀ (ρ : PositiveRadius) (i : Fin n),
      (fun θ : sphere (0 : Domain n) 1 => D' (ρ.val • θ.val) i) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • B θ i)) :
    ∀ i : Fin n, (fun θ => A θ i) =ᵐ[(volume : Measure (Domain n)).toSphere]
      (fun θ => B θ i) := by
  have hww' := radial_representatives_ae_eq_of_angular_ae_eq hvv' hwray hw'ray
  have hw'' := hw'.congr_ae hww'.symm (Filter.EventuallyEq.refl _ _)
  exact angular_radial_gradient_ae_eq_of_ae_formula hn hw hw'' hwray hwray hDray hD'ray

end StratificationTheory
