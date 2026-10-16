module

public import StratificationTheory.Foundation.SphereAEClasses
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.Analysis.SobolevAECongruence

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- Every actual radial representative on an open punctured neighborhood
has the same weak gradient as a global punctured radial representative. -/
theorem radial_representative_weakGradient_ae_eq {n q : ℕ}
    {v : sphere (0 : Domain n) 1 → Ambient q}
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    (hw : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w D)
    (hwray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w (ρ.val • θ.val) = v θ)
    (U : OpenDomain n) (h0 : (0 : Domain n) ∉ U.val)
    {z : Domain n → Ambient q} {Dz : Domain n → Gradient n q}
    (hz : HasWeakGradient U z Dz)
    (hzray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      ρ.val • θ.val ∈ U.val → z (ρ.val • θ.val) = v θ) :
    Dz =ᵐ[volume.restrict U.val] D := by
  have hsub : U.val ⊆ ({(0 : Domain n)}ᶜ : Set (Domain n)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    exact h0 (heq ▸ hx)
  have hwU : HasWeakGradient U w D := hw.1.mono hsub
  have hzw : z =ᵐ[volume.restrict U.val] w := by
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    let sx : ({(0 : Domain n)}ᶜ : Set (Domain n)) := ⟨x, hsub hx⟩
    let p := homeomorphUnitSphereProd (Domain n) sx
    have hp : p.2.val • p.1.val = x := by
      have he := congrArg (fun y : ({(0 : Domain n)}ᶜ : Set (Domain n)) => y.val)
        ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply sx)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using he
    have hzv := hzray ⟨p.2.val, p.2.property⟩ p.1 (hp ▸ hx)
    rw [← hp, hzv, hwray ⟨p.2.val, p.2.property⟩ p.1]
  exact hz.ae_eq_of_ae_eq_map hwU hzw

/-- Angular a.e. equality gives the corresponding reciprocal-radius
column formula on every actual open punctured neighborhood. -/
theorem radial_column_formula_of_angular_ae_eq {n q : ℕ}
    {A B : sphere (0 : Domain n) 1 → Gradient n q}
    (hAB : ∀ i : Fin n, (fun θ => A θ i) =ᵐ[(volume : Measure (Domain n)).toSphere]
      (fun θ => B θ i))
    {D : Domain n → Gradient n q}
    (hDray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i)
    (U : OpenDomain n) (h0 : (0 : Domain n) ∉ U.val) :
    ∀ᵐ x ∂volume.restrict U.val, ∀ hx : x ≠ 0, ∀ i : Fin n,
      D x i = ‖x‖⁻¹ • B ((homeomorphUnitSphereProd (Domain n)
        ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1) i := by
  have hAall : ∀ᵐ θ ∂(volume : Measure (Domain n)).toSphere, ∀ i : Fin n,
      A θ i = B θ i := ae_all_iff.mpr hAB
  have hp := ae_polar_angle_of_ae_sphere hAall
  have hp' : ∀ᵐ x ∂volume.restrict ({(0 : Domain n)}ᶜ), ∀ hx : x ≠ 0, ∀ i : Fin n,
      A ((homeomorphUnitSphereProd (Domain n)
        ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1) i =
      B ((homeomorphUnitSphereProd (Domain n)
        ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1) i := by
    apply (ae_restrict_iff_subtype (measurableSet_singleton (0 : Domain n)).compl).mpr
    filter_upwards [hp] with x hx
    intro _
    exact hx
  have hsub : U.val ⊆ ({(0 : Domain n)}ᶜ : Set (Domain n)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    exact h0 (heq ▸ hx)
  filter_upwards [hp'.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub)),
    ae_restrict_mem U.property.measurableSet] with x hx hU
  intro hx0 i
  let sx : ({(0 : Domain n)}ᶜ : Set (Domain n)) := ⟨x, hsub hU⟩
  let p := homeomorphUnitSphereProd (Domain n) sx
  have heq : p.2.val • p.1.val = x := by
    have h := congrArg (fun y : ({(0 : Domain n)}ᶜ : Set (Domain n)) => y.val)
      ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply sx)
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using h
  have hnorm : p.2.val = ‖x‖ := homeomorphUnitSphereProd_apply_snd_coe (Domain n) sx
  have hd := hDray ⟨p.2.val, p.2.property⟩ p.1 i
  rw [heq, hnorm] at hd
  exact hd.trans (congrArg (fun z : Ambient q => ‖x‖⁻¹ • z) (hx hx0 i))

end StratificationTheory
