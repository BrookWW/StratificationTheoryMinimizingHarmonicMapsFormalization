module

public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.SobolevRestriction

public section

open HarmonicMaps MeasureTheory Set Filter

namespace StratificationTheory

/-- Actual weak-gradient uniqueness on an a.e. open cover identifies the
columns of a locally constructed graph with one prescribed ambient field. -/
theorem memW12_same_gradient_of_open_cover {n q : ℕ} {I : Type*} [Countable I]
    {Ω : OpenDomain n} (C : I → OpenDomain n)
    {w : Domain n → Ambient q} {D E : Domain n → Gradient n q}
    (hcover : ∀ᵐ x ∂volume.restrict Ω.val, ∃ j : I, x ∈ (C j).val)
    (hC : ∀ j : I, HasWeakGradient (C j) w D)
    (hE : MemW12 Ω w E) : MemW12 Ω w D := by
  have hEach (j : I) : ∀ᵐ x : Domain n ∂volume,
      x ∈ Ω.val → x ∈ (C j).val → E x = D x := by
    let V : OpenDomain n := ⟨Ω.val ∩ (C j).val, Ω.property.inter (C j).property⟩
    have hEV : HasWeakGradient V w E := hE.1.mono (show V.val ⊆ Ω.val from fun _ hx => hx.1)
    have hDV : HasWeakGradient V w D := (hC j).mono (show V.val ⊆ (C j).val from fun _ hx => hx.2)
    have hEq : E =ᵐ[volume.restrict V.val] D := hEV.ae_eq hDV
    have hImp := (ae_restrict_iff' V.property.measurableSet).mp hEq
    filter_upwards [hImp] with x hx hxΩ hxC
    exact hx ⟨hxΩ, hxC⟩
  apply hE.congr_ae (EventuallyEq.refl _ _)
  filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr hEach), hcover,
    ae_restrict_mem Ω.property.measurableSet] with x hx hcov hxΩ
  obtain ⟨j, hj⟩ := hcov
  exact hx j hxΩ hj

end StratificationTheory
