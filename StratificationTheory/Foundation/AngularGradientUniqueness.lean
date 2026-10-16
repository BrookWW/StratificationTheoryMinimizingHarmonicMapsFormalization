module

public import StratificationTheory.Foundation.PolarAETransport
public import HarmonicMaps.Analysis.SobolevAECongruence

public section
open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- Coherent positive-ray fields of two weak gradients of the same radial
map determine the same angular almost-everywhere columns. -/
theorem angular_radial_gradient_ae_eq_of_ae_formula {n q : ℕ} (hn : 0 < n)
    {v : sphere (0 : Domain n) 1 → Ambient q}
    {w w' : Domain n → Ambient q} {D D' : Domain n → Gradient n q}
    {A B : sphere (0 : Domain n) 1 → Gradient n q}
    (hw : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w D)
    (hw' : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w' D')
    (hwray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w (ρ.val • θ.val) = v θ)
    (hw'ray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w' (ρ.val • θ.val) = v θ)
    (hDray : ∀ (ρ : PositiveRadius) (i : Fin n),
      (fun θ : sphere (0 : Domain n) 1 => D (ρ.val • θ.val) i) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • A θ i))
    (hD'ray : ∀ (ρ : PositiveRadius) (i : Fin n),
      (fun θ : sphere (0 : Domain n) 1 => D' (ρ.val • θ.val) i) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • B θ i)) :
    ∀ i : Fin n, (fun θ => A θ i) =ᵐ[(volume : Measure (Domain n)).toSphere]
      (fun θ => B θ i) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hww' : w =ᵐ[volume.restrict ({(0 : Domain n)}ᶜ)] w' := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : Domain n)).compl] with x hx
    let sx : ({(0 : Domain n)}ᶜ : Set (Domain n)) := ⟨x, hx⟩
    let p := homeomorphUnitSphereProd (Domain n) sx
    have hp : p.2.val • p.1.val = x := by
      have he := congrArg (fun z : ({(0 : Domain n)}ᶜ : Set (Domain n)) => z.val)
        ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply sx)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using he
    rw [← hp, hwray ⟨p.2.val, p.2.property⟩ p.1, hw'ray ⟨p.2.val, p.2.property⟩ p.1]
  have hDD' := hw.1.ae_eq_of_ae_eq_map hw'.1 hww'
  change D =ᵐ[volume.restrict ({(0 : Domain n)}ᶜ)] D' at hDD'
  rw [restrict_compl_singleton] at hDD'
  have hpolar := ae_polar_slice_of_ae_volume (n := n) (P := fun x => D x = D' x) hDD' 0
  have hsub : Ioo (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) := fun r hr => lt_trans (by norm_num : (0 : ℝ) < 1) hr.1
  have hi := hpolar.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  have hvol : (volume : Measure ℝ) (Ioo (1 : ℝ) 2) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨r, hr, hreq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hi
  have hrpos : 0 < r := by linarith [hr.1]
  intro i
  filter_upwards [hreq, hDray ⟨r, hrpos⟩ i, hD'ray ⟨r, hrpos⟩ i] with θ hθ hA hB
  simp only [zero_add] at hθ
  have heq := congrFun hθ i
  rw [hA, hB] at heq
  have heq' := congrArg (fun z : Ambient q => r • z) heq
  simpa only [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul] using heq'

/-- Coherent positive-ray fields of two weak gradients of the same radial
map determine the same angular almost-everywhere columns. -/
theorem angular_radial_gradient_ae_eq {n q : ℕ} (hn : 0 < n)
    {v : sphere (0 : Domain n) 1 → Ambient q}
    {w w' : Domain n → Ambient q} {D D' : Domain n → Gradient n q}
    {A B : sphere (0 : Domain n) 1 → Gradient n q}
    (hw : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w D)
    (hw' : MemW12Loc ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w' D')
    (hwray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w (ρ.val • θ.val) = v θ)
    (hw'ray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), w' (ρ.val • θ.val) = v θ)
    (hDray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i)
    (hD'ray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D' (ρ.val • θ.val) i = ρ.val⁻¹ • B θ i) :
    ∀ i : Fin n, (fun θ => A θ i) =ᵐ[(volume : Measure (Domain n)).toSphere]
      (fun θ => B θ i) := by
  apply angular_radial_gradient_ae_eq_of_ae_formula hn hw hw' hwray hw'ray
  · intro ρ i
    exact Filter.Eventually.of_forall fun θ => hDray ρ θ i
  · intro ρ i
    exact Filter.Eventually.of_forall fun θ => hD'ray ρ θ i

end StratificationTheory
