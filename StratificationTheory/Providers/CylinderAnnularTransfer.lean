module

public import StratificationTheory.Frozen.CylinderTraceCharacterization
public import StratificationTheory.Foundation.CylinderPointCoordinates
public import HarmonicMaps.Sobolev
import StratificationTheory.Interpolation.CylinderAnnularTransport
import StratificationTheory.Foundation.CylinderSobolevCollar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory.Providers.CylinderAnnularTransfer

/-- A full cylinder Sobolev map transfers to the actual annulus with its
original interior values and the same continuous native-L2 endpoint trace
curve under the radial affine parameter. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (ha : -1 < a) {s : ℝ} (hs : 0 < s)
    (c : Domain n) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) :
    let lo := s * (1 + a)
    let hi := s * (1 + b)
    let Ω : OpenDomain n := ⟨{x | lo < ‖x - c‖ ∧ ‖x - c‖ < hi},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let τ : C(Icc lo hi, Icc a b) :=
      ⟨fun r => ⟨r.val / s - 1, by
        constructor
        · have h : a + 1 ≤ r.val / s := (le_div_iff₀ hs).mpr (by
            have hr := r.property.1
            dsimp only [lo] at hr
            nlinarith only [hr])
          linarith only [h]
        · have h : r.val / s ≤ b + 1 := (div_le_iff₀ hs).mpr (by
            have hr := r.property.2
            dsimp only [hi] at hr
            nlinarith only [hr])
          linarith only [h]⟩,
        by
          apply Continuous.subtype_mk
          exact (continuous_subtype_val.div_const s).sub (continuous_const (y := (1 : ℝ)))⟩
    let K := (cylinderTrace hn hab v hv).comp τ
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃ W : Domain n → Ambient q, ∃ DW : Domain n → Gradient n q,
      MemW12 Ω W DW ∧
      (∀ (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b),
        W (c + (s * (1 + t)) • θ.val) =
          v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
            unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩) ∧
      ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo lo hi,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => W (c + r • θ.val)) 2 σ,
          K ⟨r, hr.1.le, hr.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => W (c + r • θ.val)) := by
  intro lo hi Ω e τ K σ
  obtain ⟨_hLv, δ, hδ, hδsmall, U, hU, _hSphere, _hzero, w, Dw, hw, hraw⟩ :=
    (memCylinderW12_iff_exists_radial_collar hn hab v).mp hv
  let Γ : OpenDomain (n + 1) := ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
    (U.property.preimage e.continuous.fst).inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp e.continuous.snd))⟩
  have hwΓ : MemW12 Γ w Dw := hw
  have hΓ : Γ.val = {y : Domain (n + 1) |
      (1 - δ < ‖(e y).1‖ ∧ ‖(e y).1‖ < 1 + δ) ∧ (e y).2 0 ∈ Ioo a b} := by
    change {y : Domain (n + 1) | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b} = _
    rw [hU]
    rfl
  let η := (Measure.volumeIoiPow (n - 1)).restrict
    {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
  let P := (η univ)⁻¹ • η
  obtain ⟨hP, β, hβ, hcβ, hsβ, _hβnonneg, hβmass⟩ := exists_normalized_smooth_radial_weight (n := n) hδ
  letI : IsProbabilityMeasure P := hP
  let W₀ := annularAveragedMap s β P w
  let DW₀ := annularAveragedColumns s β P Dw
  let Ω₀ : OpenDomain n := ⟨{x : Domain n | lo < ‖x‖ ∧ ‖x‖ < hi},
    isOpen_Ioo.preimage continuous_norm⟩
  have hW₀ : MemW12 Ω₀ W₀ DW₀ := memW12_annularAveragedMap hn hab ha hs hwΓ hδ hδsmall hΓ hβ hcβ hsβ
  have hfinite : volume Ω₀.val ≠ ⊤ := by
    have hballfinite : volume (ball (0 : Domain n) hi) ≠ ⊤ := measure_ball_ne_top
    apply ne_top_of_le_ne_top hballfinite
    apply measure_mono
    intro x hx
    rw [mem_ball, dist_zero_right]
    exact hx.2
  let W : Domain n → Ambient q := fun x => W₀ (x - c)
  let DW : Domain n → Gradient n q := fun x i => DW₀ (x - c) i
  have hW : MemW12 Ω W DW := memW12_translate_finite_openDomain hW₀ hfinite c
  have hAEρ : ∀ᵐ ρ ∂P, 1 - δ < ρ.val ∧ ρ.val < 1 + δ :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem
      ((isOpen_Ioo.preimage continuous_subtype_val).measurableSet))
  have hRaw₀ (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b) :
      W₀ ((s * (1 + t)) • θ.val) =
        v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
          unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩ := by
    let cv : unitCylinder n a b :=
      ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
        unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩
    have hsp : (e cv.val).1 = θ.val := by simp only [cv, e.apply_symm_apply]
    have htm : (e cv.val).2 = EuclideanSpace.single (0 : Fin 1) t := by
      simp only [cv, e.apply_symm_apply]
    have hct : (e cv.val).2 0 ∈ Ioo a b := by
      rw [htm]
      simpa only [EuclideanSpace.single, PiLp.single_apply, ite_true] using ht
    have havg : (fun ρ : Ioi (0 : ℝ) => β ρ.val • w
        (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t))) =ᵐ[P]
        (fun ρ => β ρ.val • v cv) := by
      filter_upwards [hAEρ] with ρ hρ
      have hpoint : ρ.val • (e cv.val).1 ∈ U.val := by
        rw [hsp, hU]
        have hnorm : ‖ρ.val • θ.val‖ = ρ.val := by
          rw [norm_smul, Real.norm_of_nonneg ρ.property.le,
            mem_sphere_zero_iff_norm.mp θ.property, mul_one]
        simpa only [mem_setOf_eq, hnorm] using hρ
      have hray := hraw ρ cv hct hpoint
      change w (e.symm (ρ.val • (e cv.val).1, (e cv.val).2)) = v cv at hray
      rw [hsp, htm] at hray
      exact congrArg (fun z : Ambient q => β ρ.val • z) hray
    change annularAveragedMap s β P w ((s * (1 + t)) • θ.val) = v cv
    rw [annularAveragedMap_param hs (ha.trans ht.1) β P w θ, integral_congr_ae havg,
      integral_smul_const, hβmass, one_smul]
  have hRaw (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b) :
      W (c + (s * (1 + t)) • θ.val) =
        v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
          unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩ := by
    change W₀ ((c + (s * (1 + t)) • θ.val) - c) = _
    rw [add_sub_cancel_left]
    exact hRaw₀ θ t ht
  refine ⟨W, DW, hW, hRaw, ?_⟩
  have htrace := (cylinderTrace_characterization hn hab v hv).1
  have hQ : Measure.QuasiMeasurePreserving (fun r : ℝ => r / s - 1) volume volume := by
    have h := (measurePreserving_sub_right (volume : Measure ℝ) (1 : ℝ)).quasiMeasurePreserving.comp
      ((volume : Measure ℝ).quasiMeasurePreserving_smul (r := s⁻¹) (inv_ne_zero hs.ne'))
    simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  have htraceR := hQ.ae htrace
  filter_upwards [htraceR] with r hr hrI
  let t := r / s - 1
  have ht : t ∈ Ioo a b := by
    have hlow : a + 1 < r / s := (lt_div_iff₀ hs).mpr (by
      have h := hrI.1
      dsimp only [lo] at h
      nlinarith only [h])
    have hhigh : r / s < b + 1 := (div_lt_iff₀ hs).mpr (by
      have h := hrI.2
      dsimp only [hi] at h
      nlinarith only [h])
    constructor <;> dsimp only [t] <;> linarith only [hlow, hhigh]
  obtain ⟨hL, hCurve⟩ := hr ht
  have hradius : s * (1 + t) = r := by
    dsimp only [t]
    field_simp
    ring
  have hfun : (fun θ : sphere (0 : Domain n) 1 => W (c + r • θ.val)) =
      (fun θ : sphere (0 : Domain n) 1 =>
        v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
          unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩) := by
    funext θ
    rw [← hradius]
    exact hRaw θ t ht
  have hLW : MemLp (fun θ : sphere (0 : Domain n) 1 => W (c + r • θ.val)) 2 σ := by
    rw [hfun]
    exact hL
  refine ⟨hLW, ?_⟩
  change cylinderTrace hn hab v hv (τ ⟨r, hrI.1.le, hrI.2.le⟩) = hLW.toLp _
  have hτ : τ ⟨r, hrI.1.le, hrI.2.le⟩ = (⟨t, ht.1.le, ht.2.le⟩ : Icc a b) := by
    apply Subtype.ext
    rfl
  rw [hτ, hCurve]
  exact hL.toLp_congr hLW (Eventually.of_forall fun θ => congrFun hfun.symm θ)

end StratificationTheory.Providers.CylinderAnnularTransfer
