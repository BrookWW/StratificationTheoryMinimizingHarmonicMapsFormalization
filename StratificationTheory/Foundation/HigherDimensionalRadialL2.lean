module

public import StratificationTheory.Foundation.RadialL2Transfer
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Square integrability of reciprocal-radius extensions

In dimension at least three, the radial Jacobian cancels the square of the
reciprocal radius. The resulting finite factor is `R^(n-2)/(n-2)`.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators

namespace StratificationTheory

private theorem ae_eq_of_ae_ae_eq {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] [NormedAddCommGroup E]
    {f g : α × β → E} (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f (x, y) = g (x, y)) :
    f =ᵐ[μ.prod ν] g := by
  have hset : MeasurableSet {x | hf.mk f x = hg.mk g x} := by
    have hm := measurableSet_eq_fun
      (hf.stronglyMeasurable_mk.sub hg.stronglyMeasurable_mk).norm.measurable
      (measurable_const (a := (0 : ℝ)))
    simpa only [Pi.sub_apply, norm_eq_zero, sub_eq_zero] using hm
  have hm : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk, h] with x hfx hgx hx
    filter_upwards [hfx, hgx, hx] with y hfy hgy hxy
    exact hfy.symm.trans (hxy.trans hgy)
  exact hf.ae_eq_mk.trans (hm.trans hg.ae_eq_mk.symm)

/-- For measurable maps, native angular a.e. equality at every positive
radius gives Euclidean a.e. equality on a finite ball. -/
theorem ae_eq_radial_ball_of_ae_rays {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E]
    {w z : Domain n → E} {R : ℝ} (hR : 0 < R)
    (hw : AEStronglyMeasurable w (volume.restrict (ball (0 : Domain n) R)))
    (hz : AEStronglyMeasurable z (volume.restrict (ball (0 : Domain n) R)))
    (hRay : ∀ ρ : PositiveRadius,
      (fun θ : sphere (0 : Domain n) 1 => w (ρ.val • θ.val)) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => z (ρ.val • θ.val))) :
    w =ᵐ[volume.restrict (ball (0 : Domain n) R)] z := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let X := ({(0 : Domain n)}ᶜ : Set (Domain n))
  let σ := (volume : Measure (Domain n)).toSphere
  let νR := (Measure.volumeIoiPow (n - 1)).restrict
    (Iio (⟨R, hR⟩ : Ioi (0 : ℝ)))
  letI : IsFiniteMeasure νR := ⟨by
    dsimp only [νR]
    rw [Measure.restrict_apply_univ, Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top⟩
  let H := homeomorphUnitSphereProd (Domain n)
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hm
  have hmR := hm.restrict_preimage (MeasurableSet.univ.prod (measurableSet_Iio
    (a := (⟨R, hR⟩ : Ioi (0 : ℝ)))))
  have hpre : H ⁻¹' (univ ×ˢ Iio (⟨R, hR⟩ : Ioi (0 : ℝ))) =
      (Subtype.val : X → Domain n) ⁻¹' ball 0 R := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_Iio,
      mem_ball, dist_zero_right]
    change ((H x).2.val < R) ↔ ‖x.val‖ < R
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  rw [hpre, ← Measure.prod_restrict] at hmR
  simp only [Measure.restrict_univ] at hmR
  have hc := (measurePreserving_subtype_coe
    ((measurableSet_singleton (0 : Domain n)).compl) (μa := volume)).restrict_preimage
      (measurableSet_ball (x := (0 : Domain n)) (ε := R))
  rw [restrict_compl_singleton] at hc
  have hws := hw.comp_measurePreserving hc
  have hzs := hz.comp_measurePreserving hc
  have hwi := hws.comp_measurePreserving (MeasurePreserving.symm H.toMeasurableEquiv hmR)
  have hzi := hzs.comp_measurePreserving (MeasurePreserving.symm H.toMeasurableEquiv hmR)
  have hwSwap := hwi.comp_measurePreserving (Measure.measurePreserving_swap (μ := νR) (ν := σ))
  have hzSwap := hzi.comp_measurePreserving (Measure.measurePreserving_swap (μ := νR) (ν := σ))
  have heqSwap := ae_eq_of_ae_ae_eq hwSwap hzSwap
    (Eventually.of_forall fun ρ : Ioi (0 : ℝ) => by
      simpa only [Function.comp_def, Prod.swap_prod_mk,
        Homeomorph.toMeasurableEquiv_symm_coe, H, σ, Filter.EventuallyEq,
        homeomorphUnitSphereProd_symm_apply_coe] using hRay ⟨ρ.val, ρ.property⟩)
  have heqProd := (Measure.measurePreserving_swap (μ := σ) (ν := νR)).quasiMeasurePreserving.ae
    heqSwap
  have heqSub := hmR.quasiMeasurePreserving.ae heqProd
  have heqSub' : (fun x : X => w x.val) =ᵐ[
      ((volume : Measure (Domain n)).comap (Subtype.val : X → Domain n)).restrict
        ((Subtype.val : X → Domain n) ⁻¹' ball 0 R)] (fun x => z x.val) := by
    simpa only [Function.comp_def, Prod.swap_swap, Homeomorph.toMeasurableEquiv_symm_coe,
      H, X, σ, νR, Filter.EventuallyEq, Homeomorph.symm_apply_apply] using heqSub
  rw [← hc.map_eq]
  exact (MeasurableEmbedding.subtype_coe
    ((measurableSet_singleton (0 : Domain n)).compl)).ae_map_iff.mpr heqSub'

private theorem radial_jacobian_inv_sq {n : ℕ} (hn : 3 ≤ n)
    (ρ : Ioi (0 : ℝ)) :
    ρ.val ^ (n - 1) * (ρ.val⁻¹) ^ 2 = ρ.val ^ (n - 3) := by
  have he : n - 1 = (n - 3) + 2 := by omega
  rw [he, pow_add]
  field_simp [(show 0 < ρ.val from ρ.property).ne']

private theorem integrable_inv_sq_volumeIoiPow {n : ℕ} (hn : 3 ≤ n)
    {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun ρ : Ioi (0 : ℝ) => (ρ.val⁻¹) ^ 2)
      (Iio (⟨R, hR⟩ : Ioi (0 : ℝ))) (Measure.volumeIoiPow (n - 1)) := by
  rw [IntegrableOn, Measure.volumeIoiPow,
    restrict_withDensity measurableSet_Iio,
    integrable_withDensity_iff_integrable_smul']
  · have hi : IntegrableOn (fun r : ℝ => r ^ (n - 3)) (Ioo 0 R) volume :=
      (intervalIntegral.intervalIntegrable_pow (n - 3)).1.mono_set Ioo_subset_Ioc_self
    have hs : IntegrableOn (fun ρ : Ioi (0 : ℝ) => ρ.val ^ (n - 3))
        (Iio (⟨R, hR⟩ : Ioi (0 : ℝ))) (Measure.comap Subtype.val volume) := by
      have hs := (MeasurableEmbedding.subtype_coe measurableSet_Ioi).integrableOn_iff_comap
        (f := fun r : ℝ => r ^ (n - 3))
        (μ := volume)
        (show Ioo 0 R ⊆ Set.range (Subtype.val : Ioi (0 : ℝ) → ℝ) by
          rw [Subtype.range_val]; exact Ioo_subset_Ioi_self)
      have he : (Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo 0 R =
          Iio (⟨R, hR⟩ : Ioi (0 : ℝ)) := by
        ext ρ
        exact and_iff_right ρ.property
      rw [he] at hs
      exact hs.mp hi
    apply hs.congr
    exact Eventually.of_forall fun ρ => by
      dsimp only
      rw [ENNReal.toReal_ofReal (pow_nonneg ρ.property.le _), smul_eq_mul,
        radial_jacobian_inv_sq hn ρ]
  · fun_prop
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem integral_inv_sq_volumeIoiPow {n : ℕ} (hn : 3 ≤ n)
    {R : ℝ} (hR : 0 < R) :
    (∫ ρ : Ioi (0 : ℝ) in Iio (⟨R, hR⟩ : Ioi (0 : ℝ)),
      (ρ.val⁻¹) ^ 2 ∂Measure.volumeIoiPow (n - 1)) =
      R ^ (n - 2) / (n - 2) := by
  rw [Measure.volumeIoiPow,
    setIntegral_withDensity_eq_setIntegral_toReal_smul
      (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
      _ measurableSet_Iio]
  have heq (ρ : Ioi (0 : ℝ)) :
      (ENNReal.ofReal (ρ.val ^ (n - 1))).toReal • (ρ.val⁻¹) ^ 2 =
        ρ.val ^ (n - 3) := by
    rw [ENNReal.toReal_ofReal (pow_nonneg ρ.property.le _), smul_eq_mul,
      radial_jacobian_inv_sq hn]
  simp_rw [heq]
  have he : (Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo 0 R =
      Iio (⟨R, hR⟩ : Ioi (0 : ℝ)) := by
    ext ρ
    exact and_iff_right ρ.property
  rw [← he, ← (MeasurableEmbedding.subtype_coe measurableSet_Ioi).setIntegral_map
      (fun r : ℝ => r ^ (n - 3)) (Ioo 0 R),
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).map_comap,
    Subtype.range_val, Measure.restrict_restrict_of_subset Ioo_subset_Ioi_self,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le,
    integral_pow]
  have he' : n - 3 + 1 = n - 2 := by omega
  rw [he', zero_pow (by omega : n - 2 ≠ 0), sub_zero]
  congr 1
  have hnreal : (n - 3 : ℕ) + 1 = (n : ℝ) - 2 := by
    have h : n = (n - 3) + 3 := by omega
    rw [h]
    push_cast
    ring
  exact hnreal

/-- In dimension at least three, reciprocal-radius angular data have actual
Euclidean L2 membership through the center and the exact energy factor. -/
theorem memLp_two_inverse_radial_ball_and_energy {n : ℕ} (hn : 3 ≤ n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : sphere (0 : Domain n) 1 → E}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    {W : Domain n → E}
    (hRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      W (ρ.val • θ.val) = ρ.val⁻¹ • v θ)
    {R : ℝ} (hR : 0 < R) :
    MemLp W 2 (volume.restrict (ball (0 : Domain n) R)) ∧
      (∫ x in ball (0 : Domain n) R, ‖W x‖ ^ 2) =
        (R ^ (n - 2) / (n - 2)) *
          ∫ θ : sphere (0 : Domain n) 1, ‖v θ‖ ^ 2
            ∂(volume : Measure (Domain n)).toSphere := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let X := ({(0 : Domain n)}ᶜ : Set (Domain n))
  let σ := (volume : Measure (Domain n)).toSphere
  let ν := Measure.volumeIoiPow (n - 1)
  let J := Iio (⟨R, hR⟩ : Ioi (0 : ℝ))
  let νR := ν.restrict J
  letI : IsFiniteMeasure νR := ⟨by
    dsimp only [νR, ν, J]
    rw [Measure.restrict_apply_univ, Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top⟩
  let F : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) → E := fun p =>
    p.2.val⁻¹ • v p.1
  have hρ : Integrable (fun ρ : Ioi (0 : ℝ) => (ρ.val⁻¹) ^ 2) νR :=
    integrable_inv_sq_volumeIoiPow hn hR
  have hsq : Integrable (fun p => ‖F p‖ ^ 2) (σ.prod νR) := by
    have hi := (hv.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).mul_prod hρ
    apply hi.congr
    exact Eventually.of_forall fun p => by
      simp only [F, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      exact mul_comm _ _
  have hmF : AEStronglyMeasurable F (σ.prod νR) :=
    ((by fun_prop : Measurable (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      p.2.val⁻¹)).aestronglyMeasurable).smul hv.aestronglyMeasurable.comp_fst
  have hprod : MemLp F 2 (σ.prod νR) :=
    (memLp_two_iff_integrable_sq_norm hmF).mpr hsq
  have henergy : (∫ p, ‖F p‖ ^ 2 ∂σ.prod νR) =
      (R ^ (n - 2) / (n - 2)) * ∫ θ, ‖v θ‖ ^ 2 ∂σ := by
    simp only [F, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp_rw [mul_comm ((_)⁻¹ ^ 2)]
    rw [integral_prod_mul (fun θ => ‖v θ‖ ^ 2)
      (fun ρ : Ioi (0 : ℝ) => (ρ.val⁻¹) ^ 2),
      integral_inv_sq_volumeIoiPow hn hR, mul_comm]
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hm
  have hmR := hm.restrict_preimage (MeasurableSet.univ.prod (measurableSet_Iio
    (a := (⟨R, hR⟩ : Ioi (0 : ℝ)))))
  have hpre : (homeomorphUnitSphereProd (Domain n)) ⁻¹'
      (univ ×ˢ J) = (Subtype.val : X → Domain n) ⁻¹' ball 0 R := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, true_and, J, mem_Iio,
      mem_ball, dist_zero_right]
    change ((homeomorphUnitSphereProd (Domain n) x).2.val < R) ↔ ‖x.val‖ < R
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  rw [hpre, ← Measure.prod_restrict] at hmR
  simp only [Measure.restrict_univ] at hmR
  have heq : (fun x : X => W x.val) = F ∘ homeomorphUnitSphereProd (Domain n) := by
    funext x
    let p := homeomorphUnitSphereProd (Domain n) x
    have hp : p.2.val • p.1.val = x.val := by
      have he := congrArg (fun z : X => z.val)
        ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply x)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using he
    change W x.val = p.2.val⁻¹ • v p.1
    rw [← hp]
    exact hRay ⟨p.2.val, p.2.property⟩ p.1
  have hsub : MemLp (fun x : X => W x.val) 2
      ((volume : Measure (Domain n)).comap (Subtype.val : X → Domain n) |>.restrict
        ((Subtype.val : X → Domain n) ⁻¹' ball 0 R)) := by
    rw [heq]
    exact hprod.comp_measurePreserving hmR
  have hc := (measurePreserving_subtype_coe
    ((measurableSet_singleton (0 : Domain n)).compl) (μa := volume)).restrict_preimage
      (measurableSet_ball (x := (0 : Domain n)) (ε := R))
  rw [restrict_compl_singleton] at hc
  have hW : MemLp W 2 (volume.restrict (ball (0 : Domain n) R)) := by
    rw [← hc.map_eq]
    exact (MeasurableEmbedding.subtype_coe
      ((measurableSet_singleton (0 : Domain n)).compl)).memLp_map_measure_iff.mpr hsub
  refine ⟨hW, ?_⟩
  calc
    (∫ x in ball (0 : Domain n) R, ‖W x‖ ^ 2) =
        ∫ x : X, ‖W x.val‖ ^ 2
          ∂((volume : Measure (Domain n)).comap (Subtype.val : X → Domain n) |>.restrict
            ((Subtype.val : X → Domain n) ⁻¹' ball 0 R)) :=
      (hc.integral_comp (MeasurableEmbedding.subtype_coe
        ((measurableSet_singleton (0 : Domain n)).compl)) (fun x => ‖W x‖ ^ 2)).symm
    _ = ∫ p, ‖F p‖ ^ 2 ∂σ.prod νR := by
      have hnorm : (fun x : X => ‖W x.val‖ ^ 2) =
          (fun p => ‖F p‖ ^ 2) ∘ homeomorphUnitSphereProd (Domain n) := by
        funext x
        rw [congrFun heq x]
        rfl
      rw [hnorm]
      exact hmR.integral_comp (Homeomorph.measurableEmbedding _) (fun p => ‖F p‖ ^ 2)
    _ = _ := henergy

/-- The exact reciprocal-radius energy identity also applies to a measurable
representative whose ray formulas hold only angular almost everywhere. -/
theorem memLp_two_inverse_radial_ball_and_energy_of_ae_ray {n : ℕ} (hn : 3 ≤ n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : sphere (0 : Domain n) 1 → E}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    {W : Domain n → E} {R : ℝ} (hR : 0 < R)
    (hW : AEStronglyMeasurable W (volume.restrict (ball (0 : Domain n) R)))
    (hRay : ∀ ρ : PositiveRadius,
      (fun θ : sphere (0 : Domain n) 1 => W (ρ.val • θ.val)) =ᵐ[
        (volume : Measure (Domain n)).toSphere] (fun θ => ρ.val⁻¹ • v θ)) :
    MemLp W 2 (volume.restrict (ball (0 : Domain n) R)) ∧
      (∫ x in ball (0 : Domain n) R, ‖W x‖ ^ 2) =
        (R ^ (n - 2) / (n - 2)) *
          ∫ θ : sphere (0 : Domain n) 1, ‖v θ‖ ^ 2
            ∂(volume : Measure (Domain n)).toSphere := by
  classical
  let z : Domain n → E := fun x => if hx : x ≠ 0 then
    ‖x‖⁻¹ • v ((homeomorphUnitSphereProd (Domain n)
      ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1) else 0
  have hzRay (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) :
      z (ρ.val • θ.val) = ρ.val⁻¹ • v θ := by
    have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    have hnorm : ‖ρ.val • θ.val‖ = ρ.val := by
      rw [norm_smul, Real.norm_of_nonneg ρ.property.le, hθ, mul_one]
    have hx0 : ρ.val • θ.val ≠ 0 := by
      intro hz
      have hz' := congrArg norm hz
      rw [hnorm, norm_zero] at hz'
      exact ρ.property.ne' hz'
    let p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) := (θ, ⟨ρ.val, ρ.property⟩)
    have hs : (⟨ρ.val • θ.val,
        by simpa only [mem_compl_iff, mem_singleton_iff] using hx0⟩ :
        ({(0 : Domain n)}ᶜ : Set (Domain n))) =
        (homeomorphUnitSphereProd (Domain n)).symm p := by
      apply Subtype.ext
      simp only [homeomorphUnitSphereProd_symm_apply_coe, p]
    simp only [z, dif_pos hx0, hnorm, hs, Homeomorph.apply_symm_apply, p]
  obtain ⟨hz, henergy⟩ := memLp_two_inverse_radial_ball_and_energy hn hv hzRay hR
  have heq : W =ᵐ[volume.restrict (ball (0 : Domain n) R)] z :=
    ae_eq_radial_ball_of_ae_rays (by omega) hR hW hz.aestronglyMeasurable
      (fun ρ => by simpa only [hzRay] using hRay ρ)
  refine ⟨hz.ae_eq heq.symm, ?_⟩
  calc
    _ = ∫ x in ball (0 : Domain n) R, ‖z x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ = _ := henergy

end StratificationTheory
