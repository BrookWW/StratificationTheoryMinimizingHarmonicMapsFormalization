module

public import StratificationTheory.Interpolation.CubicalEdgeInterpolationGraph
public import StratificationTheory.Interpolation.LinearCylinderEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Native energy of the affine interpolation over an edge

Product integration gives the spatial coefficient one half of the time
length and the exact reciprocal-length discrepancy energy for the time
column of the same explicit weak graph.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- The displayed rectangular gradient has finite native quadratic energy.
The total estimate and exact time-column energy use the original line data. -/
theorem interval_pair_rectangle_gradient_energy {q : ℕ}
    {a b c d : ℝ} (hcd : c < d)
    {F G f h g k : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hk : MemLp k 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo a b)] h) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let α : Domain 2 → ℝ := fun y => ((e y).2 0 - c) / (d - c)
    let Ω := {y : Domain 2 | (e y).1 0 ∈ Ioo a b ∧ (e y).2 0 ∈ Ioo c d}
    let DW : Domain 2 → Gradient 2 q := fun y =>
      Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
        (fun _ : Fin 1 => (1 - α y) • g ((e y).1 0) + α y • k ((e y).1 0))
        (fun _ : Fin 1 => (d - c)⁻¹ • (G ((e y).1 0) - F ((e y).1 0)))
    Integrable (fun y => hsNormSq (DW y)) (volume.restrict Ω) ∧
    (∫ y in Ω, hsNormSq (DW y)) ≤
      ((d - c) / 2) * ((∫ s in Ioo a b, ‖g s‖ ^ 2) + ∫ s in Ioo a b, ‖k s‖ ^ 2) +
      (d - c)⁻¹ * ∫ s in Ioo a b, ‖f s - h s‖ ^ 2 ∧
    (∫ y in Ω, ‖DW y (Fin.natAdd 1 (0 : Fin 1))‖ ^ 2) =
      (d - c)⁻¹ * ∫ s in Ioo a b, ‖f s - h s‖ ^ 2 := by
  intro e α Ω DW
  let S := {x : Domain 1 | x 0 ∈ Ioo a b}
  let μ := (volume : Measure (Domain 1)).restrict S
  let ν := (volume : Measure ℝ).restrict (Icc c d)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let C := e.trans (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Domain 1)) τ)
  have hS : MeasurableSet S := measurableSet_Ioo.preimage
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable
  have hm := measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := a) (b := b))
  have hF : MemLp (fun x : Domain 1 => F (x 0)) 2 μ :=
    (hf.ae_eq hFae.symm).comp_measurePreserving hm
  have hG : MemLp (fun x : Domain 1 => G (x 0)) 2 μ :=
    (hh.ae_eq hGae.symm).comp_measurePreserving hm
  have hg1 : MemLp (fun x : Domain 1 => g (x 0)) 2 μ := hg.comp_measurePreserving hm
  have hk1 : MemLp (fun x : Domain 1 => k (x 0)) 2 μ := hk.comp_measurePreserving hm
  have hC0 : MeasurePreserving C volume ((volume : Measure (Domain 1)).prod volume) :=
    measurePreserving_cylinder_coordinates 1
  have hC := hC0.restrict_preimage (hS.prod (measurableSet_Ioo (a := c) (b := d)))
  rw [← Measure.prod_restrict] at hC
  change MeasurePreserving C (volume.restrict Ω)
    (μ.prod (volume.restrict (Ioo c d))) at hC
  have hν : (volume : Measure ℝ).restrict (Ioo c d) = ν :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [hν] at hC
  let A : Domain 1 × ℝ → ℝ := fun p =>
    ‖(1 - (p.2 - c) / (d - c)) • g (p.1 0) + ((p.2 - c) / (d - c)) • k (p.1 0)‖ ^ 2
  let T : Domain 1 × ℝ → ℝ := fun p => ‖(d - c)⁻¹ • (G (p.1 0) - F (p.1 0))‖ ^ 2
  obtain ⟨hAI, hAE⟩ := affine_field_integrable_energy_le μ hcd hg1 hk1
  obtain ⟨hTI, hTE⟩ := constant_time_difference_integrable_energy μ hcd hF hG
  have hAN : Integrable (fun y => A (C y)) (volume.restrict Ω) :=
    hC.integrable_comp_of_integrable hAI
  have hTN : Integrable (fun y => T (C y)) (volume.restrict Ω) :=
    hC.integrable_comp_of_integrable hTI
  have hAt := hC.integral_comp C.toHomeomorph.measurableEmbedding A
  have hTt := hC.integral_comp C.toHomeomorph.measurableEmbedding T
  have hsp : (∫ y in Ω, A (C y)) ≤
      ((d - c) / 2) * ((∫ s in Ioo a b, ‖g s‖ ^ 2) + ∫ s in Ioo a b, ‖k s‖ ^ 2) := by
    rw [hAt]
    dsimp only [μ, S] at hAE
    rw [integral_domainOne_interval a b (fun s => ‖g s‖ ^ 2),
      integral_domainOne_interval a b (fun s => ‖k s‖ ^ 2)] at hAE
    exact hAE
  have htime : (∫ y in Ω, T (C y)) =
      (d - c)⁻¹ * ∫ s in Ioo a b, ‖f s - h s‖ ^ 2 := by
    rw [hTt, hTE]
    change (d - c)⁻¹ * (∫ x : Domain 1 in {x | x 0 ∈ Ioo a b},
      ‖G (x 0) - F (x 0)‖ ^ 2) = _
    rw [integral_domainOne_interval a b (fun s => ‖G s - F s‖ ^ 2)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hFae, hGae] with s hsF hsG
    rw [hsF, hsG, norm_sub_rev]
  have hsum (y : Domain 2) : hsNormSq (DW y) = A (C y) + T (C y) := by
    simp only [hsNormSq, Fin.sum_univ_two]
    rfl
  have htimecol (y : Domain 2) : ‖DW y (Fin.natAdd 1 (0 : Fin 1))‖ ^ 2 = T (C y) := by
    simp only [DW, Fin.addCases_right]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun y => hsNormSq (DW y)) = (fun y => A (C y) + T (C y)) from funext hsum]
    exact hAN.fun_add hTN
  · simp_rw [hsum]
    rw [integral_add hAN hTN, htime]
    exact add_le_add hsp le_rfl
  · simpa only [htimecol] using htime

/-- The same literal affine interpolation has a finite discrepancy integral
from its first closed-line representative, controlled by the original raw
line discrepancy with a time-length coefficient. -/
theorem interval_pair_rectangle_discrepancy_energy {q : ℕ}
    {a b c d : ℝ} (hcd : c < d) {F G f h : ℝ → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo a b)] h) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let α : Domain 2 → ℝ := fun y => ((e y).2 0 - c) / (d - c)
    let Ω := {y : Domain 2 | (e y).1 0 ∈ Ioo a b ∧ (e y).2 0 ∈ Ioo c d}
    let W : Domain 2 → Ambient q := fun y =>
      (1 - α y) • F ((e y).1 0) + α y • G ((e y).1 0)
    Integrable (fun y => ‖W y - F ((e y).1 0)‖ ^ 2) (volume.restrict Ω) ∧
    (∫ y in Ω, ‖W y - F ((e y).1 0)‖ ^ 2) ≤
      ((d - c) / 2) * ∫ s in Ioo a b, ‖f s - h s‖ ^ 2 := by
  intro e α Ω W
  let S := {x : Domain 1 | x 0 ∈ Ioo a b}
  let μ := (volume : Measure (Domain 1)).restrict S
  let ν := (volume : Measure ℝ).restrict (Icc c d)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let C := e.trans (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Domain 1)) τ)
  have hS : MeasurableSet S := measurableSet_Ioo.preimage
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable
  have hm := measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := a) (b := b))
  have hF : MemLp (fun x : Domain 1 => F (x 0)) 2 μ :=
    (hf.ae_eq hFae.symm).comp_measurePreserving hm
  have hG : MemLp (fun x : Domain 1 => G (x 0)) 2 μ :=
    (hh.ae_eq hGae.symm).comp_measurePreserving hm
  have hC0 : MeasurePreserving C volume ((volume : Measure (Domain 1)).prod volume) :=
    measurePreserving_cylinder_coordinates 1
  have hC := hC0.restrict_preimage (hS.prod (measurableSet_Ioo (a := c) (b := d)))
  rw [← Measure.prod_restrict] at hC
  change MeasurePreserving C (volume.restrict Ω)
    (μ.prod (volume.restrict (Ioo c d))) at hC
  have hν : (volume : Measure ℝ).restrict (Ioo c d) = ν :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [hν] at hC
  have hzero : MemLp (fun _ : Domain 1 => (0 : Ambient q)) 2 μ := MemLp.zero'
  obtain ⟨hAI, hAE⟩ := affine_field_integrable_energy_le μ hcd hzero (hG.sub hF)
  let A : Domain 1 × ℝ → ℝ := fun p =>
    ‖(1 - (p.2 - c) / (d - c)) • (0 : Ambient q) +
      ((p.2 - c) / (d - c)) • (G (p.1 0) - F (p.1 0))‖ ^ 2
  have hAN : Integrable (fun y => A (C y)) (volume.restrict Ω) :=
    hC.integrable_comp_of_integrable hAI
  have hAt := hC.integral_comp C.toHomeomorph.measurableEmbedding A
  have hD : (∫ x : Domain 1, ‖G (x 0) - F (x 0)‖ ^ 2 ∂μ) =
      ∫ s in Ioo a b, ‖f s - h s‖ ^ 2 := by
    change (∫ x : Domain 1 in {x | x 0 ∈ Ioo a b}, ‖G (x 0) - F (x 0)‖ ^ 2) = _
    rw [integral_domainOne_interval a b (fun s => ‖G s - F s‖ ^ 2)]
    apply integral_congr_ae
    filter_upwards [hFae, hGae] with s hsF hsG
    rw [hsF, hsG, norm_sub_rev]
  have hEq (y : Domain 2) : ‖W y - F ((e y).1 0)‖ ^ 2 = A (C y) := by
    have hW : W y - F ((e y).1 0) = α y • (G ((e y).1 0) - F ((e y).1 0)) := by
      simp only [W, sub_smul, one_smul, smul_sub]
      abel
    rw [hW]
    simp only [A, smul_zero, zero_add]
    rfl
  rw [show (fun y => ‖W y - F ((e y).1 0)‖ ^ 2) = (fun y => A (C y)) from funext hEq]
  refine ⟨hAN, ?_⟩
  rw [hAt]
  simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero, zero_add,
    Pi.sub_apply, hD] using hAE

end StratificationTheory
