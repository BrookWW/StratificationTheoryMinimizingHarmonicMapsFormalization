module
public import StratificationTheory.Foundation.CylinderBochnerL2
public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import StratificationTheory.Foundation.CylinderSobolevCollar
public import StratificationTheory.Foundation.CylinderRawTime
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff
namespace StratificationTheory

theorem measurePreserving_native_radial_collar_inverse {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    MeasurePreserving (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) => p.2.val • p.1.val)
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        ((Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}))
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) := by
  let X := ({(0 : Domain n)}ᶜ : Set (Domain n))
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  let ν := Measure.volumeIoiPow (n - 1)
  let J : Set (Ioi (0 : ℝ)) := {ρ | ε < ρ.val ∧ ρ.val < R}
  let S : Set (Domain n) := {x | ε < ‖x‖ ∧ ‖x‖ < R}
  have hS : MeasurableSet S := (isOpen_Ioo.preimage continuous_norm).measurableSet
  have hp := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hp
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere hn] at hp
  have hi := hp.symm (homeomorphUnitSphereProd (Domain n)).toMeasurableEquiv
  have hc := measurePreserving_subtype_coe
    (measurableSet_singleton (0 : Domain n)).compl (μa := volume)
  have hm := hc.comp hi
  have hpre : (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      ((homeomorphUnitSphereProd (Domain n)).symm p).val) ⁻¹' S = univ ×ˢ J := by
    ext p
    have hθ : ‖p.1.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using p.1.property
    simp only [mem_preimage, S, mem_setOf_eq, homeomorphUnitSphereProd_symm_apply_coe,
      norm_smul, Real.norm_of_nonneg p.2.property.le, hθ, mul_one,
      mem_prod, mem_univ, true_and, J]
  have hr := hm.restrict_preimage hS
  change MeasurePreserving (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      ((homeomorphUnitSphereProd (Domain n)).symm p).val)
    ((σ.prod ν).restrict ((fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      ((homeomorphUnitSphereProd (Domain n)).symm p).val) ⁻¹' S))
    ((volume.restrict X).restrict S) at hr
  rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ] at hr
  have hsub : S ⊆ X := by
    intro x hx
    change x ≠ 0
    exact norm_pos_iff.mp (hε.trans hx.1)
  rw [Measure.restrict_restrict_of_subset hsub] at hr
  simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hr


theorem measurePreserving_native_polar_collar_cylinder_inverse {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (R a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MeasurePreserving (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
      e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2))
      (((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.restrict (Ioo a b))).prod
        ((Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}))
      (volume.restrict {y : Domain (n + 1) |
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}) := by
  intro e
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure ℝ := volume.restrict (Ioo a b)
  let η := (Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}
  let S : Set (Domain n) := {x | ε < ‖x‖ ∧ ‖x‖ < R}
  let Ω : Set (Domain (n + 1)) :=
    {y | (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hS : MeasurableSet S := (isOpen_Ioo.preimage continuous_norm).measurableSet
  have hΩ : MeasurableSet Ω :=
    (hS.preimage e.continuous.fst.measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        e.continuous.snd).measurable)
  have hc := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage hΩ
  have hpre : (fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) ⁻¹' Ω = S ×ˢ Ioo a b := by
    ext p
    simp only [mem_preimage, Ω, e.apply_symm_apply, PiLp.single_apply,
      ite_true, mem_setOf_eq, mem_prod, S]
  rw [hpre, ← Measure.prod_restrict] at hc
  have hp := (measurePreserving_native_radial_collar_inverse hn hε R).prod
    (MeasurePreserving.id ν)
  have hs : MeasurePreserving
      (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) => ((p.1.1, p.2), p.1.2))
      ((σ.prod ν).prod η) ((σ.prod η).prod ν) := by
    exact ((measurePreserving_prodAssoc σ η ν).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id σ).prod Measure.measurePreserving_swap).comp
        (measurePreserving_prodAssoc σ ν η))
  simpa only [Function.comp_def, Prod.map_apply, id_eq, σ, ν, η, Ω, e] using hc.comp (hp.comp hs)


theorem radial_collar_jacobian_mass_finite_pos {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) :
    let J : Set (Ioi (0 : ℝ)) := {ρ | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    0 < Measure.volumeIoiPow (n - 1) J ∧ Measure.volumeIoiPow (n - 1) J ≠ ⊤ := by
  intro J
  have hR : 0 < 1 + δ := by linarith
  have hbound : Measure.volumeIoiPow (n - 1) J ≤
      Measure.volumeIoiPow (n - 1) (Iio (⟨1 + δ, hR⟩ : Ioi (0 : ℝ))) :=
    measure_mono (fun _ h => h.2)
  have hfinite : Measure.volumeIoiPow (n - 1) J ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Measure.volumeIoiPow_apply_Iio]; exact ENNReal.ofReal_ne_top) hbound
  refine ⟨?_, hfinite⟩
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hae : ∀ᵐ ρ ∂(volume : Measure ℝ).comap (Subtype.val : Ioi (0 : ℝ) → ℝ), ρ ∉ J :=
    (ae_volumeIoiPow_iff (n - 1)).mp (measure_eq_zero_iff_ae_notMem.mp hzero)
  have hzero' := measure_eq_zero_iff_ae_notMem.mpr hae
  letI : Measure.IsOpenPosMeasure ((volume : Measure ℝ).comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
    Measure.IsOpenPosMeasure.comap volume (isOpen_Ioi.isOpenEmbedding_subtypeVal)
  have hJ : IsOpen J := isOpen_Ioo.preimage continuous_subtype_val
  have hne : J.Nonempty := ⟨⟨1, by norm_num⟩, by constructor <;> linarith⟩
  exact (hJ.measure_pos _ hne).ne' hzero'


theorem memLp_two_native_radial_collar_average {n q : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2) (a b : ℝ)
    {f : Domain (n + 1) → Ambient q}
    (hf : MemLp f 2 (volume.restrict {y : Domain (n + 1) |
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      (1 - δ < ‖(e y).1‖ ∧ ‖(e y).1‖ < 1 + δ) ∧ (e y).2 0 ∈ Ioo a b})) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let J : Set (Ioi (0 : ℝ)) := {ρ | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let η := (Measure.volumeIoiPow (n - 1)).restrict J
    let P := (η univ)⁻¹ • η
    IsProbabilityMeasure P ∧
      MemLp (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
        f (e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2))) 2
        (((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
          (volume.restrict (Ioo a b))).prod P) ∧
      MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
        ∫ ρ, f (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) ∂P) 2
        ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
          (volume.restrict (Ioo a b))) := by
  intro e J η P
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure ℝ := volume.restrict (Ioo a b)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  obtain ⟨hpos, hfin⟩ := radial_collar_jacobian_mass_finite_pos (n := n) hδ
  have hmass : η univ = Measure.volumeIoiPow (n - 1) J := Measure.restrict_apply_univ J
  letI : IsFiniteMeasure η := ⟨by rw [hmass]; exact hfin.lt_top⟩
  letI : NeZero η := ⟨by
    intro hz
    have he := congrArg (fun μ : Measure (Ioi (0 : ℝ)) => μ univ) hz
    rw [hmass] at he
    exact hpos.ne' (by simpa using he)⟩
  letI : IsProbabilityMeasure P := inferInstance
  refine ⟨inferInstance, ?_⟩
  have hp := hf.comp_measurePreserving
    (measurePreserving_native_polar_collar_cylinder_inverse hn (by linarith : 0 < 1 - δ) (1 + δ) a b)
  have hscale : (η univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by rw [hmass]; exact hpos.ne')
  have hpP : MemLp
      (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
        f (e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)))
      2 ((σ.prod ν).prod P) := by
    rw [Measure.prod_smul_right]
    exact hp.smul_measure hscale
  exact ⟨hpP, (memLp_two_probability_average hpP).1⟩


theorem exists_memCylinder_radial_average_data {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) {v : unitCylinder n a b → Ambient q}
    (hv : MemCylinderW12 hn hab v) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∃ U : OpenDomain n,
      U.val = {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ} ∧
      ∃ w : Domain (n + 1) → Ambient q, ∃ Dw : Domain (n + 1) → Gradient (n + 1) q,
        MemW12 ⟨{y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b},
          (U.property.preimage (continuous_fst.comp
            (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp
                (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)))⟩ w Dw ∧
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
        let J : Set (Ioi (0 : ℝ)) := {ρ | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
        let η := (Measure.volumeIoiPow (n - 1)).restrict J
        let P := (η univ)⁻¹ • η
        IsProbabilityMeasure P ∧
          MemLp (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
            w (e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2))) 2
            (((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
              (volume.restrict (Ioo a b))).prod P) ∧
          MemLp (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
            Dw (e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2))
              (Fin.natAdd n (0 : Fin 1))) 2
            (((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
              (volume.restrict (Ioo a b))).prod P) ∧
          MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
            ∫ ρ, w (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) ∂P) 2
            ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
              (volume.restrict (Ioo a b))) ∧
          MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
            ∫ ρ, Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
              (Fin.natAdd n (0 : Fin 1)) ∂P) 2
            ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
              (volume.restrict (Ioo a b))) ∧
          ∀ c : unitCylinder n a b, (e c.val).2 0 ∈ Ioo a b →
            (∫ ρ, w (e.symm (ρ.val • (e c.val).1, (e c.val).2)) ∂P) = v c := by
  obtain ⟨hLv, δ, hδ, hδsmall, U, hU, _hSphere, _hzero, w, Dw, hW, hraw⟩ :=
    (memCylinderW12_iff_exists_radial_collar hn hab v).mp hv
  refine ⟨δ, hδ, hδsmall, U, hU, w, Dw, hW, ?_⟩
  intro e J η P
  have hD : MemLp (fun y => Dw y (Fin.natAdd n (0 : Fin 1))) 2
      (volume.restrict {y : Domain (n + 1) |
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
        (1 - δ < ‖(e y).1‖ ∧ ‖(e y).1‖ < 1 + δ) ∧ (e y).2 0 ∈ Ioo a b}) := by
    have hi := hW.2.2 (Fin.natAdd n (0 : Fin 1))
    change MemLp (fun y => Dw y (Fin.natAdd n (0 : Fin 1))) 2
      (volume.restrict {y : Domain (n + 1) | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b}) at hi
    rwa [hU] at hi
  have hM : MemLp w 2
      (volume.restrict {y : Domain (n + 1) |
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
        (1 - δ < ‖(e y).1‖ ∧ ‖(e y).1‖ < 1 + δ) ∧ (e y).2 0 ∈ Ioo a b}) := by
    have hi := hW.2.1
    change MemLp w 2 (volume.restrict {y : Domain (n + 1) |
      (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b}) at hi
    rwa [hU] at hi
  have hAvg := memLp_two_native_radial_collar_average (by omega : 0 < n) hδ hδsmall a b hD
  have hMap := memLp_two_native_radial_collar_average (by omega : 0 < n) hδ hδsmall a b hM
  refine ⟨hAvg.1, hMap.2.1, hAvg.2.1, hMap.2.2, hAvg.2.2, ?_⟩
  letI : IsProbabilityMeasure P := hAvg.1
  have hJ : MeasurableSet J := (isOpen_Ioo.preimage continuous_subtype_val).measurableSet
  have hAE : ∀ᵐ ρ ∂P, ρ ∈ J :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem hJ)
  intro c ht
  have hθ : ‖(e c.val).1‖ = 1 := by
    have hc : (e c.val).1 ∈ sphere (0 : Domain n) 1 := c.property.1
    simpa only [mem_sphere, dist_zero_right] using hc
  have heq : (fun ρ : Ioi (0 : ℝ) => w (e.symm (ρ.val • (e c.val).1, (e c.val).2))) =ᵐ[P]
      (fun _ => v c) := by
    filter_upwards [hAE] with ρ hρ
    change 1 - δ < ρ.val ∧ ρ.val < 1 + δ at hρ
    apply hraw ρ c ht
    rw [hU]
    change 1 - δ < ‖ρ.val • (e c.val).1‖ ∧ ‖ρ.val • (e c.val).1‖ < 1 + δ
    simpa only [norm_smul, Real.norm_of_nonneg ρ.property.le, hθ, mul_one] using hρ
  rw [integral_congr_ae heq]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]


theorem MemW12.native_radial_collar_time_test_ae {n q : ℕ} (hn : 0 < n)
    (U : OpenDomain n) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hU : U.val = {x : Domain n | 1 - δ < ‖x‖ ∧ ‖x‖ < 1 + δ}) {a b : ℝ}
    {w : Domain (n + 1) → Ambient q} {Dw : Domain (n + 1) → Gradient (n + 1) q}
    (hw : MemW12
      ⟨{y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ U.val ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b},
        (U.property.preimage (continuous_fst.comp
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp
              (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).continuous)))⟩ w Dw)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ioo a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let J : Set (Ioi (0 : ℝ)) := {ρ | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let η := (Measure.volumeIoiPow (n - 1)).restrict J
    let P := (η univ)⁻¹ • η
    ∀ᵐ p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ)
        ∂(Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod P,
      (∫ t in Ioo a b,
        deriv φ t • w (e.symm (p.2.val • p.1.val, EuclideanSpace.single (0 : Fin 1) t)) +
        φ t • Dw (e.symm (p.2.val • p.1.val, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1))) = 0 := by
  intro e J η P
  have ht := MemW12.radial_collar_time_test_ae U hU hw hφ hcφ hsφ
  have hz := ht.mono (fun _ hx => hx.2.2.2)
  rw [hU] at hz
  have hp := (measurePreserving_native_radial_collar_inverse hn
    (by linarith : 0 < 1 - δ) (1 + δ)).quasiMeasurePreserving.ae hz
  have hscale : ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod P) ≪
      ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod η) := by
    rw [Measure.prod_smul_right]
    exact Measure.smul_absolutelyContinuous
  exact hscale.ae_le hp

end StratificationTheory
