module

public import StratificationTheory.Interpolation.CylinderAnnularTransport
public import StratificationTheory.Interpolation.AnnularAERadialCoherence
public import StratificationTheory.Foundation.AnnularRawEquality
public import StratificationTheory.Foundation.CylinderNativeCoordinates
public import StratificationTheory.Foundation.NativeCylinderAnnularCoordinates
public import StratificationTheory.Foundation.CylinderPostcomposition
public import StratificationTheory.Foundation.AnnularPropertyTransfer
public import HarmonicMaps.SobolevRestriction
public import StratificationTheory.Foundation.SmoothPostcompositionEnergy
public import StratificationTheory.Foundation.CylinderTracePostcomposition
public import StratificationTheory.Frozen.CylinderAnnularTransfer

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal ContDiff BigOperators
namespace StratificationTheory

/-- Original coherent native columns control the energy of the same
annular map carrying the complete original postcomposition trace curve. -/
theorem exists_cylinder_annular_postcomposition_trace_energy {n q k : ℕ} (hn : 2 ≤ n)
    {a b s : ℝ} (hab : a < b) (ha : -1 < a) (hs : 0 < s)
    (v : unitCylinder n a b → Ambient q) (hv : MemCylinderW12 hn hab v)
    (W : Domain (n + 1) → Ambient q) (DW : Domain (n + 1) → Gradient (n + 1) q)
    (g : unitCylinder n a b → Gradient (n + 1) q)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (C : ℝ≥0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    let U : OpenDomain (n + 1) :=
      ⟨{y | ‖(e y).1‖ ∈ Ioo (1 / 2 : ℝ) 2 ∧ (e y).2 0 ∈ Ioo a b},
        (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    MemW12 U W DW →
    (∀ r ∈ Ioo (1 / 2 : ℝ) 2, ∀ c : unitCylinder n a b,
      (e c.val).2 0 ∈ Ioo a b → W (e.symm (r • (e c.val).1, (e c.val).2)) = v c) →
    (∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      ∀ᵐ c : unitCylinder n a b ∂μ, (e c.val).2 0 ∈ Ioo a b →
        (∀ i : Fin n, DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
          r⁻¹ • g c (Fin.castAdd 1 i)) ∧
        DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
          g c (Fin.natAdd n (0 : Fin 1))) →
    (∀ i : Fin (n + 1), MemLp (fun c => g c i) 2 μ) →
    (∀ᵐ c ∂μ, ‖fderiv ℝ F (v c)‖ ≤ (C : ℝ)) →
    let lo := s * (1 + a)
    let hi := s * (1 + b)
    let V : OpenDomain n := ⟨{x | lo < ‖x‖ ∧ ‖x‖ < hi}, isOpen_Ioo.preimage continuous_norm⟩
    let κ := max lo⁻¹ s⁻¹
    let τ : C(Icc lo hi, Icc a b) :=
      ⟨fun r => ⟨r.val / s - 1, by
        constructor
        · have hr := r.property.1
          change s * (1 + a) ≤ r.val at hr
          have hh : a + 1 ≤ r.val / s := (le_div_iff₀ hs).mpr (by nlinarith)
          linarith
        · have hr := r.property.2
          change r.val ≤ s * (1 + b) at hr
          have hh : r.val / s ≤ b + 1 := (div_le_iff₀ hs).mpr (by nlinarith)
          linarith⟩,
        by
          apply Continuous.subtype_mk
          exact (continuous_subtype_val.div_const s).sub (continuous_const (y := (1 : ℝ)))⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃ hFv : MemCylinderW12 hn hab (F ∘ v),
      let H := cylinderTrace hn hab (F ∘ v) hFv
      let K := H.comp τ
      ∃ (A : Domain n → Ambient k) (DA : Domain n → Gradient n k),
        MemW12 V A DA ∧
        (∀ (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b),
          A ((s * (1 + t)) • θ.val) = F (v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
            unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩)) ∧
        (∫ x in V.val, hsNormSq (DA x)) ≤
          (s * hi ^ (n - 1)) * κ ^ 2 * (C : ℝ) ^ 2 * ∫ c, hsNormSq (g c) ∂μ ∧
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo lo hi,
          ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => A (r • θ.val)) 2 σ,
            K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ => A (r • θ.val)))
 := by
  classical
  intro e μ U hW hRaw hCoh hg hBound lo hi V κ τ σ
  have hnpos : 0 < n := by omega
  let δ : ℝ := 1 / 4
  have hδ : 0 < δ := by norm_num [δ]
  have hδsmall : δ < 1 / 2 := by norm_num [δ]
  let η := (Measure.volumeIoiPow (n - 1)).restrict
    {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
  let P := (η univ)⁻¹ • η
  let Ωδ : OpenDomain (n + 1) :=
    ⟨{y | (1 - δ < ‖(e y).1‖ ∧ ‖(e y).1‖ < 1 + δ) ∧ (e y).2 0 ∈ Ioo a b},
      (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hSub : Ωδ.val ⊆ U.val := by
    intro y hy
    change ((1 - δ < ‖(e y).1‖ ∧ ‖(e y).1‖ < 1 + δ) ∧ (e y).2 0 ∈ Ioo a b) at hy
    exact ⟨⟨by dsimp only [δ] at hy; linarith [hy.1.1],
      by dsimp only [δ] at hy; linarith [hy.1.2]⟩, hy.2⟩
  have hWδ : MemW12 Ωδ W DW :=
    ⟨hW.1.mono hSub, hW.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i => (hW.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  obtain ⟨hProb, β, hβ, hcβ, hsβ, _hβnonneg, hmass⟩ :=
    exists_normalized_smooth_radial_weight (n := n) hδ
  letI : IsProbabilityMeasure P := hProb
  obtain ⟨Acoord, Bcoord, _hCoords, hA, hB, _hABInt, hABEnergy, hCoordCoh⟩ :=
    exists_native_cylinder_annular_coordinates hnpos hδsmall DW g hg hCoh
  let Avg := annularAveragedMap s β P W
  let DAvg := annularAveragedColumns s β P DW
  have hAvg : MemW12 V Avg DAvg :=
    memW12_annularAveragedMap hn hab ha hs hWδ hδ hδsmall rfl hβ hcβ hsβ
  have hAvgEnergy : (∫ x in V.val, hsNormSq (DAvg x)) ≤
      (s * hi ^ (n - 1)) * κ ^ 2 * ∫ c, hsNormSq (g c) ∂μ := by
    have hh := annularAveragedColumns_energy_le_of_ae_radial_coherence hnpos hWδ
      hδ hδsmall hs ha hab rfl Acoord Bcoord β hA hB hmass hCoordCoh
    rw [hABEnergy] at hh
    exact hh.2.2
  have hBand : ∀ᵐ ρ : Ioi (0 : ℝ) ∂P, 1 - δ < ρ.val ∧ ρ.val < 1 + δ := by
    apply (Measure.smul_absolutelyContinuous (μ := η) (c := (η univ)⁻¹)).ae_le
    exact ae_restrict_mem ((isOpen_Ioo.preimage continuous_subtype_val).measurableSet)
  have hAvgRaw (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b) :
      Avg ((s * (1 + t)) • θ.val) = v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
        unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩ := by
    let c : unitCylinder n a b := ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
      unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩
    change annularAveragedMap s β P W ((s * (1 + t)) • θ.val) = _
    rw [annularAveragedMap_param hs (ha.trans ht.1)]
    calc
      (∫ ρ : Ioi (0 : ℝ), β ρ.val • W (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) ∂P) =
          ∫ ρ : Ioi (0 : ℝ), β ρ.val • v c ∂P := by
        apply integral_congr_ae
        filter_upwards [hBand] with ρ hρ
        have hρ' : ρ.val ∈ Ioo (1 / 2 : ℝ) 2 := by
          dsimp only [δ] at hρ
          constructor <;> linarith [hρ.1, hρ.2]
        have hct : (e c.val).2 0 ∈ Ioo a b := by
          simpa only [c, e.apply_symm_apply, PiLp.single_apply, ite_true] using ht
        have hh := hRaw ρ.val hρ' c hct
        have hEq : W (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) = v c := by
          simpa only [c, e.apply_symm_apply] using hh
        rw [hEq]
      _ = (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) • v c := integral_smul_const _ _
      _ = v c := by rw [hmass, one_smul]
  have hBoundAvg : ∀ᵐ x ∂volume.restrict V.val, ‖fderiv ℝ F (Avg x)‖ ≤ (C : ℝ) :=
    ae_annular_property_of_native_cylinder hnpos hs ha v Avg
      (fun z => ‖fderiv ℝ F z‖ ≤ (C : ℝ)) hBound hAvgRaw
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val) :=
    isFiniteMeasure_restrict.mpr (by
      apply ne_top_of_le_ne_top (Metric.isBounded_ball.measure_lt_top.ne : (volume : Measure (Domain n)) (ball 0 hi) ≠ ⊤)
      apply measure_mono
      intro x hx
      exact mem_ball_zero_iff.mpr hx.2)
  have hPost : MemW12 V (F ∘ Avg) (fun x i => fderiv ℝ F (Avg x) (DAvg x i)) :=
    MemW12.postcompose_finite hAvg F hF L hDF
  have hPostE := (smooth_postcomposition_column_energy_le hAvg.2.1.aestronglyMeasurable
    hAvg.2.2 F hF C hBoundAvg).2.2
  let hFv := memCylinderW12_postcompose hn hab v hv F hF L hDF
  refine ⟨hFv, ?_⟩
  intro H K
  obtain ⟨A, DA, hAnn, hAnnRaw, hTrace⟩ := cylinder_to_annulus_exists hn hab ha hs
    (0 : Domain n) (F ∘ v) hFv
  have hAnn' : MemW12 V A DA := by simpa only [sub_zero] using hAnn
  have hAnnRaw' (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b) :
      A ((s * (1 + t)) • θ.val) = F (v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
        unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩) := by
    simpa only [zero_add, Function.comp_apply] using hAnnRaw θ t ht
  have hEqE := annular_weak_columns_and_energy_eq_of_raw_ray_eq hs ha hPost hAnn'
    (fun θ t ht => (congrArg F (hAvgRaw θ t ht)).trans (hAnnRaw' θ t ht).symm)
  refine ⟨A, DA, hAnn', hAnnRaw', ?_, ?_⟩
  · rw [← hEqE.2]
    calc
      _ ≤ (C : ℝ) ^ 2 * ∫ x in V.val, hsNormSq (DAvg x) := hPostE
      _ ≤ (C : ℝ) ^ 2 * ((s * hi ^ (n - 1)) * κ ^ 2 * ∫ c, hsNormSq (g c) ∂μ) :=
        mul_le_mul_of_nonneg_left hAvgEnergy (sq_nonneg _)
      _ = _ := by ring
  · simpa only [zero_add] using hTrace

end StratificationTheory
