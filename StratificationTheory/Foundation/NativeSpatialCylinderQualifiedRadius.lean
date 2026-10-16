module

public import StratificationTheory.Foundation.NativeSpatialCylinderGoodRadius

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

private theorem ae_native_product_memLp_two_right {X Y E : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → E} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x => f (x, y)) 2 μ := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_right,
    (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).prod_left_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

/-- A single actual spatial radius retains the original graph, value
property, averaged cylinder energy, and any independently proved almost
everywhere radius qualification. The physical time coordinate is unchanged. -/
theorem exists_native_spatial_cylinder_good_radius_with_qualification {n q : ℕ} (hn : 0 < n)
    {s R ε : ℝ} (hs : 0 < s) (hsR : s < R)
    (W : Domain (n + 1) → Ambient q) (DW : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (s < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε},
        (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | s < ρ.val ∧ ρ.val < R}
    let μ : Measure (unitCylinder n 0 ε) := Measure.euclideanHausdorffMeasure n
    let F := fun (r : ℝ) (c : unitCylinder n 0 ε) =>
      e.symm (r • (e c.val).1, (e c.val).2)
    MemW12 Ω W DW → ∀ P : Ambient q → Prop,
    (∀ᵐ y ∂volume.restrict Ω.val, P (W y)) →
    ∀ Q : ℝ → Prop, (∀ᵐ r ∂volume.restrict (Ioo s R), Q r) →
    ∃ r ∈ Ioo s R, Q r ∧
      MemLp (fun c => W (F r c)) 2 μ ∧
      (∀ i : Fin (n + 1), MemLp (fun c => DW (F r c) i) 2 μ) ∧
      Integrable (fun c => hsNormSq (DW (F r c))) μ ∧
      (∀ᵐ c ∂μ, P (W (F r c))) ∧
      (∫ c, hsNormSq (DW (F r c)) ∂μ) ≤
        (η univ).toReal⁻¹ * ∫ y in Ω.val, hsNormSq (DW y) := by
  intro e Ω η μ F hW P hP Q hQ
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc (0 : ℝ) ε → ℝ)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : SigmaFinite ν :=
    (measurePreserving_subtype_coe (measurableSet_Icc (a := (0 : ℝ)) (b := ε))
      (μa := (volume : Measure ℝ))).sigmaFinite
  letI : SFinite μ := (unitCylinder_param_measurePreserving hn 0 ε).2.sfinite
  obtain ⟨hMassPos, hMassFin⟩ := native_spatial_radius_band_mass (n := n) hs hsR
  letI : IsFiniteMeasure η := ⟨hMassFin.lt_top⟩
  have hηzero : η ≠ 0 := by
    intro hz
    have hmass : η univ = 0 := by rw [hz]; simp
    exact hMassPos.ne' hmass
  let G : unitCylinder n 0 ε × Ioi (0 : ℝ) → Domain (n + 1) :=
    fun p => F p.2.val p.1
  have hm := measurePreserving_native_cylinder_radial_inverse hn hs R 0 ε
  have hMap : MemLp (fun p => W (G p)) 2 (μ.prod η) :=
    hW.2.1.comp_measurePreserving hm
  have hCols (i : Fin (n + 1)) : MemLp (fun p => DW (G p) i) 2 (μ.prod η) :=
    (hW.2.2 i).comp_measurePreserving hm
  have hEnergy : Integrable (fun p => hsNormSq (DW (G p))) (μ.prod η) :=
    hm.integrable_comp_of_integrable hW.integrable_hsNormSq
  have hEnergySlice := hEnergy.prod_left_ae
  have hAllCols : ∀ᵐ ρ ∂η, ∀ i : Fin (n + 1),
      MemLp (fun c => DW (F ρ.val c) i) 2 μ :=
    ae_all_iff.mpr fun i => ae_native_product_memLp_two_right (hCols i)
  have hProp : ∀ᵐ ρ ∂η, ∀ᵐ c ∂μ, P (W (F ρ.val c)) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (hm.quasiMeasurePreserving.ae hP))
  have hBand : ∀ᵐ ρ ∂η, s < ρ.val ∧ ρ.val < R :=
    ae_restrict_mem ((isOpen_Ioo.preimage continuous_subtype_val).measurableSet)
  have hGood : ∀ᵐ ρ ∂η, (s < ρ.val ∧ ρ.val < R) ∧
      MemLp (fun c => W (F ρ.val c)) 2 μ ∧
      (∀ i : Fin (n + 1), MemLp (fun c => DW (F ρ.val c) i) 2 μ) ∧
      Integrable (fun c => hsNormSq (DW (F ρ.val c))) μ ∧
      (∀ᵐ c ∂μ, P (W (F ρ.val c))) := by
    filter_upwards [hBand, ae_native_product_memLp_two_right hMap,
      hAllCols, hEnergySlice, hProp] with ρ hρ hmap hc he hp
    exact ⟨hρ, hmap, hc, he, hp⟩
  let E := fun ρ : Ioi (0 : ℝ) => ∫ c, hsNormSq (DW (F ρ.val c)) ∂μ
  have hE : Integrable E η := hEnergy.integral_prod_right
  have hQη : ∀ᵐ ρ ∂η, Q ρ.val := (ae_positive_radius_band_iff (n := n) hs Q).mpr hQ
  have hQualified := hQη.and hGood
  obtain ⟨ρ, hρ, hBound⟩ := exists_notMem_null_le_average hηzero hE (ae_iff.mp hQualified)
  have hρ' := Classical.not_not.mp hρ
  have hTotal : (∫ ρ, E ρ ∂η) = ∫ y in Ω.val, hsNormSq (DW y) := by
    rw [← integral_prod_symm _ hEnergy]
    have hMeas : AEStronglyMeasurable (fun y => hsNormSq (DW y))
        (Measure.map G (μ.prod η)) := by
      rw [hm.map_eq]
      exact hW.integrable_hsNormSq.aestronglyMeasurable
    have hIntegral := integral_map hm.measurable.aemeasurable hMeas
    rw [hm.map_eq] at hIntegral
    exact hIntegral.symm
  refine ⟨ρ.val, hρ'.2.1, hρ'.1, hρ'.2.2.1, hρ'.2.2.2.1, hρ'.2.2.2.2.1, hρ'.2.2.2.2.2, ?_⟩
  simpa only [average_eq, measureReal_def, smul_eq_mul, hTotal] using hBound

end StratificationTheory
