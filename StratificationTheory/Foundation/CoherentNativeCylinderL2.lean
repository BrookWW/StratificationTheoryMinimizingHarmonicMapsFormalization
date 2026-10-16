module

public import StratificationTheory.Foundation.CylinderRadialProductMeasure
public import StratificationTheory.Foundation.CoherentProductL2

/-!
# Native cylinder L2 and energy from actual ambient columns

The exact native cylindrical polar measure transfers an ambient L2 field to
a product field. Genuine almost-everywhere spatial-ray coherence then
recovers the native cylinder L2 class and its exact radial energy factor.
Spatial columns use the reciprocal radius; the independent time column uses
the constant scalar one.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal
namespace StratificationTheory

/-- Weighted positive-radius a.e. statements on an actual band have exactly
the original restricted real-volume null sets, without a measurable-predicate
assumption. -/
theorem ae_positive_radius_band_iff {n : ℕ} {ε R : ℝ} (hε : 0 < ε)
    (P : ℝ → Prop) :
    (∀ᵐ ρ ∂(Measure.volumeIoiPow (n - 1)).restrict
      {ρ | ε < ρ.val ∧ ρ.val < R}, P ρ.val) ↔
      ∀ᵐ r ∂volume.restrict (Ioo ε R), P r := by
  have hJ : MeasurableSet {ρ : Ioi (0 : ℝ) | ε < ρ.val ∧ ρ.val < R} :=
    (isOpen_Ioo.preimage continuous_subtype_val).measurableSet
  rw [ae_restrict_iff' hJ, ae_volumeIoiPow_iff]
  change (∀ᵐ r : Ioi (0 : ℝ) ∂(volume : Measure ℝ).comap Subtype.val,
    (ε < r.val ∧ r.val < R) → P r.val) ↔ _
  rw [← ae_restrict_iff_subtype (μ := volume) (s := Ioi (0 : ℝ))
    (p := fun r => (ε < r ∧ r < R) → P r) measurableSet_Ioi,
    ae_restrict_iff' measurableSet_Ioi, ae_restrict_iff' measurableSet_Ioo]
  apply Filter.eventually_congr
  apply Filter.Eventually.of_forall
  intro r
  constructor
  · intro h hr
    exact h (hε.trans hr.1) hr
  · intro h _ hr
    exact h hr

private theorem positive_radius_band_measure {n : ℕ} {ε R : ℝ}
    (hε : 0 < ε) (hεR : ε < R) :
    let J : Set (Ioi (0 : ℝ)) := {ρ | ε < ρ.val ∧ ρ.val < R}
    0 < Measure.volumeIoiPow (n - 1) J ∧ Measure.volumeIoiPow (n - 1) J ≠ ⊤ := by
  intro J
  have hR : 0 < R := hε.trans hεR
  have hbound : Measure.volumeIoiPow (n - 1) J ≤
      Measure.volumeIoiPow (n - 1) (Iio (⟨R, hR⟩ : Ioi (0 : ℝ))) :=
    measure_mono (fun _ h => h.2)
  refine ⟨?_, ne_top_of_le_ne_top
    (by rw [Measure.volumeIoiPow_apply_Iio]; exact ENNReal.ofReal_ne_top) hbound⟩
  apply pos_iff_ne_zero.mpr
  intro hz
  have hae : ∀ᵐ ρ ∂(volume : Measure ℝ).comap (Subtype.val : Ioi (0 : ℝ) → ℝ), ρ ∉ J :=
    (ae_volumeIoiPow_iff (n - 1)).mp (measure_eq_zero_iff_ae_notMem.mp hz)
  letI : Measure.IsOpenPosMeasure ((volume : Measure ℝ).comap
      (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioi.isOpenEmbedding_subtypeVal
  have hJ : IsOpen J := isOpen_Ioo.preimage continuous_subtype_val
  have hmid : 0 < (ε + R) / 2 := by linarith
  have hne : J.Nonempty := ⟨⟨(ε + R) / 2, hmid⟩, by constructor <;> linarith⟩
  exact (hJ.measure_pos _ hne).ne' (measure_eq_zero_iff_ae_notMem.mpr hae)

/-- A genuine coherent ambient spatial or time column determines an actual
native cylinder L2 class and its exact, unnormalized radial energy factor. -/
theorem native_cylinder_L2_energy_of_radial_column_coherence {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ε R a b : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (spatial : Bool) (f : Domain (n + 1) → E)
    (g : unitCylinder n a b → E)
    (hf : MemLp f 2 (volume.restrict {y : Domain (n + 1) |
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b})) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let η := (Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    let s : Ioi (0 : ℝ) → ℝ := fun ρ => if spatial then ρ.val⁻¹ else 1
    (∀ᵐ ρ ∂η, ∀ᵐ c ∂μ,
      f (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = s ρ • g c) →
    MemLp g 2 μ ∧
      (∫ y in {y : Domain (n + 1) |
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}, ‖f y‖ ^ 2) =
        (∫ ρ, (s ρ) ^ 2 ∂η) * ∫ c, ‖g c‖ ^ 2 ∂μ := by
  intro e η μ s hcoh
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν
      (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  letI : SFinite μ := (unitCylinder_param_measurePreserving hn a b).2.sfinite
  obtain ⟨hpos, hfin⟩ := positive_radius_band_measure (n := n) hε hεR
  have hmass : η univ = Measure.volumeIoiPow (n - 1) {ρ | ε < ρ.val ∧ ρ.val < R} :=
    Measure.restrict_apply_univ _
  letI : IsFiniteMeasure η := ⟨by rw [hmass]; exact hfin.lt_top⟩
  letI : NeZero η := ⟨by
    intro hz
    have h := congrArg (fun m : Measure (Ioi (0 : ℝ)) => m univ) hz
    rw [hmass] at h
    exact hpos.ne' (by simpa using h)⟩
  let F : unitCylinder n a b × Ioi (0 : ℝ) → Domain (n + 1) := fun p =>
    e.symm (p.2.val • (e p.1.val).1, (e p.1.val).2)
  have hMP := measurePreserving_native_cylinder_radial_inverse hn hε R a b
  have hp : MemLp (fun p => f (F p)) 2 (μ.prod η) := hf.comp_measurePreserving hMP
  have hs : ∀ᵐ ρ ∂η, s ρ ≠ 0 := Filter.Eventually.of_forall (fun ρ => by
    cases spatial
    · change (1 : ℝ) ≠ 0
      exact one_ne_zero
    · change ρ.val⁻¹ ≠ 0
      exact inv_ne_zero (ne_of_gt ρ.property))
  refine ⟨memLp_two_of_product_scalar_coherence hp g s hs hcoh, ?_⟩
  have heq := integral_sq_norm_product_scalar_coherence hp g s hcoh
  have hmeas : AEStronglyMeasurable (fun y => ‖f y‖ ^ 2)
      (Measure.map F (μ.prod η)) := by
    rw [hMP.map_eq]
    exact (hf.integrable_norm_pow (by norm_num)).aestronglyMeasurable
  rw [← integral_map hMP.measurable.aemeasurable hmeas, hMP.map_eq] at heq
  exact heq

/-- The real-radius and interior-time coherence used by the original joint
Luckhaus statement suffices for native L2 and the exact energy factor.
Closed time faces are discarded only by their proved native null measure. -/
theorem native_cylinder_L2_energy_of_real_radial_column_coherence {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ε R a b : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (spatial : Bool) (f : Domain (n + 1) → E)
    (g : unitCylinder n a b → E)
    (hf : MemLp f 2 (volume.restrict {y : Domain (n + 1) |
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b})) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let η := (Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    (∀ᵐ r ∂volume.restrict (Ioo ε R), ∀ᵐ c ∂μ, (e c.val).2 0 ∈ Ioo a b →
      f (e.symm (r • (e c.val).1, (e c.val).2)) =
        (if spatial then r⁻¹ else 1) • g c) →
    MemLp g 2 μ ∧
      (∫ y in {y : Domain (n + 1) |
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}, ‖f y‖ ^ 2) =
        (∫ ρ, (if spatial then ρ.val⁻¹ else 1) ^ 2 ∂η) * ∫ c, ‖g c‖ ^ 2 ∂μ := by
  intro e η μ hcoh
  apply native_cylinder_L2_energy_of_radial_column_coherence hn hε hεR spatial f g hf
  have hc : ∀ᵐ ρ ∂η, ∀ᵐ c ∂μ, (e c.val).2 0 ∈ Ioo a b →
      f (e.symm (ρ.val • (e c.val).1, (e c.val).2)) =
        (if spatial then ρ.val⁻¹ else 1) • g c :=
    (ae_positive_radius_band_iff (n := n) hε _).mpr hcoh
  filter_upwards [hc] with ρ hρ
  filter_upwards [hρ, ae_unitCylinder_time_mem_Ioo hn a b] with c hceq hct
  exact hceq hct

end StratificationTheory
