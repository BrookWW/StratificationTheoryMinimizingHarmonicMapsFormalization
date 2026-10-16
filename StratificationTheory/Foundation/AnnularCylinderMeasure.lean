module

public import StratificationTheory.Foundation.CylinderParamMeasure
public import StratificationTheory.Foundation.PolarSlices
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exact volume measure for radial annular cylinder coordinates

The sphere factor carries its native Hausdorff measure. Radius, and then
affine time, carry the actual positive radial Jacobian. The resulting
pushforward is the original Euclidean volume on the open annulus.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal
namespace StratificationTheory

private theorem measurePreserving_withDensity_comp {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν) (g : β → ℝ≥0∞) (hg : Measurable g) :
    MeasurePreserving f (μ.withDensity (g ∘ f)) (ν.withDensity g) := by
  refine ⟨hf.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hs.preimage hf.measurable),
    withDensity_apply _ hs]
  exact hf.setLIntegral_comp_preimage hs hg

private theorem measurePreserving_real_positive_radius_weighted {k : ℕ} {a b : ℝ}
    (ha : 0 < a) :
    MeasurePreserving (Subtype.val : Ioi (0 : ℝ) → ℝ)
      ((Measure.volumeIoiPow k).restrict (Subtype.val ⁻¹' Ioo a b))
      ((volume.restrict (Ioo a b)).withDensity (fun r : ℝ => ENNReal.ofReal (r ^ k))) := by
  have hsub := (measurePreserving_subtype_coe (measurableSet_Ioi (a := (0 : ℝ)))
    (μa := (volume : Measure ℝ))).restrict_preimage (measurableSet_Ioo (a := a) (b := b))
  have hJ : Ioo a b ∩ Ioi (0 : ℝ) = Ioo a b :=
    inter_eq_left.mpr fun r hr => ha.trans hr.1
  rw [Measure.restrict_restrict measurableSet_Ioo, hJ] at hsub
  have h := measurePreserving_withDensity_comp hsub
    (fun r : ℝ => ENNReal.ofReal (r ^ k)) (measurable_id.pow_const k).ennreal_ofReal
  simpa only [Measure.volumeIoiPow, restrict_withDensity
    (measurable_subtype_coe measurableSet_Ioo), Function.comp_def] using h

/-- Positive polar radius with its exact Jacobian pushes native sphere area
times radius measure onto the actual open-annulus volume. -/
theorem measurePreserving_native_polar_annulus {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (ha : 0 < a) :
    MeasurePreserving (fun p : sphere (0 : Domain n) 1 × ℝ => p.2 • p.1.val)
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        ((volume.restrict (Ioo a b)).withDensity (fun r : ℝ => ENNReal.ofReal (r ^ (n - 1)))))
      (volume.restrict {x : Domain n | a < ‖x‖ ∧ ‖x‖ < b}) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let σ := (volume : Measure (Domain n)).toSphere
  let A : Set (Domain n) := {x | a < ‖x‖ ∧ ‖x‖ < b}
  have hA : MeasurableSet A :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hinv := ((volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd).symm
    (homeomorphUnitSphereProd (Domain n)).toMeasurableEquiv
  have hsub := measurePreserving_subtype_coe
    (measurableSet_singleton (0 : Domain n)).compl (μa := (volume : Measure (Domain n)))
  rw [restrict_compl_singleton] at hsub
  have hrad : MeasurePreserving
      (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) => p.2.val • p.1.val)
      (σ.prod (Measure.volumeIoiPow (n - 1))) volume := by
    simpa only [Homeomorph.toMeasurableEquiv_symm_coe,
      homeomorphUnitSphereProd_symm_apply_coe, Function.comp_def,
      finrank_euclideanSpace, Fintype.card_fin] using hsub.comp hinv
  have hpre : (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      p.2.val • p.1.val) ⁻¹' A =
        (univ : Set (sphere (0 : Domain n) 1)) ×ˢ (Subtype.val ⁻¹' Ioo a b) := by
    ext p
    have hθ : ‖p.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.property
    simp only [mem_preimage, A, mem_setOf_eq, norm_smul, Real.norm_of_nonneg p.2.property.le,
      hθ, mul_one, mem_prod, mem_univ, mem_Ioo, true_and]
  have hradA := hrad.restrict_preimage hA
  rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ] at hradA
  have hparam := (MeasurePreserving.id σ).prod
    (measurePreserving_real_positive_radius_weighted (k := n - 1) (b := b) ha)
  have hm : Measurable (fun p : sphere (0 : Domain n) 1 × ℝ => p.2 • p.1.val) := by
    fun_prop
  refine ⟨hm, ?_⟩
  rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
  change Measure.map (fun p : sphere (0 : Domain n) 1 × ℝ => p.2 • p.1.val)
    (σ.prod ((volume.restrict (Ioo a b)).withDensity
      (fun r : ℝ => ENNReal.ofReal (r ^ (n - 1))))) = _
  rw [← hparam.map_eq, Measure.map_map hm hparam.measurable]
  exact hradA.map_eq

private theorem measurePreserving_radius_affine {s a b : ℝ} (hs : 0 < s) :
    MeasurePreserving (fun t : ℝ => s * (1 + t))
      (ENNReal.ofReal s • volume.restrict (Ioo a b))
      (volume.restrict (Ioo (s * (1 + a)) (s * (1 + b)))) := by
  have hf : Measurable (fun t : ℝ => s * (1 + t)) := by fun_prop
  have hglob : MeasurePreserving (fun t : ℝ => s * (1 + t))
      (ENNReal.ofReal s • volume) volume := by
    refine ⟨hf, ?_⟩
    rw [Measure.map_smul]
    have hmap : Measure.map (fun t : ℝ => s * (1 + t)) volume =
        Measure.map (fun r : ℝ => s * r) volume := by
      rw [show (fun t : ℝ => s * (1 + t)) = (fun r : ℝ => s * r) ∘ (fun t => 1 + t) by rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop),
        (measurePreserving_add_left volume (1 : ℝ)).map_eq]
    rw [hmap]
    simpa only [abs_of_pos hs] using Real.smul_map_volume_mul_left hs.ne'
  have h := hglob.restrict_preimage (measurableSet_Ioo
    (a := s * (1 + a)) (b := s * (1 + b)))
  have hpre : (fun t : ℝ => s * (1 + t)) ⁻¹' Ioo (s * (1 + a)) (s * (1 + b)) = Ioo a b := by
    ext t
    simp only [mem_preimage, mem_Ioo, mul_lt_mul_iff_right₀ hs, add_lt_add_iff_left]
  rwa [hpre, Measure.restrict_smul] at h

/-- The physical annular coordinate `s(1+t) theta` has Jacobian
`s * (s(1+t))^(n-1)` with respect to native sphere area times ordinary time. -/
theorem measurePreserving_annular_cylinder {n : ℕ} (hn : 0 < n)
    {s a b : ℝ} (hs : 0 < s) (ha : -1 < a) :
    MeasurePreserving (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (s * (1 + p.2)) • p.1.val)
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        ((volume.restrict (Ioo a b)).withDensity
          (fun t : ℝ => ENNReal.ofReal (s * (s * (1 + t)) ^ (n - 1)))))
      (volume.restrict {x : Domain n |
        s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}) := by
  letI : IsFiniteMeasure (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)) := by
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hR : 0 < s * (1 + a) := mul_pos hs (by linarith only [ha])
  have htime := measurePreserving_withDensity_comp
    (measurePreserving_radius_affine (a := a) (b := b) hs)
    (fun r : ℝ => ENNReal.ofReal (r ^ (n - 1)))
    (measurable_id.pow_const (n - 1)).ennreal_ofReal
  have hsource : (ENNReal.ofReal s • volume.restrict (Ioo a b)).withDensity
      ((fun r : ℝ => ENNReal.ofReal (r ^ (n - 1))) ∘ (fun t : ℝ => s * (1 + t))) =
      (volume.restrict (Ioo a b)).withDensity
        (fun t : ℝ => ENNReal.ofReal (s * (s * (1 + t)) ^ (n - 1))) := by
    rw [withDensity_smul_measure, ← withDensity_smul]
    · congr 1
      funext t
      exact (ENNReal.ofReal_mul hs.le).symm
    · exact ((measurable_const.mul (measurable_const.add measurable_id)).pow_const
        (n - 1)).ennreal_ofReal
  rw [hsource] at htime
  have hparam := (MeasurePreserving.id
    (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))).prod htime
  exact (measurePreserving_native_polar_annulus hn hR).comp hparam

/-- On the genuine positive annular parameter carrier, the physical map is
an actual measurable embedding. No injectivity on all real times is used. -/
theorem measurableEmbedding_annular_cylinder_param {n : ℕ} {s a b : ℝ}
    (hs : 0 < s) (ha : -1 < a) :
    MeasurableEmbedding (fun p : sphere (0 : Domain n) 1 × Ioo a b =>
      (s * (1 + p.2.val)) • p.1.val) := by
  letI : PolishSpace (sphere (0 : Domain n) 1) := isClosed_sphere.polishSpace
  letI : PolishSpace (Ioo a b) := isOpen_Ioo.polishSpace
  have hcont : Continuous (fun p : sphere (0 : Domain n) 1 × Ioo a b =>
      (s * (1 + p.2.val)) • p.1.val) := by fun_prop
  apply hcont.measurableEmbedding
  intro x y hxy
  have hx : 0 < s * (1 + x.2.val) := mul_pos hs (by linarith only [ha, x.2.property.1])
  have hy : 0 < s * (1 + y.2.val) := mul_pos hs (by linarith only [ha, y.2.property.1])
  have hnx : ‖x.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.1.property
  have hny : ‖y.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.1.property
  have hnorm := congrArg norm hxy
  simp only [norm_smul, Real.norm_of_nonneg hx.le, Real.norm_of_nonneg hy.le,
    hnx, hny, mul_one] at hnorm
  have htime : x.2.val = y.2.val := by nlinarith only [hnorm, hs]
  have hangle : x.1.val = y.1.val := by
    dsimp only at hxy
    rw [htime] at hxy
    have h := congrArg (fun z : Domain n => (s * (1 + y.2.val))⁻¹ • z) hxy
    simpa only [smul_smul, inv_mul_cancel₀ hy.ne', one_smul] using h
  exact Prod.ext (Subtype.ext hangle) (Subtype.ext htime)

/-- Weighted native sphere-times-open-time parameters preserve actual
annular volume, with the same physical parameter map as above. -/
theorem measurePreserving_annular_cylinder_param {n : ℕ} (hn : 0 < n)
    {s a b : ℝ} (hs : 0 < s) (ha : -1 < a) :
    MeasurePreserving (fun p : sphere (0 : Domain n) 1 × Ioo a b =>
      (s * (1 + p.2.val)) • p.1.val)
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        ((volume.comap (Subtype.val : Ioo a b → ℝ)).withDensity
          (fun t => ENNReal.ofReal (s * (s * (1 + t.val)) ^ (n - 1)))))
      (volume.restrict {x : Domain n |
        s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}) := by
  letI : IsFiniteMeasure (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)) := by
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : SigmaFinite (volume.comap (Subtype.val : Ioo a b → ℝ)) :=
    (measurePreserving_subtype_coe (measurableSet_Ioo (a := a) (b := b))
      (μa := (volume : Measure ℝ))).sigmaFinite
  have htime := measurePreserving_withDensity_comp
    (measurePreserving_subtype_coe (measurableSet_Ioo (a := a) (b := b))
      (μa := (volume : Measure ℝ)))
    (fun t : ℝ => ENNReal.ofReal (s * (s * (1 + t)) ^ (n - 1))) (by fun_prop)
  dsimp only [Function.comp_def] at htime
  exact (measurePreserving_annular_cylinder hn hs ha).comp
    ((MeasurePreserving.id _).prod htime)

/-- Arbitrary a.e. predicates, including nonmeasurable raw representatives,
transport in both directions through the actual positive annular parameters. -/
theorem ae_annular_cylinder_iff_param {n : ℕ} (hn : 0 < n)
    {s a b : ℝ} (hs : 0 < s) (ha : -1 < a) (P : Domain n → Prop) :
    (∀ᵐ x ∂volume.restrict {x : Domain n |
      s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}, P x) ↔
    ∀ᵐ p : sphere (0 : Domain n) 1 × Ioo a b
      ∂(Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.comap (Subtype.val : Ioo a b → ℝ)),
      P ((s * (1 + p.2.val)) • p.1.val) := by
  letI : IsFiniteMeasure (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)) := by
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : SigmaFinite (volume.comap (Subtype.val : Ioo a b → ℝ)) :=
    (measurePreserving_subtype_coe (measurableSet_Ioo (a := a) (b := b))
      (μa := (volume : Measure ℝ))).sigmaFinite
  let J : Ioo a b → ℝ≥0∞ := fun t => ENNReal.ofReal (s * (s * (1 + t.val)) ^ (n - 1))
  have hJ : Measurable J := by fun_prop
  rw [← (measurePreserving_annular_cylinder_param hn hs ha).map_eq,
    (measurableEmbedding_annular_cylinder_param hs ha).ae_map_iff,
    prod_withDensity_right hJ]
  change (∀ᵐ p : sphere (0 : Domain n) 1 × Ioo a b
    ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
      (volume.comap (Subtype.val : Ioo a b → ℝ))).withDensity (J ∘ Prod.snd),
      P ((s * (1 + p.2.val)) • p.1.val)) ↔ _
  rw [ae_withDensity_iff (hJ.comp measurable_snd)]
  have hpos (p : sphere (0 : Domain n) 1 × Ioo a b) : J p.2 ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    exact mul_pos hs (pow_pos (mul_pos hs (by linarith only [ha, p.2.property.1])) _)
  simp only [Function.comp_def, hpos, Ne, not_false_eq_true, true_implies]

/-- Exact Bochner change of variables for the original function, with the
native sphere-time measure and the physical radial Jacobian. -/
theorem integral_annular_cylinder {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s a b : ℝ} (hs : 0 < s) (ha : -1 < a) (f : Domain n → E) :
    (∫ x in {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}, f x) =
      ∫ p : sphere (0 : Domain n) 1 × ℝ,
        (s * (s * (1 + p.2)) ^ (n - 1)) • f ((s * (1 + p.2)) • p.1.val)
        ∂(Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
          (volume.restrict (Ioo a b)) := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := volume.comap (Subtype.val : Ioo a b → ℝ)
  let J : Ioo a b → ℝ≥0∞ := fun t => ENNReal.ofReal (s * (s * (1 + t.val)) ^ (n - 1))
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : SigmaFinite ν :=
    (measurePreserving_subtype_coe (measurableSet_Ioo (a := a) (b := b))
      (μa := (volume : Measure ℝ))).sigmaFinite
  have hJ : Measurable J := by fun_prop
  have hm := measurePreserving_annular_cylinder_param (b := b) hn hs ha
  have he := measurableEmbedding_annular_cylinder_param (n := n) (b := b) hs ha
  have hparam := (MeasurePreserving.id σ).prod
    (measurePreserving_subtype_coe (measurableSet_Ioo (a := a) (b := b))
      (μa := (volume : Measure ℝ)))
  calc
    _ = ∫ p : sphere (0 : Domain n) 1 × Ioo a b,
        f ((s * (1 + p.2.val)) • p.1.val) ∂σ.prod (ν.withDensity J) :=
      (hm.integral_comp he f).symm
    _ = ∫ p : sphere (0 : Domain n) 1 × Ioo a b,
        (J p.2).toReal • f ((s * (1 + p.2.val)) • p.1.val) ∂σ.prod ν := by
      rw [prod_withDensity_right hJ]
      exact integral_withDensity_eq_integral_toReal_smul
        (show Measurable (fun p : sphere (0 : Domain n) 1 × Ioo a b => J p.2) from
          hJ.comp measurable_snd)
        (ae_of_all _ fun p => ENNReal.ofReal_lt_top) _
    _ = ∫ p : sphere (0 : Domain n) 1 × Ioo a b,
        (s * (s * (1 + p.2.val)) ^ (n - 1)) •
          f ((s * (1 + p.2.val)) • p.1.val) ∂σ.prod ν := by
      apply integral_congr_ae
      apply ae_of_all
      intro p
      have hnonneg : 0 ≤ s * (s * (1 + p.2.val)) ^ (n - 1) :=
        mul_nonneg hs.le (pow_nonneg (mul_pos hs (by linarith only [ha, p.2.property.1])).le _)
      exact congrArg (fun r : ℝ => r • f ((s * (1 + p.2.val)) • p.1.val))
        (ENNReal.toReal_ofReal hnonneg)
    _ = _ := hparam.integral_comp
      (MeasurableEmbedding.id.prodMap (MeasurableEmbedding.subtype_coe measurableSet_Ioo))
      (fun p : sphere (0 : Domain n) 1 × ℝ =>
        (s * (s * (1 + p.2)) ^ (n - 1)) • f ((s * (1 + p.2)) • p.1.val))

end StratificationTheory
