module

public import StratificationTheory.Foundation.CylinderPointCoordinates
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
import StratificationTheory.Foundation.CylinderSurfaceMeasure

/-!
# Native cylinder parametrization and almost-everywhere transport

The actual sphere-interval parametrization is a measurable embedding and
preserves native surface measure exactly. Its embedding property transfers
arbitrary almost-everywhere predicates in both directions.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal

namespace StratificationTheory

/-- The canonical physical sphere-time parametrization is a measurable
embedding with native coefficient-one product measure. -/
theorem unitCylinder_param_measurePreserving {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let p : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun z =>
      ⟨e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val), unitCylinder_param_mem z.1 z.2⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
    MeasurableEmbedding p ∧ MeasurePreserving p (σ.prod ν)
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)) := by
  intro e p σ ν
  let C := unitCylinder n a b
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hsingle (t : ℝ) : EuclideanSpace.single (0 : Fin 1) t = τ.symm t := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  have hpCont : Continuous p := by
    apply Continuous.subtype_mk
    simp_rw [hsingle]
    exact e.symm.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (τ.symm.continuous.comp (continuous_subtype_val.comp continuous_snd)))
  have hpInj : Function.Injective p := by
    intro x y hxy
    have h := congrArg (fun z : unitCylinder n a b => e z.val) hxy
    change e (e.symm (x.1.val, EuclideanSpace.single (0 : Fin 1) x.2.val)) =
      e (e.symm (y.1.val, EuclideanSpace.single (0 : Fin 1) y.2.val)) at h
    rw [e.apply_symm_apply, e.apply_symm_apply] at h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · apply Subtype.ext
      have ht := congrArg (fun z : Domain n × Domain 1 => z.2 0) h
      simpa only [PiLp.single_apply, ite_true] using ht
  letI : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hpEmb : MeasurableEmbedding p := (hpCont.isClosedEmbedding hpInj).measurableEmbedding
  have hσ : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI := hσ
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  letI : SigmaFinite ν := htime.sigmaFinite
  let j : sphere (0 : Domain n) 1 × Icc a b → sphere (0 : Domain n) 1 × ℝ :=
    fun z => (z.1, z.2.val)
  have hj : MeasurePreserving j (σ.prod ν) (σ.prod (volume.restrict (Icc a b))) :=
    (MeasurePreserving.id σ).prod htime
  let emb : sphere (0 : Domain n) 1 × ℝ → Domain (n + 1) :=
    fun z => e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2)
  have hemb : Measurable emb := by
    apply Continuous.measurable
    simp_rw [emb, hsingle]
    exact e.symm.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (τ.symm.continuous.comp continuous_snd))
  have hmap : Measure.map emb (σ.prod (volume.restrict (Icc a b))) =
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C :=
    map_cylinder_surface_product_Icc_eq_native_unitCylinder hn a b
  have hC : MeasurableSet C := (isClosed_native_cylinder_surface_Icc n a b).measurableSet
  have hval : Measure.map (Subtype.val : C → Domain (n + 1))
      (Measure.euclideanHausdorffMeasure n : Measure C) =
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C := by
    simpa only [Subtype.range_coe] using
      (Isometry.map_euclideanHausdorffMeasure (d := n)
        (isometry_subtype_coe : Isometry (Subtype.val : C → Domain (n + 1))))
  refine ⟨hpEmb, hpCont.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe hC).map_injective
  rw [Measure.map_map measurable_subtype_coe hpCont.measurable]
  have heq : (Subtype.val : C → Domain (n + 1)) ∘ p = emb ∘ j := rfl
  rw [heq, ← Measure.map_map hemb hj.measurable, hj.map_eq, hmap, hval]


/-- Almost-everywhere statements on the native cylinder are equivalent to
statements on its true sphere-interval product, without measurability of the
predicate. -/
theorem ae_unitCylinder_iff_param {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (P : unitCylinder n a b → Prop) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
    (∀ᵐ c ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)), P c) ↔
      ∀ᵐ z : sphere (0 : Domain n) 1 × Icc a b ∂σ.prod ν,
        P ⟨e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val),
          unitCylinder_param_mem z.1 z.2⟩ := by
  intro e σ ν
  obtain ⟨hEmb, hMP⟩ := unitCylinder_param_measurePreserving hn a b
  rw [← hMP.map_eq]
  exact hEmb.ae_map_iff

/-- One angular full-measure set carrying a property at every closed time
produces that property on the actual native physical cylinder. -/
theorem ae_unitCylinder_of_ae_forall_time {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (P : unitCylinder n a b → Prop)
    (hP : ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t : Icc a b,
        P ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (θ.val, EuclideanSpace.single (0 : Fin 1) t.val), unitCylinder_param_mem θ t⟩) :
    ∀ᵐ c ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)), P c := by
  apply (ae_unitCylinder_iff_param hn P).mpr
  have hprod := (Measure.quasiMeasurePreserving_fst
    (ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ))).ae hP
  exact hprod.mono (fun z hz => hz z.2)

/-- The two time faces are null for native physical cylinder measure, so
almost every closed-cylinder point has strictly interior time. -/
theorem ae_unitCylinder_time_mem_Ioo {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    ∀ᵐ c : unitCylinder n a b ∂Measure.euclideanHausdorffMeasure n,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) c.val).2 0 ∈ Ioo a b := by
  apply (ae_unitCylinder_iff_param hn _).mpr
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  have htime : MeasurePreserving (Subtype.val : Icc a b → ℝ) ν (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hI : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hparam : ∀ᵐ z : sphere (0 : Domain n) 1 × Icc a b
      ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod ν, z.2.val ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_snd.ae (htime.quasiMeasurePreserving.ae hI)
  filter_upwards [hparam] with z hz
  simpa only [ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true] using hz

end StratificationTheory
