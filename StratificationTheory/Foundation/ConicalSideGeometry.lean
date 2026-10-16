module

public import StratificationTheory.Foundation.CubicalConeGeometry
public import StratificationTheory.Foundation.CylinderSurfaceProductMeasure

/-!
# Physical parallel sides of native face cones

The same literal degree-zero extension is evaluated on actual parallel
lateral planes. Orthogonal coordinates identify their true Euclidean metric
and native Hausdorff measure, including the sqrt(2) height Jacobian.
-/

public section
open HarmonicMaps MeasureTheory Set
open scoped BigOperators
namespace StratificationTheory

/-- The literal degree-zero extension on parallel lateral planes has the
original raw reciprocal-parameter slice. Positive offsets below twice the
height satisfy all actual spatial cone inequalities. -/
theorem native_face_cone_parallel_side_slice {n : ℕ} {E : Type*}
    (w : Domain (n + 1) → E) {δ t : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hδt : δ < 2 * t)
    (x : Domain n) (hx : ∀ i : Fin n, |x i| < t) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let W : Domain ((n + 1) + 1) → E := fun y => w (((e y).2 0)⁻¹ • (e y).1)
    let γ := e.symm (b.symm (x, EuclideanSpace.single (0 : Fin 1) (t - δ)),
      EuclideanSpace.single (0 : Fin 1) t)
    W γ = w (b.symm (t⁻¹ • x, EuclideanSpace.single (0 : Fin 1) (1 - δ / t))) ∧
      (e γ).2 0 - (b (e γ).1).2 0 = δ ∧
      (∀ i : Fin (n + 1), |(e γ).1 i| < (e γ).2 0) := by
  intro b e W γ
  have hs : t⁻¹ • EuclideanSpace.single (0 : Fin 1) (t - δ) =
      EuclideanSpace.single (0 : Fin 1) (1 - δ / t) := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul]
    field_simp
  have hraw : W γ = w (b.symm (t⁻¹ • x,
      EuclideanSpace.single (0 : Fin 1) (1 - δ / t))) := by
    dsimp only [W, γ]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply, ite_true]
    rw [← b.symm.map_smul]
    change w (b.symm (t⁻¹ • x, t⁻¹ • EuclideanSpace.single (0 : Fin 1) (t - δ))) = _
    rw [hs]
  refine ⟨hraw, ?_, ?_⟩
  · simp only [γ, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
    ring
  · simp only [γ, e.apply_symm_apply, PiLp.single_apply, ite_true]
    intro i
    refine Fin.addCases (fun j : Fin n => ?_) (fun j : Fin 1 => ?_) i
    · simpa [b, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd] using hx j
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have h : |t - δ| < t := abs_lt.mpr ⟨by linarith only [hδt], by linarith only [hδ]⟩
      simpa [b, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd] using h

/-- The parallel lateral planes have actual Euclidean isometric coordinates
when the common height coordinate is normalized by sqrt(2). -/
theorem isometry_native_cone_lateral_chart (n : ℕ) (δ : ℝ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2 - δ)),
        EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2))
    Isometry Γ := by
  intro b e Γ
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hsub : Γ x - Γ y = e.symm
      (b.symm ((b x).1 - (b y).1,
        EuclideanSpace.single (0 : Fin 1) (((b x).2 0 - (b y).2 0) / Real.sqrt 2)),
       EuclideanSpace.single (0 : Fin 1) (((b x).2 0 - (b y).2 0) / Real.sqrt 2)) := by
    dsimp only [Γ]
    rw [← map_sub]
    congr 1
    apply Prod.ext
    · change b.symm _ - b.symm _ = _
      rw [← map_sub]
      congr 1
      apply Prod.ext
      · rfl
      · change EuclideanSpace.single (0 : Fin 1) _ - EuclideanSpace.single 0 _ = _
        rw [← PiLp.single_sub]
        congr 1
        ring
    · change EuclideanSpace.single (0 : Fin 1) _ - EuclideanSpace.single 0 _ = _
      rw [← PiLp.single_sub]
      congr 1
      ring
  rw [hsub, norm_sq_finAddEquivProd_symm, norm_sq_finAddEquivProd_symm]
  simp only [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  have hsource : ‖x - y‖ ^ 2 = ‖(b x).1 - (b y).1‖ ^ 2 +
      ((b x).2 0 - (b y).2 0) ^ 2 := by
    have h := norm_sq_finAddEquivProd_symm (n := n) (m := 1)
      ((b x).1 - (b y).1, (b x).2 - (b y).2)
    rw [← Prod.mk_sub_mk, ← map_sub, b.symm_apply_apply] at h
    have hOne : ‖(b x).2 - (b y).2‖ = |(b x).2 0 - (b y).2 0| := by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using
        (isometry_domainOne_eval.dist_eq (b x).2 (b y).2).symm
    rw [map_sub] at h
    change ‖x - y‖ ^ 2 = ‖(b x).1 - (b y).1‖ ^ 2 + ‖(b x).2 - (b y).2‖ ^ 2 at h
    rw [hOne, sq_abs] at h
    exact h
  rw [hsource]
  field_simp
  nlinarith only [hsqrt2]

/-- The same normalized lateral chart parametrizes the whole actual affine
hyperplane and preserves its native codimension-one Hausdorff measure. -/
theorem measurePreserving_native_cone_lateral_chart (n : ℕ) (δ : ℝ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2 - δ)),
        EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2))
    let P : Set (Domain ((n + 1) + 1)) :=
      {y | (e y).2 0 - (b (e y).1).2 0 = δ}
    range Γ = P ∧ MeasurePreserving Γ volume
      ((Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict P) := by
  intro b e Γ P
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hrange : range Γ = P := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      change (e (Γ y)).2 0 - (b (e (Γ y)).1).2 0 = δ
      simp only [Γ, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
      ring
    · intro hz
      refine ⟨b.symm ((b (e z).1).1,
        EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2 * (e z).2 0)), ?_⟩
      apply e.injective
      simp only [Γ, b.apply_symm_apply, e.apply_symm_apply, PiLp.single_apply, ite_true]
      have hdiv : Real.sqrt 2 * (e z).2 0 / Real.sqrt 2 = (e z).2 0 := by
        field_simp
      rw [hdiv]
      apply Prod.ext
      · apply b.injective
        rw [b.apply_symm_apply]
        apply Prod.ext
        · rfl
        · ext i
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          simp only [PiLp.single_apply, ite_true]
          change (e z).2 0 - (b (e z).1).2 0 = δ at hz
          linarith only [hz]
      · ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp only [PiLp.single_apply, ite_true]
  refine ⟨hrange, (isometry_native_cone_lateral_chart n δ).continuous.measurable, ?_⟩
  have h := (isometry_native_cone_lateral_chart n δ).map_euclideanHausdorffMeasure (d := n + 1)
  change Measure.map Γ (Measure.euclideanHausdorffMeasure (n + 1)) = _ at h
  have hvol : (Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain (n + 1))) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Domain (n + 1)))
  rw [hvol] at h
  rw [hrange] at h
  exact h

private theorem map_native_time_scaling (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let D : Domain (n + 1) → Domain (n + 1) := fun y => b.symm ((b y).1, r • (b y).2)
    Measure.map D volume = ENNReal.ofReal |r⁻¹| • volume := by
  intro b D
  let A : Domain n × Domain 1 → Domain n × Domain 1 := Prod.map id (r • ·)
  have hAmeas : Measurable A := measurable_id.prodMap (measurable_const_smul r)
  have hA : Measure.map A ((volume : Measure (Domain n)).prod (volume : Measure (Domain 1))) =
      ENNReal.ofReal |r⁻¹| • ((volume : Measure (Domain n)).prod (volume : Measure (Domain 1))) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_const_smul r), Measure.map_id,
      Measure.map_addHaar_smul volume hr]
    simpa using
      (Measure.prod_smul_right (μ := (volume : Measure (Domain n)))
        (ν := (volume : Measure (Domain 1))) (ENNReal.ofReal |r⁻¹|))
  have hb := measurePreserving_finAddEquivProd n 1
  have hbs := measurePreserving_finAddEquivProd_symm n 1
  calc
    _ = Measure.map b.symm (Measure.map A (Measure.map b volume)) := by
      rw [Measure.map_map hAmeas b.continuous.measurable,
        Measure.map_map b.symm.continuous.measurable (hAmeas.comp b.continuous.measurable)]
      rfl
    _ = _ := by rw [hb.map_eq, hA, Measure.map_smul, hbs.map_eq]

/-- The unnormalized physical-height chart has the exact sqrt(2) surface
Jacobian for the actual native affine hyperplane measure. -/
theorem map_native_cone_lateral_height_chart (n : ℕ) (δ : ℝ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 - δ)),
        EuclideanSpace.single (0 : Fin 1) ((b y).2 0))
    let P : Set (Domain ((n + 1) + 1)) :=
      {y | (e y).2 0 - (b (e y).1).2 0 = δ}
    Measure.map Γ volume = ENNReal.ofReal ((Real.sqrt 2)⁻¹) •
      ((Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict P) := by
  intro b e Γ P
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let D : Domain (n + 1) → Domain (n + 1) :=
    fun y => b.symm ((b y).1, Real.sqrt 2 • (b y).2)
  let Γ₀ : Domain (n + 1) → Domain ((n + 1) + 1) := fun y =>
    e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2 - δ)),
      EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2))
  have hcomp : Γ = Γ₀ ∘ D := by
    funext y
    dsimp only [Γ, Γ₀, D, Function.comp_apply]
    rw [b.apply_symm_apply]
    have hreal : (Real.sqrt 2 • (b y).2) 0 / Real.sqrt 2 = (b y).2 0 := by
      change Real.sqrt 2 * (b y).2 0 / Real.sqrt 2 = _
      field_simp
    rw [hreal]
  have hD := map_native_time_scaling n hsqrtpos.ne'
  have hΓ := (measurePreserving_native_cone_lateral_chart n δ).2
  have hDmeas : Measurable D :=
    (b.symm.continuous.comp ((continuous_fst.comp b.continuous).prodMk
      ((continuous_snd.comp b.continuous).const_smul (Real.sqrt 2)))).measurable
  have hΓmeas : Measurable Γ₀ := (isometry_native_cone_lateral_chart n δ).continuous.measurable
  change Measure.map D volume = ENNReal.ofReal |(Real.sqrt 2)⁻¹| • volume at hD
  rw [hcomp, ← Measure.map_map hΓmeas hDmeas,
    hD, Measure.map_smul, hΓ.map_eq, abs_of_pos (inv_pos.mpr hsqrtpos)]

end StratificationTheory
