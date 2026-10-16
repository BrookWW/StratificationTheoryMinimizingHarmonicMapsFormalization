module

public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import HarmonicMaps.Analysis.SphereSurfaceLocalBounds
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Native Hausdorff measure of bounded-time unit cylinders

Euclidean tangent-space charts with the actual time coordinate give finite
native surface measure on bounded-time embedded unit cylinders. Nonempty
intervals have positive surface measure, fixed-time faces are null, and
translation of time preserves the measure. Actual constant maps belong to
surface L2 and nonzero constants determine nonzero classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Module
open scoped ENNReal NNReal RealInnerProductSpace

namespace StratificationTheory

private theorem exists_cylinder_chart_image_finite {n : ℕ} (hn : 0 < n)
    (a b : ℝ) (θ : sphere (0 : Domain n) 1) :
    ∃ U : Set (sphere (0 : Domain n) 1), IsOpen U ∧ θ ∈ U ∧
      ∃ B : Set (Domain (n + 1)),
        (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) B ≠ ⊤ ∧
        (a = b → (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) B = 0) ∧
        ∀ θ' ∈ U, ∀ t ∈ Icc a b,
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
            (θ'.val, EuclideanSpace.single (0 : Fin 1) t) ∈ B := by
  have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
  let H := (ℝ ∙ θ.val)ᗮ
  let P := WithLp 2 (H × ℝ)
  let j := WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ
  let pH : P →L[ℝ] H := (ContinuousLinearMap.fst ℝ H ℝ).comp j.toContinuousLinearMap
  let pT : P →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ H ℝ).comp j.toContinuousLinearMap
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let ψ : H → Domain n := fun u => ‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u)
  let F : P → Domain (n + 1) := fun z => e.symm (ψ (pH z), τ.symm (pT z))
  let K : Set P := j ⁻¹' (closedBall (0 : H) (1 / 2) ×ˢ Icc a b)
  have hK : IsCompact K := j.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_closedBall (0 : H) (1 / 2)).prod isCompact_Icc)
  have hdimH : finrank ℝ H = n - 1 := by
    have hθ0 : θ.val ≠ 0 := norm_ne_zero_iff.mp (by rw [hθ]; norm_num)
    have h := (ℝ ∙ θ.val).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hθ0, finrank_euclideanSpace_fin] at h
    dsimp only [H]
    omega
  have hdimP : finrank ℝ P = n := by
    rw [(WithLp.linearEquiv 2 ℝ (H × ℝ)).finrank_eq,
      finrank_prod, finrank_self, hdimH]
    omega
  have hLipψ := (sphereSurface_chart_lipschitz θ.val hθ (1 / 2)
    (by norm_num) (by norm_num)).1
  have hPH : MapsTo pH K (closedBall (0 : H) (1 / 2)) := fun z hz => hz.1
  have hLips := hLipψ.comp pH.lipschitz.lipschitzOnWith hPH
  have hLipt := τ.symm.lipschitz.comp pT.lipschitz
  have hPair := hLips.prodMk hLipt.lipschitzOnWith
  have hLipF := e.symm.lipschitz.lipschitzOnWith.comp hPair
    (mapsTo_univ _ _)
  have hBound := euclideanHausdorff_lipschitzOn_image_le_volume hLipF (Subset.refl K)
  rw [hdimP] at hBound
  have hKVol : (volume : Measure P) K ≠ ⊤ := hK.measure_ne_top
  have hImage : (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' K) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hKVol) hBound
  have hImageZero (hab : a = b) :
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' K) = 0 := by
    have hv := (WithLp.volume_preserving_ofLp H ℝ).measure_preimage
      (s := closedBall (0 : H) (1 / 2) ×ˢ Icc a b)
      (measurableSet_closedBall.prod measurableSet_Icc).nullMeasurableSet
    change (volume : Measure P) K =
      ((volume : Measure H).prod (volume : Measure ℝ)) (closedBall 0 (1 / 2) ×ˢ Icc a b) at hv
    have hKZero : (volume : Measure P) K = 0 := by
      simpa only [Measure.prod_prod, Real.volume_Icc, hab, sub_self, ENNReal.ofReal_zero, mul_zero] using hv
    have hz := hBound
    rw [hKZero, mul_zero] at hz
    exact le_antisymm hz bot_le
  let U : Set (sphere (0 : Domain n) 1) :=
    {θ' | 0 < inner ℝ θ.val θ'.val ∧
      ‖(inner ℝ θ.val θ'.val)⁻¹ • θ'.val - θ.val‖ < 1 / 2}
  obtain ⟨hU, hθU, hCover, _⟩ := sphereSurface_chart_neighborhood θ.val hθ (1 / 2) (by norm_num)
  have hθU' : θ ∈ U := hθU
  refine ⟨U, hU, hθU', F '' K, hImage, hImageZero, ?_⟩
  intro θ' hθ' t ht
  obtain ⟨u, hu, hup⟩ := hCover θ' hθ'
  refine ⟨j.symm (u, t), ?_, ?_⟩
  · change j (j.symm (u, t)) ∈ closedBall (0 : H) (1 / 2) ×ˢ Icc a b
    rw [j.apply_symm_apply]
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hu.le, ht⟩
  · have htime : τ.symm t = EuclideanSpace.single (0 : Fin 1) t := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [τ, PiLp.equivOfUnique]
    change e.symm (ψ ((j (j.symm (u, t))).1), τ.symm ((j (j.symm (u, t))).2)) = _
    rw [j.apply_symm_apply, htime]
    change e.symm (ψ u, EuclideanSpace.single (0 : Fin 1) t) = _
    dsimp only [ψ]
    rw [hup]


/-- A bounded-time actual embedded unit cylinder has finite normalized
Hausdorff measure in its surface dimension. -/
theorem native_cylinder_surface_Icc_measure_ne_top {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b} ≠ ⊤ := by
  classical
  let S := sphere (0 : Domain n) 1
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  choose U hU hθU B hB _hBZero hCover using exists_cylinder_chart_image_finite hn a b
  have hcoverSphere : (univ : Set S) ⊆ ⋃ θ : S, U θ := by
    intro θ _
    exact mem_iUnion.mpr ⟨θ, hθU θ⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcoverSphere
  have hsub : {y : Domain (n + 1) | (e y).1 ∈ S ∧ (e y).2 0 ∈ Icc a b} ⊆
      ⋃ θ ∈ t, B θ := by
    intro y hy
    let θ : S := ⟨(e y).1, hy.1⟩
    obtain ⟨θ₀, hθ₀t, hθ₀U⟩ := mem_iUnion₂.mp (ht (mem_univ θ))
    have hmem := hCover θ₀ θ hθ₀U ((e y).2 0) hy.2
    change e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) ∈ B θ₀ at hmem
    rw [cylinder_coordinates_inverse_left n y] at hmem
    exact mem_iUnion₂.mpr ⟨θ₀, hθ₀t, hmem⟩
  have hsum : (∑ θ ∈ t, (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))
      (B θ)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr (fun θ _ => (hB θ).lt_top)).ne
  exact ne_top_of_le_ne_top hsum
    ((measure_mono hsub).trans (measure_biUnion_finset_le t B))

/-- The actual closed-time embedded unit cylinder is a closed measurable set. -/
theorem isClosed_native_cylinder_surface_Icc (n : ℕ) (a b : ℝ) :
    IsClosed {y : Domain (n + 1) |
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ sphere (0 : Domain n) 1 ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b} := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  have ht : Continuous (fun y : Domain (n + 1) => (e y).2 0) :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp e.continuous.snd
  exact (isClosed_sphere.preimage e.continuous.fst).inter (isClosed_Icc.preimage ht)

/-- Every actual ambient constant has finite L2 membership on the physical
bounded-time cylinder with the source's normalized surface Hausdorff measure. -/
theorem memLp_const_native_cylinder_surface_Icc {n q : ℕ} (hn : 0 < n)
    (a b : ℝ) (c : Ambient q) :
    MemLp (fun _ : Domain (n + 1) => c) 2
      ((Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict
        {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
            sphere (0 : Domain n) 1 ∧
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b}) := by
  letI : IsFiniteMeasure
      ((Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict
        {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
            sphere (0 : Domain n) 1 ∧
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b}) :=
    isFiniteMeasure_restrict.mpr (native_cylinder_surface_Icc_measure_ne_top hn a b)
  exact memLp_const c

/-- A nondegenerate bounded-time actual unit cylinder has positive normalized
Hausdorff measure in its surface dimension. -/
theorem native_cylinder_surface_Icc_measure_pos {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (hab : a < b) :
    0 < (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b} := by
  let θ : sphere (0 : Domain n) 1 :=
    ⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1, by
      rw [mem_sphere_zero_iff_norm]
      simp⟩
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  let H := (ℝ ∙ θ.val)ᗮ
  let P := WithLp 2 (H × ℝ)
  let j := WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ
  let pH : P →L[ℝ] H := (ContinuousLinearMap.fst ℝ H ℝ).comp j.toContinuousLinearMap
  let pT : P →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ H ℝ).comp j.toContinuousLinearMap
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let ψ : H → Domain n := fun u => ‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u)
  let F : P → Domain (n + 1) := fun z => e.symm (ψ (pH z), τ.symm (pT z))
  let K : Set P := j ⁻¹' (closedBall (0 : H) (1 / 2) ×ˢ Icc a b)
  let C : Set (Domain (n + 1)) :=
    {y | (e y).1 ∈ sphere (0 : Domain n) 1 ∧ (e y).2 0 ∈ Icc a b}
  have hdimH : finrank ℝ H = n - 1 := by
    have hθ0 : θ.val ≠ 0 := norm_ne_zero_iff.mp (by rw [hθ]; norm_num)
    have h := (ℝ ∙ θ.val).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hθ0, finrank_euclideanSpace_fin] at h
    dsimp only [H]
    omega
  have hdimP : finrank ℝ P = n := by
    rw [(WithLp.linearEquiv 2 ℝ (H × ℝ)).finrank_eq,
      finrank_prod, finrank_self, hdimH]
    omega
  have hKpos : 0 < (volume : Measure P) K := by
    have hv := (WithLp.volume_preserving_ofLp H ℝ).measure_preimage
      (s := closedBall (0 : H) (1 / 2) ×ˢ Icc a b)
      (measurableSet_closedBall.prod measurableSet_Icc).nullMeasurableSet
    change (volume : Measure P) K =
      ((volume : Measure H).prod (volume : Measure ℝ)) (closedBall 0 (1 / 2) ×ˢ Icc a b) at hv
    rw [hv, Measure.prod_prod]
    have hHpos : 0 < (volume : Measure H) (closedBall 0 (1 / 2)) :=
      (isOpen_ball.measure_pos (volume : Measure H)
        ⟨0, mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)⟩).trans_le
          (measure_mono ball_subset_closedBall)
    have hTpos : 0 < (volume : Measure ℝ) (Icc a b) :=
      ((Measure.measure_Ioo_pos volume).mpr hab).trans_le (measure_mono Ioo_subset_Icc_self)
    exact ENNReal.mul_pos hHpos.ne' hTpos.ne'
  have hImageSub : F '' K ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    change (e (e.symm (ψ (pH z), τ.symm (pT z)))).1 ∈ sphere (0 : Domain n) 1 ∧
      (e (e.symm (ψ (pH z), τ.symm (pT z)))).2 0 ∈ Icc a b
    rw [e.apply_symm_apply]
    constructor
    · exact mem_sphere_zero_iff_norm.mpr (sphereSurface_chart_geometry θ.val hθ (pH z)).2.1
    · simpa [τ, PiLp.equivOfUnique, pT] using hz.2
  let Kψ : ℝ≥0 := Real.toNNReal ((1 + (1 / 2 : ℝ)) / (1 - 1 / 2))
  let Kj : ℝ≥0 := ‖j.symm.toContinuousLinearMap‖₊
  let Kτ : ℝ≥0 := ‖τ.toContinuousLinearMap‖₊
  let Ke : ℝ≥0 := ‖e.toContinuousLinearMap‖₊
  let Kmax : ℝ≥0 := max Kψ Kτ
  let K0 : ℝ≥0 := Kj * Kmax * Ke
  have hAnti : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ K0 * dist (F x) (F y) := by
    intro x hx y hy
    have hu : dist (pH x) (pH y) ≤ Kψ * dist (ψ (pH x)) (ψ (pH y)) := by
      have hu : ‖pH x‖ ≤ (1 / 2 : ℝ) := by
        simpa only [mem_closedBall, dist_zero_right, pH, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_coe] using hx.1
      have hv : ‖pH y‖ ≤ (1 / 2 : ℝ) := by
        simpa only [mem_closedBall, dist_zero_right, pH, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_coe] using hy.1
      simpa only [dist_eq_norm, ψ, Kψ, Real.coe_toNNReal _
        (by norm_num : (0 : ℝ) ≤ (1 + (1 / 2 : ℝ)) / (1 - 1 / 2))] using
        (sphereSurface_chart_distortion θ.val hθ (1 / 2) (by norm_num)
          (pH x) (pH y) hu hv).2
    have ht : dist (pT x) (pT y) ≤ Kτ * dist (τ.symm (pT x)) (τ.symm (pT y)) := by
      simpa only [τ.apply_symm_apply] using
        τ.lipschitz.dist_le_mul (τ.symm (pT x)) (τ.symm (pT y))
    have hp : dist (j x) (j y) ≤ Kmax *
        dist (ψ (pH x), τ.symm (pT x)) (ψ (pH y), τ.symm (pT y)) := by
      change max (dist (pH x) (pH y)) (dist (pT x) (pT y)) ≤ _
      apply max_le
      · apply hu.trans
        apply mul_le_mul
        · exact_mod_cast le_max_left Kψ Kτ
        · rw [Prod.dist_eq]
          exact le_max_left _ _
        · exact dist_nonneg
        · exact NNReal.coe_nonneg _
      · apply ht.trans
        apply mul_le_mul
        · exact_mod_cast le_max_right Kψ Kτ
        · rw [Prod.dist_eq]
          exact le_max_right _ _
        · exact dist_nonneg
        · exact NNReal.coe_nonneg _
    have hj : dist x y ≤ Kj * dist (j x) (j y) := by
      simpa only [j.symm_apply_apply] using j.symm.lipschitz.dist_le_mul (j x) (j y)
    have he : dist (ψ (pH x), τ.symm (pT x)) (ψ (pH y), τ.symm (pT y)) ≤
        Ke * dist (F x) (F y) := by
      simpa only [F, e.apply_symm_apply] using e.lipschitz.dist_le_mul (F x) (F y)
    calc
      dist x y ≤ Kj * dist (j x) (j y) := hj
      _ ≤ Kj * (Kmax * dist (ψ (pH x), τ.symm (pT x)) (ψ (pH y), τ.symm (pT y))) :=
        mul_le_mul_of_nonneg_left hp (NNReal.coe_nonneg _)
      _ ≤ Kj * (Kmax * (Ke * dist (F x) (F y))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (NNReal.coe_nonneg _))
          (NNReal.coe_nonneg _)
      _ = K0 * dist (F x) (F y) := by simp only [K0, NNReal.coe_mul]; ring
  have hLower := volume_le_euclideanHausdorff_image_of_dist_le hAnti (Subset.refl K)
  rw [hdimP] at hLower
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hImageZero : (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' K) = 0 :=
    le_antisymm (by
      have hle := measure_mono (μ := (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))) hImageSub
      change (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) C = 0 at hzero
      simpa only [hzero] using hle) bot_le
  rw [hImageZero, mul_zero] at hLower
  exact not_le_of_gt hKpos hLower


/-- Each actual fixed-time face of the unit cylinder has zero normalized
Hausdorff measure in the cylinder's surface dimension. -/
theorem native_cylinder_surface_time_measure_zero {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 = a} = 0 := by
  classical
  let S := sphere (0 : Domain n) 1
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  choose U hU hθU B _hB hBZero hCover using exists_cylinder_chart_image_finite hn a a
  have hcoverSphere : (univ : Set S) ⊆ ⋃ θ : S, U θ := by
    intro θ _
    exact mem_iUnion.mpr ⟨θ, hθU θ⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcoverSphere
  have hsub : {y : Domain (n + 1) | (e y).1 ∈ S ∧ (e y).2 0 = a} ⊆
      ⋃ θ ∈ t, B θ := by
    intro y hy
    let θ : S := ⟨(e y).1, hy.1⟩
    obtain ⟨θ₀, hθ₀t, hθ₀U⟩ := mem_iUnion₂.mp (ht (mem_univ θ))
    have hmem := hCover θ₀ θ hθ₀U a (by simp : a ∈ Icc a a)
    have heq : e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) a) = y := by
      rw [← hy.2]
      exact cylinder_coordinates_inverse_left n y
    change e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) a) ∈ B θ₀ at hmem
    rw [heq] at hmem
    exact mem_iUnion₂.mpr ⟨θ₀, hθ₀t, hmem⟩
  apply le_antisymm _ bot_le
  calc
    _ ≤ ∑ θ ∈ t, (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (B θ) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le t B)
    _ = 0 := Finset.sum_eq_zero (fun θ _ => hBZero θ rfl)

/-- A nonzero actual ambient constant determines a nonzero L2 class on a
nondegenerate physical cylinder, using its native surface Hausdorff measure. -/
theorem toLp_const_native_cylinder_surface_Icc_ne_zero {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (hab : a < b) {c : Ambient q} (hc : c ≠ 0) :
    (memLp_const_native_cylinder_surface_Icc hn a b c).toLp
      (fun _ : Domain (n + 1) => c) ≠ 0 := by
  let C : Set (Domain (n + 1)) :=
    {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
        sphere (0 : Domain n) 1 ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b}
  let μ := (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C
  let hL : MemLp (fun _ : Domain (n + 1) => c) 2 μ := memLp_const_native_cylinder_surface_Icc hn a b c
  intro hz
  have hAE : (fun _ : Domain (n + 1) => c) =ᵐ[μ] (0 : Domain (n + 1) → Ambient q) := by
    apply (hL.toLp_eq_toLp_iff MemLp.zero).mp
    rw [MemLp.toLp_zero]
    exact hz
  have hmass : μ univ ≠ 0 := by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    exact (native_cylinder_surface_Icc_measure_pos hn hab).ne'
  have hAE' : ∀ᵐ x ∂μ.restrict univ, c = 0 := by
    rw [Measure.restrict_univ]
    change ∀ᵐ x ∂μ, c = 0 at hAE
    exact hAE
  obtain ⟨x, _hx, hcx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass hAE'
  exact hc hcx


/-- Removing the two fixed-time faces leaves the same actual restricted
surface measure on the embedded cylinder. -/
theorem native_cylinder_surface_Icc_restrict_eq_Ioo {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b} =
    (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b} := by
  have hface (t : ℝ) : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))),
      ¬((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
        sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 = t) := by
    apply ae_iff.mpr
    simpa only [not_not] using native_cylinder_surface_time_measure_zero hn t
  apply Measure.restrict_congr_set
  filter_upwards [hface a, hface b] with y ha hb
  apply propext
  constructor
  · intro hy
    have hna : (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ≠ a :=
      fun h => ha ⟨hy.1, h⟩
    have hnb : (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ≠ b :=
      fun h => hb ⟨hy.1, h⟩
    exact ⟨hy.1, lt_of_le_of_ne hy.2.1 hna.symm, lt_of_le_of_ne hy.2.2 hnb⟩
  · intro hy
    exact ⟨hy.1, hy.2.1.le, hy.2.2.le⟩

/-- Translating the actual time coordinate preserves the source's normalized
surface Hausdorff measure of every bounded-time unit cylinder. -/
theorem native_cylinder_surface_Icc_measure_time_translate (n : ℕ) (a b t : ℝ) :
    (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc (a + t) (b + t)} =
    (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          sphere (0 : Domain n) 1 ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Icc a b} := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let z : Domain (n + 1) := e.symm (0, EuclideanSpace.single (0 : Fin 1) t)
  let C : Set (Domain (n + 1)) := {y | (e y).1 ∈ sphere (0 : Domain n) 1 ∧
    (e y).2 0 ∈ Icc a b}
  let Ct : Set (Domain (n + 1)) := {y | (e y).1 ∈ sphere (0 : Domain n) 1 ∧
    (e y).2 0 ∈ Icc (a + t) (b + t)}
  have hspatial (y : Domain (n + 1)) : (e (y + z)).1 = (e y).1 := by
    rw [map_add]
    simp only [z, e.apply_symm_apply, Prod.fst_add, add_zero]
  have htime (y : Domain (n + 1)) : (e (y + z)).2 0 = (e y).2 0 + t := by
    rw [map_add]
    simp [z]
  have himage : (fun y : Domain (n + 1) => y + z) '' C = Ct := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e (x + z)).1 ∈ sphere (0 : Domain n) 1 ∧
        (e (x + z)).2 0 ∈ Icc (a + t) (b + t)
      rw [hspatial, htime]
      exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
    · intro hy
      have hsp := hspatial (y - z)
      have htm := htime (y - z)
      rw [sub_add_cancel] at hsp htm
      refine ⟨y - z, ?_, sub_add_cancel _ _⟩
      change (e (y - z)).1 ∈ sphere (0 : Domain n) 1 ∧ (e (y - z)).2 0 ∈ Icc a b
      refine ⟨by rw [← hsp]; exact hy.1, ?_, ?_⟩
      · have h := hy.2.1
        rw [htm] at h
        linarith
      · have h := hy.2.2
        rw [htm] at h
        linarith
  change (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) Ct = _
  rw [← himage]
  exact (isometry_add_right z).euclideanHausdorffMeasure_image C

end StratificationTheory
