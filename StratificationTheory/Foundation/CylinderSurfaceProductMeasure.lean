module

public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import StratificationTheory.Frozen.UnitCylinder
public import HarmonicMaps.Analysis.SphereSurfaceLocalBounds
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Native product measure of Euclidean cylinder surfaces

Central sphere coordinates together with unchanged time have arbitrarily
small distortion in the actual Euclidean parameter norm. Their sharp local
Hausdorff comparisons identify the complete embedded-cylinder surface measure
with native sphere area times real-time Lebesgue measure. Restriction to a
closed time interval gives the literal closed unit-cylinder measure.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Module Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace StratificationTheory

/-- The inverse canonical split has the Euclidean squared-norm identity. -/
theorem norm_sq_finAddEquivProd_symm {n m : ℕ} (p : Domain n × Domain m) :
    ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm p‖ ^ 2 =
      ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  let a := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv (m := n) (n := m)).symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin n ⊕ Fin m => ℝ))
  change ‖a.symm (WithLp.toLp 2 p)‖ ^ 2 = _
  rw [a.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]
  rfl

private theorem sum_squares_bound {A B T X Y L : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hxsq : X ^ 2 = A ^ 2 + T ^ 2) (hysq : Y ^ 2 = B ^ 2 + T ^ 2)
    (hAB : A ≤ L * B) : X ≤ L * Y := by
  have hA2 : A ^ 2 ≤ L ^ 2 * B ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hAB 2
  have hL2 : 1 ≤ L ^ 2 := by nlinarith only [hL]
  have hT2 : T ^ 2 ≤ L ^ 2 * T ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL2 (sq_nonneg T)
  apply (sq_le_sq₀ hX (mul_nonneg (le_trans zero_le_one hL) hY)).mp
  rw [hxsq, mul_pow, hysq, mul_add]
  exact add_le_add hA2 hT2

/-- The actual central sphere chart together with unchanged time has
Euclidean distortion constants approaching one on shrinking tangent balls. -/
theorem cylinder_surface_chart_distortion {n : ℕ} (θ : sphere (0 : Domain n) 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    let H := (ℝ ∙ θ.val)ᗮ
    let ψ : H → Domain n := fun u => ‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u)
    let F : WithLp 2 (H × ℝ) → Domain (n + 1) := fun z =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (ψ z.fst, EuclideanSpace.single (0 : Fin 1) z.snd)
    ∀ x y : WithLp 2 (H × ℝ), ‖x.fst‖ ≤ ε → ‖y.fst‖ ≤ ε →
      ‖F x - F y‖ ≤ (1 + ε) * ‖x - y‖ ∧
      ‖x - y‖ ≤ ((1 + ε) / (1 - ε)) * ‖F x - F y‖ := by
  intro H ψ F x y hx hy
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hSphere := sphereSurface_chart_distortion θ.val hθ ε hε1 x.fst y.fst hx hy
  have htarget : ‖F x - F y‖ ^ 2 =
      ‖ψ x.fst - ψ y.fst‖ ^ 2 + ‖x.snd - y.snd‖ ^ 2 := by
    change ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (ψ x.fst, EuclideanSpace.single (0 : Fin 1) x.snd) -
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (ψ y.fst, EuclideanSpace.single (0 : Fin 1) y.snd)‖ ^ 2 = _
    rw [← map_sub, norm_sq_finAddEquivProd_symm]
    change ‖ψ x.fst - ψ y.fst‖ ^ 2 +
      ‖EuclideanSpace.single (0 : Fin 1) x.snd - EuclideanSpace.single (0 : Fin 1) y.snd‖ ^ 2 = _
    rw [← PiLp.single_sub, PiLp.norm_single]
  have hsource : ‖x - y‖ ^ 2 = ‖x.fst - y.fst‖ ^ 2 + ‖x.snd - y.snd‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    rfl
  have hL : 1 ≤ 1 + ε := by linarith only [hε]
  have hK : 1 ≤ (1 + ε) / (1 - ε) :=
    (le_div_iff₀ (sub_pos.mpr hε1)).mpr (by linarith only [hε])
  exact ⟨sum_squares_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hL htarget hsource hSphere.1,
    sum_squares_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hK hsource htarget hSphere.2⟩


/-- Actual cylinder central coordinates are Lipschitz and inverse Lipschitz
on the tangent-ball carrier, with constants tending to one with its radius. -/
theorem cylinder_surface_chart_lipschitz {n : ℕ} (θ : sphere (0 : Domain n) 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    let H := (ℝ ∙ θ.val)ᗮ
    let ψ : H → Domain n := fun u => ‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u)
    let F : WithLp 2 (H × ℝ) → Domain (n + 1) := fun z =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (ψ z.fst, EuclideanSpace.single (0 : Fin 1) z.snd)
    let P : Set (WithLp 2 (H × ℝ)) := {z | ‖z.fst‖ ≤ ε}
    LipschitzOnWith (Real.toNNReal (1 + ε)) F P ∧
      AntilipschitzWith (Real.toNNReal ((1 + ε) / (1 - ε))) (fun z : P => F z.val) := by
  intro H ψ F P
  have hK : 0 ≤ (1 + ε) / (1 - ε) :=
    div_nonneg (by linarith only [hε]) (sub_pos.mpr hε1).le
  constructor
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_eq_norm, Real.coe_toNNReal _ (by linarith only [hε] : 0 ≤ 1 + ε)] using
      (cylinder_surface_chart_distortion θ hε hε1 x y hx hy).1
  · apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simpa only [Subtype.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK] using
      (cylinder_surface_chart_distortion θ hε hε1 x.val y.val x.property y.property).2

/-- Every actual cylinder chart image has normalized Hausdorff bounds by
its actual n-dimensional Euclidean parameter volume, with sharp local factors. -/
theorem cylinder_surface_chart_euclideanHausdorff_bounds {n : ℕ} (hn : 0 < n)
    (θ : sphere (0 : Domain n) 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    let H := (ℝ ∙ θ.val)ᗮ
    let ψ : H → Domain n := fun u => ‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u)
    let F : WithLp 2 (H × ℝ) → Domain (n + 1) := fun z =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (ψ z.fst, EuclideanSpace.single (0 : Fin 1) z.snd)
    ∀ A : Set (WithLp 2 (H × ℝ)), A ⊆ {z | ‖z.fst‖ ≤ ε} →
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' A) ≤
        (ENNReal.ofReal (1 + ε)) ^ n * (volume : Measure (WithLp 2 (H × ℝ))) A ∧
      (volume : Measure (WithLp 2 (H × ℝ))) A ≤
        (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ n *
          (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' A) := by
  intro H ψ F A hA
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hdimH : finrank ℝ H = n - 1 := by
    have hθ0 : θ.val ≠ 0 := norm_ne_zero_iff.mp (by rw [hθ]; norm_num)
    have h := (ℝ ∙ θ.val).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hθ0, finrank_euclideanSpace_fin] at h
    dsimp only [H]
    omega
  have hdim : finrank ℝ (WithLp 2 (H × ℝ)) = n := by
    rw [(WithLp.linearEquiv 2 ℝ (H × ℝ)).finrank_eq,
      finrank_prod, finrank_self, hdimH]
    omega
  obtain ⟨hLip, hAnti⟩ := cylinder_surface_chart_lipschitz θ hε hε1
  constructor
  · have h := euclideanHausdorff_lipschitzOn_image_le_volume hLip hA
    rw [hdim] at h
    exact h
  · have h := volume_le_euclideanHausdorff_image_of_antilipschitzOn (f := F)
      (patch := {z : WithLp 2 (H × ℝ) | ‖z.fst‖ ≤ ε}) (S := A)
      (K := Real.toNNReal ((1 + ε) / (1 - ε))) hAnti hA
    rw [hdim] at h
    exact h


private theorem sphere_chart_pushforward_local_bounds {n : ℕ} (hn : 0 < n)
    (θ : sphere (0 : Domain n) 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    let H := (ℝ ∙ θ.val)ᗮ
    let φ : H → sphere (0 : Domain n) 1 := fun u =>
      ⟨‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u), by
        exact mem_sphere_zero_iff_norm.mpr
          (sphereSurface_chart_geometry θ.val (mem_sphere_zero_iff_norm.mp θ.property) u).2.1⟩
    let U : Set (sphere (0 : Domain n) 1) :=
      {ω | 0 < inner ℝ θ.val ω.val ∧ ‖(inner ℝ θ.val ω.val)⁻¹ • ω.val - θ.val‖ < ε}
    let κ := Measure.map φ ((volume : Measure H).restrict (ball (0 : H) ε))
    IsOpen U ∧ θ ∈ U ∧ φ '' ball (0 : H) ε = U ∧
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).restrict U ≤
        (ENNReal.ofReal (1 + ε)) ^ (n - 1) • κ ∧
      κ ≤ (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ (n - 1) •
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).restrict U := by
  intro H φ U κ
  have hθ := mem_sphere_zero_iff_norm.mp θ.property
  have hφ : Continuous φ := (sphereSurface_chart_continuous θ.val hθ).subtype_mk _
  obtain ⟨hU, hθU, hcover, hinto⟩ := sphereSurface_chart_neighborhood θ.val hθ ε hε
  have hφT : φ '' ball (0 : H) ε = U := by
    ext ω
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hinto u (mem_ball_zero_iff.mp hu)
    · intro hω
      obtain ⟨u, hu, heq⟩ := hcover ω hω
      exact ⟨u, mem_ball_zero_iff.mpr hu, Subtype.ext heq⟩
  have hdimH : finrank ℝ H = n - 1 := by
    have hθ0 : θ.val ≠ 0 := norm_ne_zero_iff.mp (by rw [hθ]; norm_num)
    have h := (ℝ ∙ θ.val).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hθ0, finrank_euclideanSpace_fin] at h
    dsimp only [H]
    omega
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  have hsets (A : Set (sphere (0 : Domain n) 1)) (hA : MeasurableSet A) :
      σ (A ∩ U) ≤ (ENNReal.ofReal (1 + ε)) ^ (n - 1) * κ A ∧
      κ A ≤ (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ (n - 1) * σ (A ∩ U) := by
    let S : Set H := φ ⁻¹' A ∩ ball 0 ε
    let ψ : H → Domain n := fun u => ‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u)
    have hκ : κ A = (volume : Measure H) S := by
      rw [Measure.map_apply hφ.measurable hA, Measure.restrict_apply (hA.preimage hφ.measurable)]
    have hφS : φ '' S = A ∩ U := by
      ext ω
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu.1, hφT ▸ mem_image_of_mem φ hu.2⟩
      · intro hω
        obtain ⟨u, hu, heq⟩ := (hφT.symm ▸ hω.2)
        exact ⟨u, ⟨by change φ u ∈ A; rw [heq]; exact hω.1, hu⟩, heq⟩
    have hImage : Subtype.val '' (A ∩ U) = ψ '' S := by
      rw [← hφS, image_image]
    have hArea : σ (A ∩ U) =
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)) (ψ '' S) := by
      rw [← hImage, isometry_subtype_coe.euclideanHausdorffMeasure_image]
    have hSb : S ⊆ closedBall (0 : H) ε := fun u hu => ball_subset_closedBall hu.2
    obtain ⟨hLip, hAnti⟩ := sphereSurface_chart_lipschitz θ.val hθ ε hε.le hε1
    constructor
    · have h := euclideanHausdorff_lipschitzOn_image_le_volume hLip hSb
      rw [hdimH, ← hArea, ← hκ] at h
      exact h
    · have h := volume_le_euclideanHausdorff_image_of_antilipschitzOn
        (f := ψ) (patch := closedBall (0 : H) ε) (S := S)
        (K := Real.toNNReal ((1 + ε) / (1 - ε))) hAnti hSb
      rw [hdimH, ← hArea, ← hκ] at h
      exact h
  refine ⟨hU, hθU, hφT, ?_, ?_⟩
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply]
    exact (hsets A hA).1
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA]
    exact (hsets A hA).2


private theorem measurableEmbedding_cylinder_surface (n : ℕ) :
    MeasurableEmbedding (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let c := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Domain n)) τ.symm).trans e.symm
  have h := c.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe (s := sphere (0 : Domain n) 1) isClosed_sphere.measurableSet).prodMap MeasurableEmbedding.id)
  have heq : (fun p : sphere (0 : Domain n) 1 × ℝ =>
      e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)) =
        c ∘ Prod.map Subtype.val id := by
    funext p
    change e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2) =
      e.symm (p.1.val, τ.symm p.2)
    congr 2
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  rw [heq]
  exact h

private theorem cylinder_surface_product_local_bounds {n : ℕ} (hn : 0 < n)
    (θ : sphere (0 : Domain n) 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    let f := fun p : sphere (0 : Domain n) 1 × ℝ =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)
    let μ := (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
      (volume : Measure ℝ)
    let ν := (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).comap f
    ∃ U : Set (sphere (0 : Domain n) 1), IsOpen U ∧ θ ∈ U ∧
      ν.restrict (U ×ˢ univ) ≤
        ((ENNReal.ofReal (1 + ε)) ^ n * (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ (n - 1)) •
          μ.restrict (U ×ˢ univ) ∧
      μ.restrict (U ×ˢ univ) ≤
        ((ENNReal.ofReal (1 + ε)) ^ (n - 1) * (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ n) •
          ν.restrict (U ×ˢ univ) := by
  intro f μ ν
  let H := (ℝ ∙ θ.val)ᗮ
  let P := WithLp 2 (H × ℝ)
  let ψ : H → Domain n := fun u => ‖θ.val + (u : Domain n)‖⁻¹ • (θ.val + u)
  let φ : H → sphere (0 : Domain n) 1 := fun u =>
    ⟨ψ u, mem_sphere_zero_iff_norm.mpr
      (sphereSurface_chart_geometry θ.val (mem_sphere_zero_iff_norm.mp θ.property) u).2.1⟩
  let U : Set (sphere (0 : Domain n) 1) :=
    {ω | 0 < inner ℝ θ.val ω.val ∧ ‖(inner ℝ θ.val ω.val)⁻¹ • ω.val - θ.val‖ < ε}
  let T : Set H := ball 0 ε
  let κ := Measure.map φ ((volume : Measure H).restrict T)
  let W := U ×ˢ (univ : Set ℝ)
  let B : Set P := {z | ‖z.fst‖ < ε}
  let χ : P → sphere (0 : Domain n) 1 × ℝ := fun z => (φ z.fst, z.snd)
  let F : P → Domain (n + 1) := f ∘ χ
  have hφ : Continuous φ := (sphereSurface_chart_continuous θ.val
    (mem_sphere_zero_iff_norm.mp θ.property)).subtype_mk _
  obtain ⟨hU, hθU, hφT, hσUp, hσLo⟩ := sphere_chart_pushforward_local_bounds hn θ hε hε1
  change IsOpen U at hU
  change θ ∈ U at hθU
  change φ '' T = U at hφT
  letI : IsFiniteMeasure (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) := by
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  let j := WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ
  have hχ : Continuous χ := (hφ.comp j.continuous.fst).prodMk j.continuous.snd
  letI : IsFiniteMeasure ((volume : Measure H).restrict T) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure κ := inferInstance
  have hj := (WithLp.volume_preserving_ofLp H ℝ).restrict_preimage
    (s := T ×ˢ (univ : Set ℝ)) (measurableSet_ball.prod MeasurableSet.univ)
  have hpre : (WithLp.ofLp : P → H × ℝ) ⁻¹' (T ×ˢ univ) = B := by
    ext z
    simp only [mem_preimage, mem_prod, mem_univ, and_true, T, B,
      mem_ball, dist_zero_right]
    rfl
  rw [hpre] at hj
  change MeasurePreserving (WithLp.ofLp : P → H × ℝ) ((volume : Measure P).restrict B)
    (((volume : Measure H).prod (volume : Measure ℝ)).restrict (T ×ˢ univ)) at hj
  rw [← Measure.prod_restrict] at hj
  simp only [Measure.restrict_univ] at hj
  have hφMP := hφ.measurable.measurePreserving ((volume : Measure H).restrict T)
  have hχMP : MeasurePreserving χ ((volume : Measure P).restrict B)
      (κ.prod (volume : Measure ℝ)) :=
    (hφMP.prod (MeasurePreserving.id (volume : Measure ℝ))).comp hj
  have hχB : χ '' B = W := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hφT ▸ mem_image_of_mem φ (mem_ball_zero_iff.mpr hz), mem_univ _⟩
    · intro hp
      obtain ⟨u, hu, hup⟩ := (hφT.symm ▸ hp.1)
      refine ⟨WithLp.toLp 2 (u, p.2), ?_, ?_⟩
      · change ‖u‖ < ε
        exact mem_ball_zero_iff.mp hu
      · change (φ u, p.2) = p
        rw [hup]
  have hf := measurableEmbedding_cylinder_surface n
  have hsets (A : Set (sphere (0 : Domain n) 1 × ℝ)) (hA : MeasurableSet A) :
      ν (A ∩ W) ≤ (ENNReal.ofReal (1 + ε)) ^ n * (κ.prod (volume : Measure ℝ)) A ∧
      (κ.prod (volume : Measure ℝ)) A ≤
        (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ n * ν (A ∩ W) := by
    let S : Set P := χ ⁻¹' A ∩ B
    have hκ : (κ.prod (volume : Measure ℝ)) A = (volume : Measure P) S := by
      have h := hχMP.measure_preimage hA.nullMeasurableSet
      rw [Measure.restrict_apply (hA.preimage hχ.measurable)] at h
      exact h.symm
    have hχS : χ '' S = A ∩ W := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz.1, hχB ▸ mem_image_of_mem χ hz.2⟩
      · intro hp
        obtain ⟨z, hz, hzp⟩ := (hχB.symm ▸ hp.2)
        exact ⟨z, ⟨by change χ z ∈ A; rw [hzp]; exact hp.1, hz⟩, hzp⟩
    have hImage : F '' S = f '' (A ∩ W) := by
      rw [← hχS, image_image]
      rfl
    have hν : ν (A ∩ W) =
        (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' S) := by
      rw [hf.comap_apply, ← hImage]
    have hSb : S ⊆ {z : P | ‖z.fst‖ ≤ ε} := by
      intro z hz
      change ‖z.fst‖ ≤ ε
      exact (show ‖z.fst‖ < ε from hz.2).le
    have hbounds := cylinder_surface_chart_euclideanHausdorff_bounds hn θ hε.le hε1 S hSb
    change (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' S) ≤
        (ENNReal.ofReal (1 + ε)) ^ n * (volume : Measure P) S ∧
      (volume : Measure P) S ≤ (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ n *
        (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))) (F '' S) at hbounds
    rw [← hν, ← hκ] at hbounds
    exact hbounds
  have hνUp : ν.restrict W ≤ (ENNReal.ofReal (1 + ε)) ^ n • (κ.prod (volume : Measure ℝ)) := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply]
    exact (hsets A hA).1
  have hνLo : (κ.prod (volume : Measure ℝ)) ≤
      (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ n • ν.restrict W := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA]
    exact (hsets A hA).2
  have hμW : μ.restrict W =
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).restrict U).prod
        (volume : Measure ℝ) := by
    symm
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)))
        (ν := (volume : Measure ℝ)) U univ)
  have hμUp : μ.restrict W ≤ (ENNReal.ofReal (1 + ε)) ^ (n - 1) • (κ.prod (volume : Measure ℝ)) := by
    rw [hμW, ← Measure.prod_smul_left]
    exact Measure.prod_mono hσUp le_rfl
  have hμLo : (κ.prod (volume : Measure ℝ)) ≤
      (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ (n - 1) • μ.restrict W := by
    rw [hμW, ← Measure.prod_smul_left]
    exact Measure.prod_mono hσLo le_rfl
  refine ⟨U, hU, hθU, ?_, ?_⟩
  · have h : (ENNReal.ofReal (1 + ε)) ^ n • (κ.prod (volume : Measure ℝ)) ≤
        (ENNReal.ofReal (1 + ε)) ^ n •
          ((ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ (n - 1) • μ.restrict W) := by
      apply Measure.le_iff'.mpr
      intro A
      simpa only [Measure.smul_apply, smul_eq_mul] using
        mul_le_mul_right (Measure.le_iff'.mp hμLo A) ((ENNReal.ofReal (1 + ε)) ^ n)
    simpa only [smul_smul] using hνUp.trans h
  · have h : (ENNReal.ofReal (1 + ε)) ^ (n - 1) • (κ.prod (volume : Measure ℝ)) ≤
        (ENNReal.ofReal (1 + ε)) ^ (n - 1) •
          ((ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ n • ν.restrict W) := by
      apply Measure.le_iff'.mpr
      intro A
      simpa only [Measure.smul_apply, smul_eq_mul] using
        mul_le_mul_right (Measure.le_iff'.mp hνLo A) ((ENNReal.ofReal (1 + ε)) ^ (n - 1))
    simpa only [smul_smul] using hμUp.trans h


private theorem measure_le_of_sphere_patches {n : ℕ}
    (μ ν : Measure (sphere (0 : Domain n) 1 × ℝ))
    (h : ∀ θ : sphere (0 : Domain n) 1, ∃ U : Set (sphere (0 : Domain n) 1),
      IsOpen U ∧ θ ∈ U ∧ μ.restrict (U ×ˢ univ) ≤ ν.restrict (U ×ˢ univ)) : μ ≤ ν := by
  classical
  choose U hU hθ hle using h
  have hcover : (univ : Set (sphere (0 : Domain n) 1)) ⊆ ⋃ θ, U θ := by
    intro θ _
    exact mem_iUnion.mpr ⟨θ, hθ θ⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let W := fun θ => U θ ×ˢ (univ : Set ℝ)
  have hW : (⋃ θ ∈ t, W θ) = univ := by
    ext p
    constructor
    · exact fun _ => mem_univ p
    · intro _
      obtain ⟨θ, hθt, hpθ⟩ := mem_iUnion₂.mp (ht (mem_univ p.1))
      exact mem_iUnion₂.mpr ⟨θ, hθt, hpθ, mem_univ p.2⟩
  have heq (θ : sphere (0 : Domain n) 1) : (μ ⊓ ν).restrict (W θ) = μ.restrict (W θ) := by
    rw [← sInf_pair, Measure.restrict_sInf_eq_sInf_restrict (by simp)
      ((hU θ).measurableSet.prod MeasurableSet.univ)]
    simpa only [image_pair, sInf_pair] using inf_eq_left.mpr (hle θ)
  have hall : (μ ⊓ ν).restrict (⋃ θ ∈ t, W θ) = μ.restrict (⋃ θ ∈ t, W θ) :=
    Measure.restrict_biUnion_finset_congr.mpr (fun θ _ => heq θ)
  rw [hW, Measure.restrict_univ, Measure.restrict_univ] at hall
  exact inf_eq_left.mp hall

private theorem cylinder_surface_coefficients_small (n : ℕ) (C : ℝ) (hC : 1 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (1 + ε) ^ n * ((1 + ε) / (1 - ε)) ^ (n - 1) < C ∧
      (1 + ε) ^ (n - 1) * ((1 + ε) / (1 - ε)) ^ n < C := by
  have hL : ContinuousAt (fun ε : ℝ => 1 + ε) 0 := (continuous_const.add continuous_id).continuousAt
  have hK : ContinuousAt (fun ε : ℝ => (1 + ε) / (1 - ε)) 0 :=
    hL.div (continuous_const.sub continuous_id).continuousAt (by norm_num)
  have hA := (hL.pow n).mul (hK.pow (n - 1))
  have hB := (hL.pow (n - 1)).mul (hK.pow n)
  have hAev : ∀ᶠ ε in 𝓝 (0 : ℝ), (1 + ε) ^ n * ((1 + ε) / (1 - ε)) ^ (n - 1) < C :=
    hA (isOpen_Iio.mem_nhds (by simpa only [mem_Iio, Pi.mul_apply, Pi.pow_apply, add_zero, sub_zero, div_one, one_pow, one_mul] using hC))
  have hBev : ∀ᶠ ε in 𝓝 (0 : ℝ), (1 + ε) ^ (n - 1) * ((1 + ε) / (1 - ε)) ^ n < C :=
    hB (isOpen_Iio.mem_nhds (by simpa only [mem_Iio, Pi.mul_apply, Pi.pow_apply, add_zero, sub_zero, div_one, one_pow, one_mul] using hC))
  have hOne : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 ∧
      (1 + ε) ^ n * ((1 + ε) / (1 - ε)) ^ (n - 1) < C ∧
      (1 + ε) ^ (n - 1) * ((1 + ε) / (1 - ε)) ^ n < C := by
    filter_upwards [self_mem_nhdsWithin, hOne.filter_mono nhdsWithin_le_nhds,
      hAev.filter_mono nhdsWithin_le_nhds, hBev.filter_mono nhdsWithin_le_nhds] with ε hε h1 h2 h3
    exact ⟨hε, h1, h2, h3⟩
  exact hev.exists

/-- The actual embedded unit-cylinder surface measure is exactly the product
of native unit-sphere surface measure and real-time Lebesgue measure. -/
theorem map_cylinder_surface_product_eq_native {n : ℕ} (hn : 0 < n) :
    Measure.map (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume : Measure ℝ)) =
    (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
        sphere (0 : Domain n) 1} := by
  let f := fun p : sphere (0 : Domain n) 1 × ℝ =>
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
      (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)
  let μ := (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
    (volume : Measure ℝ)
  let ν := (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).comap f
  have hglobal (C : ℝ) (hC : 1 < C) : ν ≤ ENNReal.ofReal C • μ ∧ μ ≤ ENNReal.ofReal C • ν := by
    obtain ⟨ε, hε, hε1, hA, hB⟩ := cylinder_surface_coefficients_small n C hC
    have hL : 0 ≤ 1 + ε := by linarith only [hε]
    have hK : 0 ≤ (1 + ε) / (1 - ε) := div_nonneg hL (sub_pos.mpr hε1).le
    have hcoeffA : (ENNReal.ofReal (1 + ε)) ^ n *
        (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ (n - 1) ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_pow hK,
        ← ENNReal.ofReal_mul (pow_nonneg hL n)]
      exact ENNReal.ofReal_le_ofReal hA.le
    have hcoeffB : (ENNReal.ofReal (1 + ε)) ^ (n - 1) *
        (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ n ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_pow hK,
        ← ENNReal.ofReal_mul (pow_nonneg hL (n - 1))]
      exact ENNReal.ofReal_le_ofReal hB.le
    constructor
    · apply measure_le_of_sphere_patches
      intro θ
      obtain ⟨U, hU, hθU, hν, _⟩ := cylinder_surface_product_local_bounds hn θ hε hε1
      refine ⟨U, hU, hθU, hν.trans ?_⟩
      apply Measure.le_iff'.mpr
      intro A
      simp only [Measure.smul_apply, Measure.restrict_smul, smul_eq_mul]
      exact mul_le_mul_left hcoeffA _
    · apply measure_le_of_sphere_patches
      intro θ
      obtain ⟨U, hU, hθU, _, hμ⟩ := cylinder_surface_product_local_bounds hn θ hε hε1
      refine ⟨U, hU, hθU, hμ.trans ?_⟩
      apply Measure.le_iff'.mpr
      intro A
      simp only [Measure.smul_apply, Measure.restrict_smul, smul_eq_mul]
      exact mul_le_mul_left hcoeffB _
  have hbound (ρ σ : Measure (sphere (0 : Domain n) 1 × ℝ))
      (hρ : ∀ C : ℝ, 1 < C → ρ ≤ ENNReal.ofReal C • σ) : ρ ≤ σ := by
    apply Measure.le_iff'.mpr
    intro A
    have hlim : Filter.Tendsto (fun C : ℝ => ENNReal.ofReal C) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hprod := ENNReal.Tendsto.mul_const hlim (b := σ A) (Or.inl one_ne_zero)
    rw [one_mul] at hprod
    apply ge_of_tendsto hprod
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards with C hC
    exact Measure.le_iff'.mp (hρ C hC) A
  have hEq : ν = μ := le_antisymm (hbound ν μ (fun C hC => (hglobal C hC).1))
    (hbound μ ν (fun C hC => (hglobal C hC).2))
  have hf := measurableEmbedding_cylinder_surface n
  have hRange : range f = {y : Domain (n + 1) |
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ sphere (0 : Domain n) 1} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      change ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))).1 ∈ sphere (0 : Domain n) 1
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact p.1.property
    · intro hy
      exact ⟨(⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1, hy⟩,
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0),
          cylinder_coordinates_inverse_left n y⟩
  change Measure.map f μ = _
  rw [← hEq]
  have h := hf.map_comap (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1)))
  rw [hRange] at h
  exact h


/-- Restricting the exact cylinder surface-product correspondence to a closed
time interval gives the source's actual closed unit-cylinder measure. -/
theorem map_cylinder_surface_product_Icc_eq_native_unitCylinder {n : ℕ} (hn : 0 < n)
    (a b : ℝ) :
    Measure.map (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.restrict (Icc a b))) =
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict
        (unitCylinder n a b) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let f := fun p : sphere (0 : Domain n) 1 × ℝ => e.symm
    (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)
  let μ := (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
    (volume : Measure ℝ)
  letI : IsFiniteMeasure (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) := by
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hpre : f ⁻¹' unitCylinder n a b = (univ : Set (sphere (0 : Domain n) 1)) ×ˢ Icc a b := by
    ext p
    change (e (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))).1 ∈ sphere (0 : Domain n) 1 ∧
      (e (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))).2 0 ∈ Icc a b ↔
        p ∈ (univ : Set (sphere (0 : Domain n) 1)) ×ˢ Icc a b
    rw [e.apply_symm_apply]
    simp
  have h := (measurableEmbedding_cylinder_surface n).restrict_map μ (unitCylinder n a b)
  change (Measure.map f μ).restrict (unitCylinder n a b) =
    Measure.map f (μ.restrict (f ⁻¹' unitCylinder n a b)) at h
  rw [hpre] at h
  change (Measure.map f μ).restrict (unitCylinder n a b) =
    Measure.map f (((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume : Measure ℝ)).restrict (univ ×ˢ Icc a b)) at h
  rw [← Measure.prod_restrict] at h
  simp only [Measure.restrict_univ] at h
  have hglobal : Measure.map f μ =
      (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict
        {y | (e y).1 ∈ sphere (0 : Domain n) 1} := map_cylinder_surface_product_eq_native hn
  have hsub : unitCylinder n a b ⊆ {y : Domain (n + 1) | (e y).1 ∈ sphere (0 : Domain n) 1} :=
    fun y hy => hy.1
  rw [hglobal, Measure.restrict_restrict_of_subset hsub] at h
  exact h.symm

end StratificationTheory
