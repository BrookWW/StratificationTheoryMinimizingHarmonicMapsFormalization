module

public import StratificationTheory.Foundation.NativeCylinderRadialL2Transfer
public import StratificationTheory.Foundation.CylinderRadialDifferential
public import StratificationTheory.Foundation.SmoothDomainSobolevPullback
public import HarmonicMaps.Analysis.SobolevL2Closure
public import HarmonicMaps.Analysis.SobolevAECongruence

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff BigOperators
namespace StratificationTheory

private theorem native_radial_source_coordinates {n : ℕ} (r : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    ContDiffOn ℝ ∞ F {y : Domain (n + 1) | (e y).1 ≠ 0} := by
  intro e F
  let A := fun z : Domain (n + 1) => e.symm (r • (e z).1, (e z).2)
  have hR : ContDiff ℝ ∞ (fun _ : Domain (n + 1) => r) := contDiff_const
  have hA : ContDiff ℝ ∞ A :=
    e.symm.contDiff.comp ((hR.smul (contDiff_fst.comp e.contDiff)).prodMk
      (contDiff_snd.comp e.contDiff))
  have hN := contDiffOn_cylinder_spatial_normalization (n := n)
  simpa only [A, F, e, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using
    hA.comp_contDiffOn hN

private theorem native_radial_source_ray {n : ℕ} {a b : ℝ}
    (r : ℝ) (ρ : Ioi (0 : ℝ)) (c : unitCylinder n a b) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    F (e.symm (ρ.val • (e c.val).1, (e c.val).2)) =
      e.symm (r • (e c.val).1, (e c.val).2) := by
  intro e F
  have hθ : ‖(e c.val).1‖ = 1 := mem_sphere_zero_iff_norm.mp c.property.1
  have hNorm : ‖ρ.val • (e c.val).1‖ = ρ.val := by
    rw [norm_smul, Real.norm_of_nonneg (show (0 : ℝ) ≤ ρ.val from ρ.property.le), hθ, mul_one]
  simp only [F, e.apply_symm_apply, hNorm, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ (show (0 : ℝ) < ρ.val from ρ.property).ne', mul_one]

private theorem smooth_native_chain_columns {d q : ℕ}
    (U : OpenDomain d) (F : Domain d → Domain d) (hF : ContDiffOn ℝ ∞ F U.val)
    {f : Domain d → Ambient q} (hf : ContDiff ℝ ∞ f) :
    HasWeakGradient U (f ∘ F) (fun y i => ∑ j : Fin d,
      (fderiv ℝ F y (EuclideanSpace.single i 1)) j • coordinateDerivative f hf j (F y)) := by
  have hWeak := hasWeakGradient_of_contDiffOn U (hf.comp_contDiffOn hF)
  refine HasWeakGradient.congr_ae hWeak EventuallyEq.rfl ?_
  filter_upwards [ae_restrict_mem U.property.measurableSet] with y hy
  funext i
  have hFd := (hF.differentiableOn (by simp)).differentiableAt (U.property.mem_nhds hy)
  rw [((hf.differentiable (by simp) (F y)).hasFDerivAt.comp y hFd.hasFDerivAt).fderiv]
  have hv : ∑ j : Fin d, (fderiv ℝ F y (EuclideanSpace.single i 1)) j •
      EuclideanSpace.single j 1 = fderiv ℝ F y (EuclideanSpace.single i 1) := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr
        (fderiv ℝ F y (EuclideanSpace.single i 1))
  simp only [ContinuousLinearMap.comp_apply]
  calc
    _ = fderiv ℝ f (F y) (∑ j : Fin d,
        (fderiv ℝ F y (EuclideanSpace.single i 1)) j • EuclideanSpace.single j 1) :=
      congrArg (fderiv ℝ f (F y)) hv.symm
    _ = _ := by simp only [map_sum, map_smul, coordinateDerivative]

private theorem native_radial_coefficient_memLp_top {n : ℕ} {a b : ℝ}
    (r : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (1 / 2 < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo a b},
        (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    ∀ i j : Fin (n + 1), MemLp (fun y => (fderiv ℝ F y (EuclideanSpace.single i 1)) j)
      ∞ (volume.restrict Ω.val) := by
  intro e F Ω i j
  let Kspace : Set (Domain n) := closedBall 0 2 \ ball 0 (1 / 2)
  let Ktime : Set (Domain 1) := (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) '' Icc a b
  let K : Set (Domain (n + 1)) := e ⁻¹' (Kspace ×ˢ Ktime)
  have hSingle : Continuous (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    convert continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) using 1
    funext t
    ext i
    simp
  have hKt : IsCompact Ktime := isCompact_Icc.image hSingle
  have hK : IsCompact K := e.toHomeomorph.isCompact_preimage.mpr
    (((isCompact_closedBall 0 2).diff isOpen_ball).prod hKt)
  have hUK : Ω.val ⊆ K := by
    intro y hy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right] using hy.1.2.le
    · simpa only [mem_ball, dist_zero_right, not_lt] using hy.1.1.le
    · refine ⟨(e y).2 0, Ioo_subset_Icc_self hy.2, ?_⟩
      ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp
  have hK0 : K ⊆ {y : Domain (n + 1) | (e y).1 ≠ 0} := by
    intro y hy hzero
    exact hy.1.2 (by rw [hzero]; exact mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hOpen : IsOpen {y : Domain (n + 1) | (e y).1 ≠ 0} :=
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set (Domain n))).preimage (continuous_fst.comp e.continuous)
  have hF := (native_radial_source_coordinates (n := n) r)
  have hCont : ContinuousOn (fun y => (fderiv ℝ F y (EuclideanSpace.single i 1)) j)
      {y : Domain (n + 1) | (e y).1 ≠ 0} :=
    (EuclideanSpace.proj j).continuous.continuousOn.comp
      ((hF.continuousOn_fderiv_of_isOpen hOpen (by simp)).clm_apply continuousOn_const)
      (mapsTo_univ _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hCont.mono hK0)
  apply memLp_top_of_bound ((hCont.mono (hUK.trans hK0)).aestronglyMeasurable Ω.property.measurableSet) C
  filter_upwards [ae_restrict_mem Ω.property.measurableSet] with y hy
  exact hC y (hUK hy)

private theorem native_radial_collar_volume_finite (n : ℕ) (a b : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (1 / 2 < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo a b},
        (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    (volume : Measure (Domain (n + 1))) Ω.val ≠ ⊤ := by
  intro e Ω
  let Kspace : Set (Domain n) := closedBall 0 2 \ ball 0 (1 / 2)
  let Ktime : Set (Domain 1) := (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) '' Icc a b
  let K : Set (Domain (n + 1)) := e ⁻¹' (Kspace ×ˢ Ktime)
  have hSingle : Continuous (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    convert continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) using 1
    funext t
    ext i
    simp
  have hKt : IsCompact Ktime := isCompact_Icc.image hSingle
  have hK : IsCompact K := e.toHomeomorph.isCompact_preimage.mpr
    (((isCompact_closedBall 0 2).diff isOpen_ball).prod hKt)
  have hUK : Ω.val ⊆ K := by
    intro y hy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right] using hy.1.2.le
    · simpa only [mem_ball, dist_zero_right, not_lt] using hy.1.1.le
    · refine ⟨(e y).2 0, Ioo_subset_Icc_self hy.2, ?_⟩
      ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp
  exact ne_top_of_le_ne_top hK.measure_ne_top (measure_mono hUK)

private theorem memW12_native_chain_graph_limit {d q : ℕ}
    (U : OpenDomain d) [IsFiniteMeasure (volume.restrict U.val)]
    (F : Domain d → Domain d) (hF : ContDiffOn ℝ ∞ F U.val)
    (W : Domain d → Ambient q) (DW : Domain d → Gradient d q)
    (f : ℕ → Domain d → Ambient q) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hCoeff : ∀ i j : Fin d, MemLp (fun y => (fderiv ℝ F y (EuclideanSpace.single i 1)) j)
      ∞ (volume.restrict U.val))
    (hfMapLp : ∀ k, MemLp (f k ∘ F) 2 (volume.restrict U.val))
    (hMapLp : MemLp (W ∘ F) 2 (volume.restrict U.val))
    (hfColLp : ∀ k i, MemLp (fun y => coordinateDerivative (f k) (hf k) i (F y)) 2 (volume.restrict U.val))
    (hColLp : ∀ i, MemLp (fun y => DW (F y) i) 2 (volume.restrict U.val))
    (hMapConv : Tendsto (fun k => eLpNorm (f k ∘ F - W ∘ F) 2 (volume.restrict U.val)) atTop (𝓝 0))
    (hColConv : ∀ i, Tendsto (fun k => eLpNorm
      (fun y => coordinateDerivative (f k) (hf k) i (F y) - DW (F y) i) 2
        (volume.restrict U.val)) atTop (𝓝 0)) :
    MemW12 U (W ∘ F) (fun y i => ∑ j : Fin d,
      (fderiv ℝ F y (EuclideanSpace.single i 1)) j • DW (F y) j) := by
  let coeff := fun (i j : Fin d) y => (fderiv ℝ F y (EuclideanSpace.single i 1)) j
  have hColumns (D : Domain d → Gradient d q)
      (hD : ∀ i, MemLp (fun y => D y i) 2 (volume.restrict U.val)) (i : Fin d) :
      MemLp (fun y => ∑ j, coeff i j y • D y j) 2 (volume.restrict U.val) := by
    simpa only [Finset.sum_apply, Pi.smul_apply'] using
      memLp_finsetSum Finset.univ (fun j _ => (hD j).smul (r := (2 : ℝ≥0∞)) (hCoeff i j))
  let Df := fun k y i => ∑ j : Fin d, coeff i j y • coordinateDerivative (f k) (hf k) j (F y)
  have hSmooth (k : ℕ) : MemW12 U (f k ∘ F) (Df k) :=
    ⟨smooth_native_chain_columns U F hF (hf k), hfMapLp k,
      hColumns (fun y j => coordinateDerivative (f k) (hf k) j (F y)) (hfColLp k)⟩
  apply MemW12.of_L2_limit hSmooth hMapLp (hColumns (fun y j => DW (F y) j) hColLp) hMapConv
  intro i
  have hEach (j : Fin d) := tendsto_eLpNorm_two_bounded_smul_zero (hCoeff i j)
    (fun k => ((hfColLp k j).sub (hColLp j)).aestronglyMeasurable) (hColConv j)
  have hSum := tendsto_eLpNorm_two_finite_sum_zero
    (fun j k => (((hfColLp k j).sub (hColLp j)).smul (r := (2 : ℝ≥0∞)) (hCoeff i j)).aestronglyMeasurable)
    hEach
  simpa only [Df, smul_sub, Finset.sum_sub_distrib, Pi.smul_apply', Pi.sub_apply,
    Finset.sum_apply, Function.comp_def] using hSum

/-- A genuine smooth graph limit on one native spatial cylinder produces
its actual finite radial weak extension and cylinder Sobolev membership. -/
theorem memCylinderW12_of_native_spatial_smooth_graph_limit {n q : ℕ}
    (hn : 2 ≤ n) {a b : ℝ} (hab : a < b) (r : ℝ)
    (W : Domain (n + 1) → Ambient q) (DW : Domain (n + 1) → Gradient (n + 1) q)
    (f : ℕ → Domain (n + 1) → Ambient q) (hf : ∀ k, ContDiff ℝ ∞ (f k)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    let X := fun c : unitCylinder n a b => e.symm (r • (e c.val).1, (e c.val).2)
    let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (1 / 2 < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo a b},
        (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    (∀ k, MemLp (fun c => f k (X c)) 2 μ) →
    MemLp (fun c => W (X c)) 2 μ →
    (∀ i : Fin (n + 1), (∀ k, MemLp (fun c => coordinateDerivative (f k) (hf k) i (X c)) 2 μ) ∧
      MemLp (fun c => DW (X c) i) 2 μ) →
    Tendsto (fun k => eLpNorm (fun c => f k (X c) - W (X c)) 2 μ) atTop (𝓝 0) →
    (∀ i : Fin (n + 1), Tendsto (fun k => eLpNorm
      (fun c => coordinateDerivative (f k) (hf k) i (X c) - DW (X c) i) 2 μ) atTop (𝓝 0)) →
    MemCylinderW12 hn hab (fun c => W (X c)) ∧
      MemW12 Ω (W ∘ F) (fun y i => ∑ j : Fin (n + 1),
        (fderiv ℝ F y (EuclideanSpace.single i 1)) j • DW (F y) j) := by
  intro e μ X F Ω hfLp hWLp hDWLp hfConv hDfConv
  have hnpos : 0 < n := by omega
  have hHalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hBand : (1 / 2 : ℝ) < 2 := by norm_num
  have hRay (ρ : Ioi (0 : ℝ)) (c : unitCylinder n a b) :
      F (e.symm (ρ.val • (e c.val).1, (e c.val).2)) = X c :=
    native_radial_source_ray r ρ c
  have hMapLp : MemLp (W ∘ F) 2 (volume.restrict Ω.val) :=
    (memLp_two_native_cylinder_radial_extension hnpos hHalf hBand (fun c => W (X c)) hWLp
      (W ∘ F) (fun ρ c => congrArg W (hRay ρ c))).1
  have hColLp (i : Fin (n + 1)) : MemLp (fun y => DW (F y) i) 2 (volume.restrict Ω.val) :=
    (memLp_two_native_cylinder_radial_extension hnpos hHalf hBand (fun c => DW (X c) i) (hDWLp i).2
      (fun y => DW (F y) i) (fun ρ c => congrArg (fun y => DW y i) (hRay ρ c))).1
  have hfMapLp (k : ℕ) : MemLp (f k ∘ F) 2 (volume.restrict Ω.val) :=
    (memLp_two_native_cylinder_radial_extension hnpos hHalf hBand (fun c => f k (X c)) (hfLp k)
      (f k ∘ F) (fun ρ c => congrArg (f k) (hRay ρ c))).1
  have hfColLp (k : ℕ) (i : Fin (n + 1)) : MemLp
      (fun y => coordinateDerivative (f k) (hf k) i (F y)) 2 (volume.restrict Ω.val) :=
    (memLp_two_native_cylinder_radial_extension hnpos hHalf hBand
      (fun c => coordinateDerivative (f k) (hf k) i (X c)) ((hDWLp i).1 k)
      (fun y => coordinateDerivative (f k) (hf k) i (F y))
      (fun ρ c => congrArg (coordinateDerivative (f k) (hf k) i) (hRay ρ c))).1
  let coeff := fun (i j : Fin (n + 1)) y => (fderiv ℝ F y (EuclideanSpace.single i 1)) j
  have hCoeff (i j : Fin (n + 1)) : MemLp (coeff i j) ∞ (volume.restrict Ω.val) :=
    native_radial_coefficient_memLp_top r i j
  have hMapConv : Tendsto (fun k => eLpNorm (f k ∘ F - W ∘ F) 2 (volume.restrict Ω.val))
      atTop (𝓝 0) :=
    tendsto_eLpNorm_two_native_cylinder_radial_extension_sub hnpos hHalf hBand
      (fun k c => f k (X c)) (fun c => W (X c)) hfLp hWLp hfConv
      (fun k => f k ∘ F) (W ∘ F) (fun k ρ c => congrArg (f k) (hRay ρ c))
      (fun ρ c => congrArg W (hRay ρ c))
  have hColConv (i : Fin (n + 1)) : Tendsto (fun k => eLpNorm
      (fun y => coordinateDerivative (f k) (hf k) i (F y) - DW (F y) i) 2
        (volume.restrict Ω.val)) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_native_cylinder_radial_extension_sub hnpos hHalf hBand
      (fun k c => coordinateDerivative (f k) (hf k) i (X c)) (fun c => DW (X c) i)
      (hDWLp i).1 (hDWLp i).2 (hDfConv i)
      (fun k y => coordinateDerivative (f k) (hf k) i (F y)) (fun y => DW (F y) i)
      (fun k ρ c => congrArg (coordinateDerivative (f k) (hf k) i) (hRay ρ c))
      (fun ρ c => congrArg (fun y => DW y i) (hRay ρ c))
  letI : IsFiniteMeasure (volume.restrict Ω.val) :=
    isFiniteMeasure_restrict.mpr (native_radial_collar_volume_finite n a b)
  have hFSmooth : ContDiffOn ℝ ∞ F Ω.val :=
    (native_radial_source_coordinates (n := n) r).mono (fun y hy =>
      norm_pos_iff.mp (hHalf.trans hy.1.1))
  have hFull : MemW12 Ω (W ∘ F) (fun y i => ∑ j, coeff i j y • DW (F y) j) :=
    memW12_native_chain_graph_limit Ω F hFSmooth W DW f hf hCoeff
      hfMapLp hMapLp hfColLp hColLp hMapConv hColConv
  refine ⟨?_, hFull⟩
  let U : OpenDomain n := ⟨{x | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2}, isOpen_Ioo.preimage continuous_norm⟩
  refine ⟨hWLp, U, ?_, ?_, W ∘ F, _, hFull, ?_⟩
  · intro x hx
    have hNorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    change 1 / 2 < ‖x‖ ∧ ‖x‖ < 2
    rw [hNorm]
    norm_num
  · intro hx
    change 1 / 2 < ‖(0 : Domain n)‖ ∧ _ at hx
    norm_num at hx
  · intro ρ c _ht _hρ
    exact congrArg W (hRay ⟨ρ.val, ρ.property⟩ c)

end StratificationTheory
