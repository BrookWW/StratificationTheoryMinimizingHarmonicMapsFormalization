module

public import StratificationTheory.Foundation.CylinderL2Slices
public import StratificationTheory.Foundation.CylinderSurfaceMeasure
public import HarmonicMaps.Analysis.VariableMollificationL2
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul

public section
open HarmonicMaps MeasureTheory Metric Set Filter MeasurableSpace
open scoped Topology ENNReal

namespace StratificationTheory

private theorem measurable_of_all_dist {α β : Type*} [MeasurableSpace α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    {F : α → β} (hF : ∀ c : β, Measurable (fun t => dist (F t) c)) : Measurable F := by
  classical
  apply measurable_of_isOpen
  intro U hU
  have hr (x : U) : ∃ r : ℝ, 0 < r ∧ ball x.val r ⊆ U :=
    isOpen_iff.mp hU x.val x.property
  choose r hr hsub using hr
  have hcover : (⋃ x : U, ball x.val (r x)) = U := by
    apply Subset.antisymm (iUnion_subset fun x => hsub x)
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨T, hT, hUnion⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball x.val (r x)) (fun _ => isOpen_ball)
  rw [← hcover, ← hUnion]
  simp only [preimage_iUnion]
  exact MeasurableSet.biUnion hT (fun x _ => measurableSet_lt (hF x.val) measurable_const)

private theorem stronglyMeasurable_curried_lp_two {n q : ℕ} (hn : 0 < n)
    {g : sphere (0 : Domain n) 1 × ℝ → Ambient q} (hg : StronglyMeasurable g) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃ F : ℝ → Lp (Ambient q) 2 σ, StronglyMeasurable F ∧
      ∀ t (ht : MemLp (fun θ => g (θ, t)) 2 σ), F t = ht.toLp (fun θ => g (θ, t)) := by
  classical
  intro σ
  let F : ℝ → Lp (Ambient q) 2 σ := fun t =>
    if ht : MemLp (fun θ => g (θ, t)) 2 σ then ht.toLp (fun θ => g (θ, t)) else 0
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp (Ambient q) 2 σ) := borel (Lp (Ambient q) 2 σ)
  letI : BorelSpace (Lp (Ambient q) 2 σ) := ⟨rfl⟩
  have hcur : StronglyMeasurable (Function.uncurry (fun t θ => g (θ, t))) :=
    hg.comp_measurable measurable_swap
  have hgood : MeasurableSet {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ} := by
    have hsq : StronglyMeasurable (Function.uncurry (fun t θ => ‖g (θ, t)‖ ^ 2)) :=
      hcur.norm.pow 2
    have hi := measurableSet_integrable (μ := σ) hsq
    convert hi using 1
    ext t
    exact memLp_two_iff_integrable_sq_norm (hcur.of_uncurry_left.aestronglyMeasurable)
  refine ⟨F, ?_, ?_⟩
  ·
    apply Measurable.stronglyMeasurable
    apply measurable_of_all_dist
    intro c
    have hdiff : StronglyMeasurable (Function.uncurry (fun t θ => ‖g (θ, t) - c θ‖ ^ 2)) := by
      exact (hcur.sub (Lp.stronglyMeasurable c |>.comp_measurable measurable_snd)).norm.pow 2
    have hInt : StronglyMeasurable (fun t : ℝ => ∫ θ, ‖g (θ, t) - c θ‖ ^ 2 ∂σ) :=
      hdiff.integral_prod_right
    have hEq : (fun t : ℝ => dist (F t) c) =
        {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ}.piecewise
          (fun t => Real.sqrt (∫ θ, ‖g (θ, t) - c θ‖ ^ 2 ∂σ)) (fun _ => dist 0 c) := by
      funext t
      by_cases ht : MemLp (fun θ => g (θ, t)) 2 σ
      · rw [Set.piecewise_eq_of_mem {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ} _ _ ht]
        simp only [F, dif_pos ht]
        have hc : (Lp.memLp c).toLp (fun θ => c θ) = c := Lp.toLp_coeFn c (Lp.memLp c)
        have hnorm : ‖ht.toLp (fun θ => g (θ, t)) - c‖ ^ 2 =
            ∫ θ, ‖g (θ, t) - c θ‖ ^ 2 ∂σ := by
          rw [← hc, ← ht.toLp_sub (Lp.memLp c), Lp.norm_toLp,
            ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (ht.sub (Lp.memLp c))]
          simp only [hc, Pi.sub_apply]
        rw [dist_eq_norm, ← hnorm, Real.sqrt_sq (norm_nonneg _)]
      · rw [Set.piecewise_eq_of_notMem {t : ℝ | MemLp (fun θ => g (θ, t)) 2 σ} _ _ ht]
        simp only [F, dif_neg ht]
    rw [hEq]
    exact Measurable.piecewise hgood (Real.continuous_sqrt.measurable.comp hInt.measurable) measurable_const
  · intro t ht
    simp only [F, dif_pos ht]


/-- Actual native angular-time L2 data provide a strongly measurable
L2-valued time curve representing their actual slices, with the exact energy. -/
theorem exists_native_lp_two_time_curve {n q : ℕ} (hn : 0 < n) (a b : ℝ)
    {f : sphere (0 : Domain n) 1 × ℝ → Ambient q}
    (hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b)))) :
    ∃ F : ℝ → Lp (Ambient q) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)),
      MemLp F 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => f (θ, t)) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1)), F t = ht.toLp (fun θ => f (θ, t))) ∧
      (∫ t in Icc a b, ‖F t‖ ^ 2) =
        ∫ p : sphere (0 : Domain n) 1 × ℝ, ‖f p‖ ^ 2
          ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
            (volume.restrict (Icc a b))) := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let μ := σ.prod ν
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  let g : sphere (0 : Domain n) 1 × ℝ → Ambient q := hf.aestronglyMeasurable.mk f
  have hgS : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 μ := hf.ae_eq hfg
  obtain ⟨F, hFS, hFslice⟩ := stronglyMeasurable_curried_lp_two hn hgS
  have hgSlice : ∀ᵐ t ∂ν, MemLp (fun θ => g (θ, t)) 2 σ := by
    have hsq := hg.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    filter_upwards [hg.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with t hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).mpr hi
  have hfgSlice : ∀ᵐ t ∂ν, (fun θ => f (θ, t)) =ᵐ[σ] (fun θ => g (θ, t)) := by
    have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hfg
    exact Measure.ae_ae_of_ae_prod hswap
  have hFslices : ∀ᵐ t ∂ν, ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ,
      F t = ht.toLp (fun θ => f (θ, t)) := by
    filter_upwards [hgSlice, hfgSlice] with t hgt hft
    have ht := hgt.ae_eq hft.symm
    exact ⟨ht, (hFslice t hgt).trans (hgt.toLp_congr ht hft.symm)⟩
  have hnorm : ∀ᵐ t ∂ν, ‖F t‖ ^ 2 = ∫ θ, ‖f (θ, t)‖ ^ 2 ∂σ := by
    filter_upwards [hFslices] with t ht
    obtain ⟨hft, hFt⟩ := ht
    rw [hFt, Lp.norm_toLp, ← integral_norm_sq_eq_eLpNorm_two_toReal_sq hft]
  have hsq : Integrable (fun p => ‖f p‖ ^ 2) μ :=
    hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hFInt : Integrable (fun t => ‖F t‖ ^ 2) ν :=
    hsq.integral_prod_right.congr (Filter.EventuallyEq.symm hnorm)
  have hFL : MemLp F 2 ν := (memLp_two_iff_integrable_sq_norm hFS.aestronglyMeasurable).mpr hFInt
  exact ⟨F, hFL, hFslices, (integral_congr_ae hnorm).trans (integral_prod_symm _ hsq).symm⟩


/-- Actual native cylinder L2 data have an L2-valued time curve representing
all actual interior slices almost everywhere, with the native physical energy. -/
theorem exists_lp_two_time_curve_of_native_cylinder {n q : ℕ} (hn : 0 < n) (a b : ℝ)
    (v : unitCylinder n a b → Ambient q)
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun p =>
      ⟨e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val), by
        change (e (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val))).1 ∈ sphere (0 : Domain n) 1 ∧
          (e (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val))).2 0 ∈ Icc a b
        rw [e.apply_symm_apply]
        exact ⟨p.1.property, by simp⟩⟩
    ∃ F : ℝ → Lp (Ambient q) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)),
      MemLp F 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b), ∀ ht : t ∈ Icc a b,
        ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht⟩))) 2
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
            F t = hslice.toLp (fun θ => v (c (θ, ⟨t, ht⟩)))) ∧
      (∫ t in Icc a b, ‖F t‖ ^ 2) =
        ∫ y : unitCylinder n a b, ‖v y‖ ^ 2 ∂Measure.euclideanHausdorffMeasure n := by
  classical
  intro e c
  let C := unitCylinder n a b
  let u : Domain (n + 1) → Ambient q := fun y => if hy : y ∈ C then v ⟨y, hy⟩ else 0
  let f := fun p : sphere (0 : Domain n) 1 × ℝ => e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2)
  let σC : Measure C := Measure.euclideanHausdorffMeasure n
  let μC := (Measure.euclideanHausdorffMeasure n : Measure (Domain (n + 1))).restrict C
  have hC : MeasurableSet C := (isClosed_native_cylinder_surface_Icc n a b).measurableSet
  have hEmb := MeasurableEmbedding.subtype_coe hC
  have hmap : Measure.map (Subtype.val : C → Domain (n + 1)) σC = μC := by
    simpa only [Subtype.range_coe] using
      (Isometry.map_euclideanHausdorffMeasure (d := n)
        (isometry_subtype_coe : Isometry (Subtype.val : C → Domain (n + 1)) ))
  have huC : (fun y : C => u y.val) = v := by
    funext y
    simp only [u, dif_pos y.property]
    congr 1
  have hu : MemLp u 2 μC := by
    rw [← hmap]
    apply hEmb.memLp_map_measure_iff.mpr
    change MemLp (fun y : C => u y.val) 2 σC
    rw [huC]
    exact hv
  have hp := memLp_two_cylinder_surface_pullback hn hu
  obtain ⟨F, hFL, hFslices, henergy⟩ := exists_native_lp_two_time_curve hn a b hp
  have hinside (t : ℝ) (ht : t ∈ Icc a b) :
      (fun θ : sphere (0 : Domain n) 1 => u (f (θ, t))) =
        (fun θ => v (c (θ, ⟨t, ht⟩))) := by
    funext θ
    have hpoint : f (θ, t) ∈ C := (c (θ, ⟨t, ht⟩)).property
    simp only [u, dif_pos hpoint]
    congr 1
  refine ⟨F, hFL, ?_, ?_⟩
  · filter_upwards [hFslices] with t hs
    intro ht
    obtain ⟨hLt, hFt⟩ := hs
    have heq := hinside t ht
    have hL : MemLp (fun θ => v (c (θ, ⟨t, ht⟩))) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) := by
      rwa [← heq]
    refine ⟨hL, hFt.trans ?_⟩
    exact hLt.toLp_congr hL (Filter.Eventually.of_forall fun θ => congrFun heq θ)
  · let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    letI : IsFiniteMeasure σ := by
      dsimp only [σ]
      rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
      infer_instance
    have hsq := hp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    have hdis := (integrable_cylinder_slice_energy_and_integral hn hu).2
    have hphys : (∫ y, ‖u y‖ ^ 2 ∂μC) = ∫ y : C, ‖v y‖ ^ 2 ∂σC := by
      have hm : MeasurePreserving (Subtype.val : C → Domain (n + 1)) σC μC :=
        ⟨measurable_subtype_coe, hmap⟩
      rw [← hm.integral_comp hEmb (fun y => ‖u y‖ ^ 2)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
        congrArg (fun z : Ambient q => ‖z‖ ^ 2) (congrFun huC y))
    exact henergy.trans ((integral_prod_symm _ hsq).trans hdis |>.trans hphys)


/-- Actual probability averages of finite product L2 data remain in L2,
with the square-energy bound needed for radial averaging of time columns. -/
theorem memLp_two_probability_average {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {f : α × β → Ambient q} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ ∧
      (∫ x, ‖∫ y, f (x, y) ∂ν‖ ^ 2 ∂μ) ≤ ∫ p, ‖f p‖ ^ 2 ∂μ.prod ν := by
  have hi : Integrable f (μ.prod ν) := hf.integrable (by norm_num)
  have hs : Integrable (fun p => ‖f p‖ ^ 2) (μ.prod ν) :=
    hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hm : AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ :=
    hi.integral_prod_left.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ‖∫ y, f (x, y) ∂ν‖ ^ 2 ≤ ∫ y, ‖f (x, y)‖ ^ 2 ∂ν := by
    filter_upwards [hi.prod_right_ae, hs.prod_right_ae] with x hix hsx
    have hc : ConvexOn ℝ univ (fun z : Ambient q => ‖z‖ ^ 2) :=
      (convexOn_univ_norm (E := Ambient q)).pow (fun _ _ => norm_nonneg _) 2
    exact hc.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => mem_univ _) hix hsx
  have hsq : Integrable (fun x => ‖∫ y, f (x, y) ∂ν‖ ^ 2) μ :=
    hs.integral_prod_left.mono' (hm.norm.pow 2) (hbound.mono fun x hx => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hx)
  exact ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hsq,
    (integral_mono_ae hsq hs.integral_prod_left hbound).trans_eq (integral_prod _ hs).symm⟩


/-- The Bochner integral of the actual slice curve has the original product
pairings against every native angular L2 class. -/
theorem exists_native_lp_two_time_curve_with_pairings {n q : ℕ} (hn : 0 < n) (a b : ℝ)
    {f : sphere (0 : Domain n) 1 × ℝ → Ambient q}
    (hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b)))) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃ F : ℝ → Lp (Ambient q) 2 σ,
      MemLp F 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ, F t = ht.toLp (fun θ => f (θ, t))) ∧
      ∀ (φ : ℝ → ℝ), Continuous φ → HasCompactSupport φ →
        ∀ c : Lp (Ambient q) 2 σ,
          inner ℝ c (∫ t in Icc a b, φ t • F t) =
            ∫ θ, (∫ t in Icc a b, φ t * inner ℝ (c θ) (f (θ, t))) ∂σ := by
  intro σ
  let ν : Measure ℝ := volume.restrict (Icc a b)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  obtain ⟨F, hF, hFs, _⟩ := exists_native_lp_two_time_curve hn a b hf
  refine ⟨F, hF, hFs, ?_⟩
  intro φ hφ hφc c
  have hφL : MemLp φ ∞ ν := hφ.memLp_top_of_hasCompactSupport hφc ν
  have hφP : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => φ p.2) ∞ (σ.prod ν) :=
    hφL.comp_snd σ
  have hweighted : MemLp (fun p => φ p.2 • f p) 2 (σ.prod ν) := hf.smul hφP
  have hcP : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => c p.1) 2 (σ.prod ν) :=
    (Lp.memLp c).comp_fst ν
  have hpI : Integrable (fun p : sphere (0 : Domain n) 1 × ℝ =>
      inner ℝ (c p.1) (φ p.2 • f p)) (σ.prod ν) := by
    have hi := L2.integrable_inner (𝕜 := ℝ) (hcP.toLp _) (hweighted.toLp _)
    apply hi.congr
    filter_upwards [hcP.coeFn_toLp, hweighted.coeFn_toLp] with p hc hf
    rw [hc, hf]
  have hFW : MemLp (fun t => φ t • F t) 2 ν := hF.smul hφL
  have hFI : Integrable (fun t => φ t • F t) ν := hFW.integrable (by norm_num)
  rw [← integral_inner hFI c]
  have hpair : ∀ᵐ t ∂ν, inner ℝ c (φ t • F t) =
      ∫ θ, inner ℝ (c θ) (φ t • f (θ, t)) ∂σ := by
    filter_upwards [hFs] with t ht
    obtain ⟨hft, hFt⟩ := ht
    have hinner : inner ℝ c (hft.toLp (fun θ => f (θ, t))) =
        ∫ θ, inner ℝ (c θ) (f (θ, t)) ∂σ := by
      rw [L2.inner_def]
      exact integral_congr_ae (hft.coeFn_toLp.mono fun θ hθ => by exact congrArg (inner ℝ (c θ)) hθ)
    rw [hFt, inner_smul_right, hinner]
    simp only [inner_smul_right]
    exact (integral_const_mul (φ t) _).symm
  rw [integral_congr_ae hpair, ← integral_prod_symm _ hpI, integral_prod _ hpI]
  simp only [inner_smul_right]
  rfl

end StratificationTheory
