module

public import StratificationTheory.Foundation.SmoothDomainSobolevPullback
public import StratificationTheory.Foundation.SobolevLocalAssembly

/-!
# Smooth coordinate pullback on arbitrary open domains

Local source balls establish the actual weak chain rule. Global native L2
domination then assembles the same function and the same columns on the whole
target domain. Neither domain is required to have finite total volume.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff BigOperators
namespace StratificationTheory

private theorem map_mono_of_ae_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} {F : X → Y} (hμν : μ ≤ ν) (hF : AEMeasurable F ν) :
    Measure.map F μ ≤ Measure.map F ν := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply_of_aemeasurable (hF.mono_measure hμν) hS,
    Measure.map_apply_of_aemeasurable hF hS]
  exact hμν _

private theorem map_restrict_le_smul_restrict_of_mapsTo
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {F : X → Y}
    {U V : Set X} {S B : Set Y} (hV : MeasurableSet V) (hB : MeasurableSet B)
    (hVU : V ⊆ U) (hBS : B ⊆ S) (hFV : MapsTo F V B)
    (hF : AEMeasurable F (μ.restrict U)) {c : ℝ≥0∞}
    (hmap : Measure.map F (μ.restrict U) ≤ c • ν.restrict S) :
    Measure.map F (μ.restrict V) ≤ c • ν.restrict B := by
  have hμ : μ.restrict V ≤ μ.restrict U := Measure.restrict_mono_set μ hVU
  have hFsmall : AEMeasurable F (μ.restrict V) := hF.mono_measure hμ
  have hsupp : ∀ᵐ y ∂Measure.map F (μ.restrict V), y ∈ B := by
    apply (ae_map_iff hFsmall hB).mpr
    filter_upwards [ae_restrict_mem hV] with x hx
    exact hFV hx
  have hbound := (map_mono_of_ae_measurable hμ hF).trans hmap
  calc
    Measure.map F (μ.restrict V) = (Measure.map F (μ.restrict V)).restrict B :=
      (Measure.restrict_eq_self_of_ae_mem hsupp).symm
    _ ≤ (c • ν.restrict S).restrict B := Measure.restrict_mono (Subset.rfl) hbound
    _ = c • ν.restrict B := by
      rw [Measure.restrict_smul, Measure.restrict_restrict hB, inter_eq_left.mpr hBS]

private theorem open_pullback_coefficient_memLp_top {m n : ℕ}
    (U : OpenDomain m) (F : Domain m → Domain n) (hF : ContDiffOn ℝ ∞ F U.val)
    (L : ℝ) (hDF : ∀ x ∈ U.val, ‖fderiv ℝ F x‖ ≤ L) (i : Fin m) (j : Fin n) :
    MemLp (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j) ∞
      (volume.restrict U.val) := by
  have hcont : ContinuousOn (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j)
      U.val :=
    (EuclideanSpace.proj j).continuous.continuousOn.comp
      ((hF.continuousOn_fderiv_of_isOpen U.property (by simp)).clm_apply
        continuousOn_const) (mapsTo_univ _ _)
  apply memLp_top_of_bound (hcont.aestronglyMeasurable U.property.measurableSet) L
  filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
  calc
    ‖(fderiv ℝ F x (EuclideanSpace.single i 1)) j‖ ≤
        ‖fderiv ℝ F x (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ j
    _ ≤ ‖fderiv ℝ F x‖ * ‖EuclideanSpace.single i 1‖ := (fderiv ℝ F x).le_opNorm _
    _ = ‖fderiv ℝ F x‖ := by
      have he : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
        simpa only [norm_one] using PiLp.norm_single 2 (fun _ : Fin m => ℝ) i (1 : ℝ)
      rw [he, mul_one]
    _ ≤ L := hDF x hx

/-- Smooth native coordinates pull back an arbitrary original finite Sobolev
graph, using genuine local source balls rather than a transformed weak-graph
assumption. Source and target dimensions may differ. -/
theorem memW12_smooth_open_domain_pullback {m n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (U : OpenDomain m)
    (F : Domain m → Domain n) (hF : ContDiffOn ℝ ∞ F U.val)
    (hFU : MapsTo F U.val Ω.val)
    (L : ℝ) (hDF : ∀ x ∈ U.val, ‖fderiv ℝ F x‖ ≤ L)
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hmap : Measure.map F (volume.restrict U.val) ≤ c • volume.restrict Ω.val) :
    MemW12 U (u ∘ F)
      (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j •
        Du (F x) j) := by
  have hFm : AEMeasurable F (volume.restrict U.val) :=
    hF.continuousOn.aemeasurable U.property.measurableSet
  have huL : MemLp (u ∘ F) 2 (volume.restrict U.val) :=
    memLp_comp_of_map_le_smul hFm hc hmap hu.2.1
  have hD (i : Fin m) : MemLp
      (fun x => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • Du (F x) j)
      2 (volume.restrict U.val) := by
    have hL := memLp_finsetSum Finset.univ (fun j _ =>
      (memLp_comp_of_map_le_smul hFm hc hmap (hu.2.2 j)).smul (r := (2 : ℝ≥0∞))
        (open_pullback_coefficient_memLp_top U F hF L hDF i j))
    simpa only [Finset.sum_apply, Pi.smul_apply', Function.comp_def] using hL
  apply memW12_of_local_sobolev_pair huL hD
  intro x hx
  obtain ⟨R, hR, hRΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Ω.property.mem_nhds (hFU hx))
  have hFcx : ContinuousAt F x := hF.continuousOn.continuousAt (U.property.mem_nhds hx)
  have hneigh : U.val ∩ F ⁻¹' ball (F x) R ∈ 𝓝 x :=
    inter_mem (U.property.mem_nhds hx) (hFcx.preimage_mem_nhds (ball_mem_nhds _ hR))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hneigh
  have hBU : ball x r ⊆ U.val := fun y hy => (hsub hy).1
  have hFB : MapsTo F (ball x r) (ball (F x) R) := fun y hy => (hsub hy).2
  have hBΩ : ball (F x) R ⊆ Ω.val := ball_subset_closedBall.trans hRΩ
  have hlocalmap : Measure.map F (volume.restrict (ball x r)) ≤
      c • volume.restrict (ball (F x) R) :=
    map_restrict_le_smul_restrict_of_mapsTo measurableSet_ball measurableSet_ball
      hBU hBΩ hFB hFm hmap
  refine ⟨r, hr, hBU, ?_⟩
  exact memW12_smooth_domain_pullback_ball hR (hu.to_memW12Loc.memW12_ball hRΩ)
    (ballDomain x r) measure_ball_ne_top F (hF.mono hBU) L
    (fun y hy => hDF y (hBU hy)) c hc hlocalmap

end StratificationTheory
