module

public import StratificationTheory.Foundation.SpatialConeNormalPatchGeometry
public import StratificationTheory.Foundation.SpatialConeNormalTrace
public import StratificationTheory.Foundation.SpatialConeTimeSobolev
public import StratificationTheory.Foundation.CoordinateRectangleTrace
public import StratificationTheory.Foundation.LocalRawTraceEndpoint

/-!
# Canonical spatial normal traces with independent time

Original face-times-time Sobolev data produce the actual weak cone graph on
small inward normal rectangles. Its canonical continuous native L2 trace
has the endpoint determined by the original flat trace.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StratificationTheory

/-- The same original spatial cone map has a genuine full weak graph on
uniform normal rectangles and the canonical original flat endpoint class. -/
theorem exists_canonical_spatial_cone_normal_trace {n q : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSbound : ∀ x ∈ S, ∀ i : Fin n, |x i| < 1)
    {a b₀ b₁ c d : ℝ} (ha : a < 1) (hb₀ : 0 < b₀) (hb₁ : b₁ < 2)
    (w : Domain (n + 1 + 1) → Ambient q)
    (Dw : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let B : OpenDomain (n + 1) :=
      ⟨⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let Ω : OpenDomain (n + 1 + 1) :=
      ⟨{z | (e z).1 ∈ B.val ∧ (e z).2 0 ∈ Ioo c d},
        (B.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    MemW12 Ω w Dw →
    let μ := ((volume : Measure (Domain n)).restrict S).prod (volume.restrict (Ioo c d))
    let f : (Domain n × ℝ) × ℝ → Ambient q := fun p =>
      w (e.symm (b.symm (p.1.1,EuclideanSpace.single (0 : Fin 1) p.2),
        EuclideanSpace.single (0 : Fin 1) p.1.2))
    ∀ H : C(Icc a 1,Lp (Ambient q) 2 μ), AEStronglyMeasurable f (μ.prod (volume.restrict (Ioo a 1))) →
    (∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 μ,
        H ⟨z,hz.1.le,hz.2.le⟩ = hs.toLp (fun x => f (x,z))) →
    ∀ g : Domain n × ℝ → Ambient q, ∀ hg : MemLp g 2 μ,
      H ⟨1,ha.le,le_rfl⟩ = hg.toLp g →
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let V := {y : Domain (n + 1 + 1) | (e y).1 ∈ C ∧ (e y).2 0 ∈ Ioo c d}
    let Fcone : Domain (n + 1 + 1 + 1) → Domain (n + 1 + 1) := fun y =>
      e.symm ((((e (eF y).1).2 0)⁻¹ • (e (eF y).1).1),(eF y).2)
    let W := w ∘ Fcone
    let D : Domain (n + 1 + 1 + 1) → Gradient (n + 1 + 1 + 1) q := fun y i =>
      ∑ j : Fin (n + 1 + 1), (fderiv ℝ Fcone y (EuclideanSpace.single i 1)) j • Dw (Fcone y) j
    let G : Domain (n + 1 + 1) → Ambient q := fun y => g (ξ (e y).1,(e y).2 0)
    ∃ F : Domain (n + 1 + 1 + 1) ≃L[ℝ] Domain (n + 1 + 1 + 1),
      (∀ y η, F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n) ∧
      ∀ U : OpenDomain (n + 1 + 1), IsCompact (closure U.val) → closure U.val ⊆ interior V →
      let σ := (volume : Measure (Domain (n + 1 + 1))).restrict U.val
      let R : ℝ → OpenDomain (n + 1 + 1 + 1) := fun δ =>
        ⟨{y | (eF y).1 ∈ U.val ∧ (eF y).2 0 ∈ Ioo (0 : ℝ) δ},
          (U.property.preimage (continuous_fst.comp eF.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp eF.continuous)))⟩
      ∃ δ : ℝ, ∃ hδ : 0 < δ,
        MemW12 (R δ) (W ∘ F) (fun y i => ∑ j : Fin (n + 1 + 1 + 1),
          (F (EuclideanSpace.single i 1)) j • D (F y) j) ∧
        ∃! J : C(Icc (0 : ℝ) δ,Lp (Ambient q) 2 σ),
          (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) δ,
            ∃ hs : MemLp (fun y => W (F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) t)))) 2 σ,
              J ⟨t,ht.1.le,ht.2.le⟩ = hs.toLp
                (fun y => W (F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) t))))) ∧
          ∃ hG : MemLp G 2 σ, J ⟨0,le_rfl,hδ.le⟩ = hG.toLp G := by
  intro b e eF B Ω hw μ f H hf hSlices g hg hEnd T ξ C V Fcone W D G
  obtain ⟨F,hF₀⟩ := exists_spatial_cone_normal_linear_chart n
  have hF : ∀ (y : Domain (n + 1 + 1)) (η : ℝ),
      F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) η)) =
        spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n := hF₀
  clear hF₀
  refine ⟨F,hF,?_⟩
  intro U hK hUV σ R
  have hSfinite : (volume : Measure (Domain n)) S ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_unit_coordinate_face_ne_top n) (measure_mono (fun x hx =>
      (mem_unit_coordinate_face_iff x).mpr (hSbound x hx)))
  have hΓ : Continuous (spatialConeParallelSlice n 0) := by
    have hEq : spatialConeParallelSlice n 0 = fun y =>
        F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) (0 : ℝ))) := by
      funext y
      simpa only [zero_smul,add_zero] using (hF y 0).symm
    rw [hEq]
    exact F.continuous.comp (eF.symm.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hΓ.continuousOn
  let ρ := b₀ / 2
  have hρ : 0 < ρ := half_pos hb₀
  have hGeometry : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ y ∈ closure U.val,
      let z := spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n
      (e (eF z).1).2 0 ∈ Ioo ρ 2 ∧
      (∀ i : Fin (n + 1), |(e (eF z).1).1 i| < (e (eF z).1).2 0) ∧
      (eF z).2 0 ∈ Ioo c d ∧ ‖z‖ < M + 1 := by
    apply eventually_spatial_normal_patch_inside_cone hK
    intro y hy
    have hyV : y ∈ V := interior_subset (hUV hy)
    have ht : 0 < T (e y).1 := hb₀.trans_le hyV.1.1.1
    refine ⟨ht,?_,hyV.1.1.2.trans_lt hb₁,?_,hyV.2,lt_of_le_of_lt (hM y hy) (lt_add_one M)⟩
    · change b₀ / 2 < T (e y).1
      linarith only [hyV.1.1.1,hb₀]
    · intro i
      have hi := hSbound (ξ (e y).1) hyV.1.2 i
      change |(T (e y).1)⁻¹ * (b (e y).1).1 i| < 1 at hi
      rw [abs_mul,abs_of_pos (inv_pos.mpr ht)] at hi
      have hi' : |(b (e y).1).1 i| / T (e y).1 < 1 := by
        rw [div_eq_mul_inv,mul_comm]
        exact hi
      exact (div_lt_one ht).mp hi'
  obtain ⟨δ,hδ,hδGeo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hGeometry
  obtain ⟨_hc,L,_hL,hTransport⟩ := exists_spatial_cone_time_sobolev_transport (n + 1) hρ (M + 1)
  obtain ⟨A,hA,hData⟩ := hTransport B c d
  have hWA : MemW12 A W D := (hData q w Dw hw).1
  have hPull := memW12_continuousLinearEquiv_preimage F hWA
  have hSub : (R δ).val ⊆ F ⁻¹' A.val := by
    intro z hz
    have hsingle (t : Domain 1) : EuclideanSpace.single (0 : Fin 1) (t 0) = t := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.single_apply,ite_true]
    have hzRep : eF.symm ((eF z).1,EuclideanSpace.single (0 : Fin 1) ((eF z).2 0)) = z := by
      rw [hsingle,eF.symm_apply_apply]
    have hGeo := hδGeo hz.2 (eF z).1 (subset_closure hz.1)
    rw [← hF,hzRep] at hGeo
    rw [hA]
    refine ⟨⟨hGeo.1,?_⟩,mem_ball_zero_iff.mpr hGeo.2.2.2⟩
    change (e (Fcone (F z))).1 ∈ B.val ∧ (e (Fcone (F z))).2 0 ∈ Ioo c d
    rw [e.apply_symm_apply]
    refine ⟨mem_iInter.mpr (fun i => ?_),hGeo.2.2.1⟩
    change ((e (eF (F z)).1).2 0)⁻¹ * (e (eF (F z)).1).1 i ∈ Ioo (-1 : ℝ) 1
    apply abs_lt.mp
    rw [abs_mul,abs_of_pos (inv_pos.mpr (hρ.trans hGeo.1.1))]
    have hdiv := (div_lt_one (hρ.trans hGeo.1.1)).mpr (hGeo.2.1 i)
    rw [mul_comm,← div_eq_mul_inv]
    exact hdiv
  have hRect : MemW12 (R δ) (W ∘ F) (fun y i =>
      ∑ j : Fin (n + 1 + 1 + 1), (F (EuclideanSpace.single i 1)) j • D (F y) j) :=
    ⟨hPull.1.mono hSub,hPull.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i => (hPull.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  have hUfinite : (volume : Measure (Domain (n + 1 + 1))) U.val ≠ ⊤ :=
    ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono subset_closure)
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr hUfinite
  obtain ⟨J,hJ,hUnique⟩ := exists_unique_L2_trace_of_memW12_rectangle U hδ hRect
  let wp : Domain (n + 1) × ℝ → Ambient q := fun p =>
    w (e.symm (p.1,EuclideanSpace.single (0 : Fin 1) p.2))
  have hsingle (t : Domain 1) : EuclideanSpace.single (0 : Fin 1) (t 0) = t := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.single_apply,ite_true]
  have hNormal := (native_spatial_face_cone_normal_side_L2 hS hSfinite ha hb₀ wp H hf hSlices
    g hg hEnd).2 (closure U.val) hK hUV
  have hWpoint (z : Domain (n + 1 + 1 + 1)) :
      wp ((((e (eF z).1).2 0)⁻¹ • (e (eF z).1).1),(eF z).2 0) = W z := by
    change w (e.symm ((((e (eF z).1).2 0)⁻¹ • (e (eF z).1).1),
      EuclideanSpace.single (0 : Fin 1) ((eF z).2 0))) =
        w (e.symm ((((e (eF z).1).2 0)⁻¹ • (e (eF z).1).1),(eF z).2))
    rw [hsingle]
  let Wp : Domain (n + 1 + 1 + 1) → Ambient q := fun z =>
    wp ((((e (eF z).1).2 0)⁻¹ • (e (eF z).1).1),(eF z).2 0)
  have hWp : Wp = W := funext hWpoint
  change
    (∀ᶠ t in 𝓝[>] (0 : ℝ), MemLp
      (fun y => Wp (spatialConeParallelSlice n 0 y + t • spatialConeNormalVector n) - G y)
        2 (volume.restrict (closure U.val))) ∧
    Tendsto (fun t : ℝ => eLpNorm
      (fun y => Wp (spatialConeParallelSlice n 0 y + t • spatialConeNormalVector n) - G y)
        2 (volume.restrict (closure U.val))) (𝓝[>] 0) (𝓝 0) at hNormal
  rw [hWp] at hNormal
  have hNormal' :
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MemLp
        (fun y => W (F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) t))) - G y)
          2 (volume.restrict (closure U.val))) ∧
      Tendsto (fun t : ℝ => eLpNorm
        (fun y => W (F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) t))) - G y)
          2 (volume.restrict (closure U.val))) (𝓝[>] 0) (𝓝 0) := by
    simp only [hF]
    exact hNormal
  obtain ⟨hGL2,hJEnd⟩ := exists_left_trace_class_of_local_raw_L2_limit σ
    (volume.restrict (closure U.val)) (Measure.restrict_mono_set volume subset_closure) hδ J
    (fun p => W (F (eF.symm (p.1,EuclideanSpace.single (0 : Fin 1) p.2)))) G hJ
    hNormal'.1 hNormal'.2
  refine ⟨δ,hδ,hRect,J,⟨hJ,hGL2,hJEnd⟩,?_⟩
  intro K hKJ
  exact hUnique K hKJ.1

end StratificationTheory
