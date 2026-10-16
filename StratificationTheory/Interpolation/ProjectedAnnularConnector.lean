module

public import StratificationTheory.Frozen.AffineAnnularPostcomposition
public import StratificationTheory.Frozen.CylinderAnnularTransfer
public import StratificationTheory.Foundation.CylinderTracePostcomposition
public import StratificationTheory.Foundation.CylinderTraceAlgebra
public import StratificationTheory.Foundation.AnnularRawEquality
public import StratificationTheory.Interpolation.LinearCylinderTrace
public import StratificationTheory.Interpolation.ProjectedCollar
public import StratificationTheory.Foundation.AnnularPropertyTransfer
public import StratificationTheory.Foundation.ThinAnnularScale

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ContDiff
namespace StratificationTheory

/-- The actual annular postcomposition has one weak pair carrying the energy
bound and the original continuous cylinder trace under radial rescaling. -/
theorem exists_affine_annular_postcomposition_trace_energy {n q k : ℕ} (hn : 2 ≤ n)
    {a b s : ℝ} (hab : a < b) (ha : -1 < a) (hs : 0 < s)
    (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (C : NNReal) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : unitCylinder n a b → Ambient q := fun y =>
      (1 - ((e y.val).2 0 - a) / (b - a)) • u ⟨(e y.val).1, y.property.1⟩ +
        (((e y.val).2 0 - a) / (b - a)) • v ⟨(e y.val).1, y.property.1⟩
    let lo := s * (1 + a)
    let hi := s * (1 + b)
    let V : OpenDomain n := ⟨{x : Domain n | lo < ‖x‖ ∧ ‖x‖ < hi},
      isOpen_Ioo.preimage continuous_norm⟩
    let κ := max lo⁻¹ s⁻¹
    let τ : C(Icc lo hi, Icc a b) :=
      ⟨fun r => ⟨r.val / s - 1, by
        constructor
        · have h : a + 1 ≤ r.val / s := (le_div_iff₀ hs).mpr (by
            have hr := r.property.1
            dsimp only [lo] at hr
            nlinarith only [hr])
          linarith only [h]
        · have h : r.val / s ≤ b + 1 := (div_le_iff₀ hs).mpr (by
            have hr := r.property.2
            dsimp only [hi] at hr
            nlinarith only [hr])
          linarith only [h]⟩,
        by
          apply Continuous.subtype_mk
          exact (continuous_subtype_val.div_const s).sub (continuous_const (y := (1 : ℝ)))⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      ‖fderiv ℝ F (c y)‖ ≤ (C : ℝ)) →
    ∃ hFc : MemCylinderW12 hn hab (F ∘ c),
      let H := cylinderTrace hn hab (F ∘ c) hFc
      let K := H.comp τ
      ∃ W : Domain n → Ambient k, ∃ DW : Domain n → Gradient n k,
        MemW12 V W DW ∧
        (∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
          W ((s * (1 + t)) • θ.val) =
            F ((1 - (t - a) / (b - a)) • u θ + ((t - a) / (b - a)) • v θ)) ∧
        (∫ x in V.val, hsNormSq (DW x)) ≤
          (s * (s * (1 + b)) ^ (n - 1)) * κ ^ 2 * (C : ℝ) ^ 2 *
            (((b - a) / 2) * (∫ θ : sphere (0 : Domain n) 1,
              ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
                ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂σ) +
              (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2 ∂σ)) ∧
        (∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo lo hi,
          ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => W (r • θ.val)) 2 σ,
            K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ => W (r • θ.val))) ∧
        (∃ hFu : MemLp (F ∘ u) 2 σ,
          H ⟨a, le_rfl, hab.le⟩ = hFu.toLp (F ∘ u)) ∧
        (∃ hFv : MemLp (F ∘ v) 2 σ,
          H ⟨b, hab.le, le_rfl⟩ = hFv.toLp (F ∘ v)) := by
  intro e c lo hi V κ τ σ hbound
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  obtain ⟨hc, _hcT, hca, hcb, _hcinc⟩ :=
    cylinderTrace_linearInterpolation hn hab u v hu hv
  let hFc := memCylinderW12_postcompose hn hab c hc F hF L hDF
  obtain ⟨W₀, D₀, hW₀, hraw₀, hE₀⟩ :=
    exists_affine_annular_postcomposition hn hab ha hs u v hu hv F hF L hDF C hbound
  obtain ⟨W, DW, hW, hraw, htrace⟩ :=
    cylinder_to_annulus_exists hn hab ha hs (0 : Domain n) (F ∘ c) hFc
  have hW' : MemW12 V W DW := by simpa only [sub_zero] using hW
  have hcraw (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b) :
      c ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
        unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩ =
        (1 - (t - a) / (b - a)) • u θ + ((t - a) / (b - a)) • v θ := by
    dsimp only [c]
    simp only [ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true]
  have hraw' (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b) :
      W ((s * (1 + t)) • θ.val) =
        F ((1 - (t - a) / (b - a)) • u θ + ((t - a) / (b - a)) • v θ) := by
    have hp : W ((s * (1 + t)) • θ.val) =
        F (c ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
          unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩) := by
      simpa only [zero_add, Function.comp_apply] using hraw θ t ht
    exact hp.trans (congrArg F (hcraw θ t ht))
  have hcolsEnergy := annular_weak_columns_and_energy_eq_of_raw_ray_eq hs ha hW₀ hW'
    (fun θ t ht => (hraw₀ θ t ht).trans (hraw' θ t ht).symm)
  refine ⟨hFc, W, DW, hW', hraw', ?_, ?_, ?_, ?_⟩
  · rw [← hcolsEnergy.2]
    exact hE₀
  · simpa only [zero_add] using htrace
  · obtain ⟨hL, hEq⟩ := cylinderTrace_postcompose hn hab c hc F hF L hDF ⟨a, le_rfl, hab.le⟩
    refine ⟨memLp_postcomposition hu.1 hF hDF, ?_⟩
    rw [hEq]
    apply Lp.ext
    filter_upwards [hL.coeFn_toLp, (memLp_postcomposition hu.1 hF hDF).coeFn_toLp,
      hu.1.coeFn_toLp] with θ hleft hright hθ
    have hpoint : cylinderTrace hn hab c hc ⟨a, le_rfl, hab.le⟩ θ = u θ := by
      rw [hca]
      exact hθ
    exact hleft.trans ((congrArg F hpoint).trans hright.symm)
  · obtain ⟨hL, hEq⟩ := cylinderTrace_postcompose hn hab c hc F hF L hDF ⟨b, hab.le, le_rfl⟩
    refine ⟨memLp_postcomposition hv.1 hF hDF, ?_⟩
    rw [hEq]
    apply Lp.ext
    filter_upwards [hL.coeFn_toLp, (memLp_postcomposition hv.1 hF hDF).coeFn_toLp,
      hv.1.coeFn_toLp] with θ hleft hright hθ
    have hpoint : cylinderTrace hn hab c hc ⟨b, hab.le, le_rfl⟩ θ = v θ := by
      rw [hcb]
      exact hθ
    exact hleft.trans ((congrArg F hpoint).trans hright.symm)

namespace Interpolation

/-- A uniform smooth target projection gives actual thin-annulus weak data,
target values, quantitative energy, and matching native endpoint traces.
The tubular input concerns the original affine connector. -/
theorem exists_projected_thin_affine_annulus_operator {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ (ρ : ℝ) (Q : Ambient q → Ambient q),
      0 < ρ ∧ ContDiff ℝ ∞ Q ∧ (∀ z ∈ N.carrierSet, Q z = z) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (s η : ℝ) (hs : 0 < s) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
        (u v : sphere (0 : Domain n) 1 → Ambient q)
        (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v)
        (huN : ∀ᵐ θ ∂Measure.euclideanHausdorffMeasure (n - 1), u θ ∈ N.carrierSet)
        (hvN : ∀ᵐ θ ∂Measure.euclideanHausdorffMeasure (n - 1), v θ ∈ N.carrierSet),
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let c : unitCylinder n (-η) 0 → Ambient q := fun y =>
        (1 - ((e y.val).2 0 + η) / η) • u ⟨(e y.val).1, y.property.1⟩ +
          (((e y.val).2 0 + η) / η) • v ⟨(e y.val).1, y.property.1⟩
      let lo := s * (1 + -η)
      let V : OpenDomain n := ⟨{x : Domain n | lo < ‖x‖ ∧ ‖x‖ < s},
        isOpen_Ioo.preimage continuous_norm⟩
      let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
      (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n (-η) 0)),
        infDist (c y) N.carrierSet < ρ) →
      ∃ W : Domain n → Ambient q, ∃ DW : Domain n → Gradient n q,
        ∃ K : C(Icc lo s, Lp (Ambient q) 2 σ),
          MemW12 V W DW ∧
          (∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo (-η) 0 →
            W ((s * (1 + t)) • θ.val) =
              Q ((1 - (t + η) / η) • u θ + ((t + η) / η) • v θ)) ∧
          (∀ᵐ x ∂volume.restrict V.val, W x ∈ N.carrierSet) ∧
          (∫ x in V.val, hsNormSq (DW x)) ≤
            16 * s ^ (n - 2) *
              ((η / 2) * (∫ θ : sphere (0 : Domain n) 1,
                ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
                  ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂σ) +
                η⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2 ∂σ)) ∧
          (∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo lo s,
            ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => W (r • θ.val)) 2 σ,
              K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ => W (r • θ.val))) ∧
          K ⟨lo, le_rfl, by dsimp only [lo]; nlinarith only [hs, hη]⟩ = hu.1.toLp u ∧
          K ⟨s, by dsimp only [lo]; nlinarith only [hs, hη], le_rfl⟩ = hv.1.toLp v ∧
          (∀ r : Icc lo s, ∀ᵐ θ ∂σ, K r θ ∈ N.carrierSet) := by
  obtain ⟨ρ, Q, hρ, _hρbase, hQ, ⟨L, _hL, hQL⟩, hfix, hnear⟩ :=
    exists_smooth_target_projection N
  refine ⟨ρ, Q, hρ, hQ, hfix, ?_⟩
  intro n hn s η hs hη hηhalf u v hu hv huN hvN e c lo V σ htube
  have hab : -η < (0 : ℝ) := by linarith only [hη]
  have ha : -1 < -η := by linarith only [hηhalf]
  have hvalues : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n (-η) 0)),
      Q (c y) ∈ N.carrierSet ∧ ‖fderiv ℝ Q (c y)‖ ≤ 2 := by
    filter_upwards [htube] with y hy
    obtain ⟨_ht, _heq, hmem, hD⟩ := hnear (c y) hy
    exact ⟨hmem, hD⟩
  have hbound : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n (-η) 0)),
      ‖fderiv ℝ Q (c y)‖ ≤ ((2 : NNReal) : ℝ) := hvalues.mono fun _ h => h.2
  have hbound' : ∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n (-η) 0)),
      ‖fderiv ℝ Q ((1 - ((e y.val).2 0 - -η) / (0 - -η)) •
        u ⟨(e y.val).1, y.property.1⟩ + (((e y.val).2 0 - -η) / (0 - -η)) •
          v ⟨(e y.val).1, y.property.1⟩)‖ ≤ ((2 : NNReal) : ℝ) := by
    simpa only [sub_neg_eq_add, zero_add] using hbound
  obtain ⟨hQc, W, DW, hW, hraw, hE, htrace, ⟨hQu, hHa⟩, ⟨hQv, hHb⟩⟩ :=
    exists_affine_annular_postcomposition_trace_energy hn hab ha hs u v hu hv Q hQ L hQL 2 hbound'
  simp only [sub_neg_eq_add, zero_add, add_zero, mul_one] at hQc hW hraw hE htrace hHa hHb
  let H := cylinderTrace hn hab (Q ∘ c) hQc
  have hlohi : lo < s := by dsimp only [lo]; nlinarith only [hs, hη]
  let τ : C(Icc lo s, Icc (-η) 0) :=
    ⟨fun r => ⟨r.val / s - 1, by
      constructor
      · have h : 1 + -η ≤ r.val / s := (le_div_iff₀ hs).mpr (by
          simpa only [lo, mul_comm] using r.property.1)
        linarith only [h]
      · have h : r.val / s ≤ 1 := (div_le_iff₀ hs).mpr (by simpa only [one_mul] using r.property.2)
        linarith only [h]⟩,
      by exact Continuous.subtype_mk ((continuous_subtype_val.div_const s).sub continuous_const) _⟩
  let K := H.comp τ
  have htarget : ∀ᵐ x ∂volume.restrict V.val, W x ∈ N.carrierSet := by
    have hrawc (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo (-η) 0) :
        W ((s * (1 + t)) • θ.val) =
          (Q ∘ c) ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
            unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩ := by
      have hp := hraw θ t ht
      simpa only [Function.comp_apply, c, ContinuousLinearEquiv.apply_symm_apply,
        PiLp.single_apply, ite_true] using hp
    have ht := ae_annular_property_of_native_cylinder (by omega : 0 < n) hs ha (Q ∘ c) W
      (fun z => z ∈ N.carrierSet) (hvalues.mono fun _ h => h.1) hrawc
    simpa only [add_zero, mul_one] using ht
  refine ⟨W, DW, K, hW, hraw, htarget, ?_, ?_, ?_, ?_, ?_⟩
  · have hJ := thin_annular_jacobian_reciprocal_factor_le hn hs hη hηhalf
    simp only [add_zero, mul_one] at hJ
    have hnonneg : 0 ≤ (η / 2) * (∫ θ : sphere (0 : Domain n) 1,
        ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
          ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂σ) +
        η⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2 ∂σ) :=
      add_nonneg (mul_nonneg (by positivity)
        (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
        (mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
    norm_num only [NNReal.coe_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at hE
    calc
      _ ≤ _ := hE
      _ ≤ (4 * s ^ (n - 2)) * 4 * _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ (by norm_num)) hnonneg
      _ = _ := by ring
  · exact htrace
  · have hτlo : τ ⟨lo, le_rfl, hlohi.le⟩ = ⟨-η, le_rfl, hab.le⟩ := by
      apply Subtype.ext
      change (s * (1 + -η)) / s - 1 = -η
      rw [mul_div_cancel_left₀ _ hs.ne']
      ring
    change H (τ ⟨lo, le_rfl, hlohi.le⟩) = _
    rw [hτlo]
    change cylinderTrace hn hab (Q ∘ c) hQc _ = _
    rw [hHa]
    apply Lp.ext
    filter_upwards [hQu.coeFn_toLp, hu.1.coeFn_toLp, huN] with θ hleft hright hN
    exact hleft.trans ((hfix _ hN).trans hright.symm)
  · have hτhi : τ ⟨s, hlohi.le, le_rfl⟩ = ⟨0, hab.le, le_rfl⟩ := by
      apply Subtype.ext
      change s / s - 1 = (0 : ℝ)
      simp only [div_self hs.ne', sub_self]
    change H (τ ⟨s, hlohi.le, le_rfl⟩) = _
    rw [hτhi]
    change cylinderTrace hn hab (Q ∘ c) hQc _ = _
    rw [hHb]
    apply Lp.ext
    filter_upwards [hQv.coeFn_toLp, hv.1.coeFn_toLp, hvN] with θ hleft hright hN
    exact hleft.trans ((hfix _ hN).trans hright.symm)
  · intro r
    exact cylinderTrace_mem_closed hn hab (Q ∘ c) hQc N.isClosed
      (hvalues.mono fun _ h => h.1) (τ r)

end Interpolation
end StratificationTheory
