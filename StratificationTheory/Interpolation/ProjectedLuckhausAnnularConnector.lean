module

public import StratificationTheory.Frozen.LuckhausJoint
public import StratificationTheory.Interpolation.CylinderAnnularCoherentEnergy
public import StratificationTheory.Interpolation.ProjectedCollar
public import StratificationTheory.Foundation.CylinderTraceAlgebra
public import StratificationTheory.Foundation.CylinderTracePostcomposition
public import StratificationTheory.Foundation.PositiveThinAnnularScale

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal ContDiff
namespace StratificationTheory.Interpolation

/-- Actual Luckhaus data give one target-valued annular weak pair with
quantitative energy and matching complete radial trace classes. -/
theorem exists_projected_luckhaus_annulus_operator {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (r η : ℝ) (hr : 0 < r) (hη : 0 < η) (hηsmall : η < 1 / 8)
        (u v : sphere (0 : Domain n) 1 → Ambient q)
        (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v)
        (_huN : ∀ᵐ θ ∂Measure.euclideanHausdorffMeasure (n - 1), u θ ∈ N.carrierSet)
        (_hvN : ∀ᵐ θ ∂Measure.euclideanHausdorffMeasure (n - 1), v θ ∈ N.carrierSet),
      let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
      let A := ∫ θ : sphere (0 : Domain n) 1,
        ∑ i : Fin n, (‖sphereGradient hn u hu i θ‖ ^ 2 + ‖sphereGradient hn v hv i θ‖ ^ 2) ∂σ
      let D := ∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2 ∂σ
      let lo := r / (1 + η)
      let V : OpenDomain n := ⟨{x | lo < ‖x‖ ∧ ‖x‖ < r}, isOpen_Ioo.preimage continuous_norm⟩
      C * η ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt A * Real.sqrt D +
        C * η ^ (-(n : ℤ)) * D < ρ ^ 2 →
      ∃ (W : Domain n → Ambient q) (DW : Domain n → Gradient n q)
        (K : C(Icc lo r, Lp (Ambient q) 2 σ)),
        MemW12 V W DW ∧ (∀ᵐ x ∂volume.restrict V.val, W x ∈ N.carrierSet) ∧
        (∫ x in V.val, hsNormSq (DW x)) ≤ 8 * C * r ^ (n - 2) * (η * A + η⁻¹ * D) ∧
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo lo r,
          ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => W (t • θ.val)) 2 σ,
            K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => W (t • θ.val))) ∧
        K ⟨lo, le_rfl, (positive_thin_annular_scale hn hr hη hηsmall).2.2.1.le⟩ = hu.1.toLp u ∧
        K ⟨r, (positive_thin_annular_scale hn hr hη hηsmall).2.2.1.le, le_rfl⟩ = hv.1.toLp v ∧
        (∀ t : Icc lo r, ∀ᵐ θ ∂σ, K t θ ∈ N.carrierSet) := by
  obtain ⟨C, hC, hLuckhaus⟩ := luckhaus_joint n hn
  obtain ⟨ρ, Q, hρ, _hρbase, hQ, ⟨L, _hL, hQL⟩, hfix, hnear⟩ :=
    exists_smooth_target_projection N
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro r η hr hη hηsmall u v hu hv huN hvN σ A D lo V hSmall
  obtain ⟨hlo, _hhalf, hlor, hscale, hJ⟩ := positive_thin_annular_scale hn hr hη hηsmall
  have hLoR : lo * (1 + η) = r := by simpa only [mul_comm] using hscale
  change (r / (1 + η)) * (1 + η) = r at hLoR
  have hA : (∫ θ : sphere (0 : Domain n) 1,
      hsNormSq (fun i : Fin n => sphereGradient hn u hu i θ) +
        hsNormSq (fun i : Fin n => sphereGradient hn v hv i θ) ∂σ) = A := by
    apply integral_congr_ae
    filter_upwards [] with θ
    simp only [hsNormSq, Finset.sum_add_distrib]
  have hD : (∫ θ : sphere (0 : Domain n) 1, ‖u θ - v θ‖ ^ 2 ∂σ) = D := by
    apply integral_congr_ae
    filter_upwards [] with θ
    rw [norm_sub_rev]
  obtain ⟨w, hw, W₀, D₀, g, hW₀, hRaw, hCoh, hg, _hTang, _hInt, hEg, hTube, hTa, hTb⟩ :=
    hLuckhaus q N.carrierSet N.isCompact u v hu hv huN hvN η ⟨hη, hηsmall⟩
  rw [hA, hD] at hEg hTube
  have hValues : ∀ᵐ c : unitCylinder n 0 η ∂Measure.euclideanHausdorffMeasure n,
      Q (w c) ∈ N.carrierSet ∧ ‖fderiv ℝ Q (w c)‖ ≤ 2 := by
    filter_upwards [hTube] with c hc
    have hClose : infDist (w c) N.carrierSet < ρ := by
      nlinarith [infDist_nonneg (x := w c) (s := N.carrierSet)]
    obtain ⟨_ht, _hEq, hN, hBound⟩ := hnear (w c) hClose
    exact ⟨hN, hBound⟩
  have hBound : ∀ᵐ c : unitCylinder n 0 η ∂Measure.euclideanHausdorffMeasure n,
      ‖fderiv ℝ Q (w c)‖ ≤ ((2 : ℝ≥0) : ℝ) := hValues.mono fun _ hc => hc.2
  have hAnn := exists_cylinder_annular_postcomposition_trace_energy hn hη (by norm_num) hlo
    w hw W₀ D₀ g Q hQ L hQL 2 hW₀ hRaw hCoh hg hBound
  simp only [add_zero, mul_one, hLoR] at hAnn
  obtain ⟨hQw, W, DW, hW, hWRaw, hE, hTrace⟩ := hAnn
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let τ : C(Icc lo r, Icc (0 : ℝ) η) :=
    ⟨fun t => ⟨t.val / lo - 1, by
      constructor
      · have hh : 1 ≤ t.val / lo := (le_div_iff₀ hlo).mpr (by simpa only [one_mul] using t.property.1)
        linarith
      · have hh : t.val / lo ≤ 1 + η := (div_le_iff₀ hlo).mpr (by rw [hscale]; exact t.property.2)
        linarith⟩, by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.div_const lo).sub (continuous_const (y := (1 : ℝ)))⟩
  let H := cylinderTrace hn hη (Q ∘ w) hQw
  let K := H.comp τ
  have hTarget : ∀ᵐ x ∂volume.restrict V.val, W x ∈ N.carrierSet := by
    have hh := ae_annular_property_of_native_cylinder (by omega) hlo (by norm_num) (Q ∘ w) W
      (fun z => z ∈ N.carrierSet) (hValues.mono fun _ hc => hc.1) hWRaw
    simpa only [add_zero, mul_one, hLoR] using hh
  have hTrace' : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo lo r,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => W (t • θ.val)) 2 σ,
        K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => W (t • θ.val)) := by
    exact hTrace
  refine ⟨W, DW, K, hW, hTarget, ?_, hTrace', ?_, ?_, ?_⟩
  · have hE' : (∫ x in V.val, hsNormSq (DW x)) ≤
        (lo * r ^ (n - 1)) * lo⁻¹ ^ 2 * 4 * (C * η * A + C / η * D) := by
      norm_num only [NNReal.coe_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num, max_self] at hE
      exact hE.trans (mul_le_mul_of_nonneg_left hEg (by positivity))
    have hJ' : (lo * r ^ (n - 1)) * lo⁻¹ ^ 2 ≤ 2 * r ^ (n - 2) := by
      simpa only [hLoR, add_zero, mul_one, max_self] using hJ
    have hEnonneg : 0 ≤ C * η * A + C / η * D := by
      dsimp only [A, D]
      exact add_nonneg (mul_nonneg (mul_nonneg hC.le hη.le)
        (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
        (mul_nonneg (div_nonneg hC.le hη.le) (integral_nonneg fun _ => sq_nonneg _))
    calc
      _ ≤ _ := hE'
      _ ≤ (2 * r ^ (n - 2)) * 4 * (C * η * A + C / η * D) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ' (by norm_num)) hEnonneg
      _ = _ := by rw [div_eq_mul_inv]; ring
  · have hτlo : τ ⟨lo, le_rfl, hlor.le⟩ = ⟨0, le_rfl, hη.le⟩ := by
      apply Subtype.ext
      change lo / lo - 1 = (0 : ℝ)
      dsimp only [lo]
      field_simp; ring
    change H (τ ⟨lo, le_rfl, hlor.le⟩) = _
    rw [hτlo]
    obtain ⟨hT, hEq⟩ := cylinderTrace_postcompose hn hη w hw Q hQ L hQL ⟨0, le_rfl, hη.le⟩
    change cylinderTrace hn hη (Q ∘ w) hQw _ = _
    rw [hEq]
    apply Lp.ext
    filter_upwards [hT.coeFn_toLp, hu.1.coeFn_toLp, huN] with θ hLeft hRight hN
    have hOld : cylinderTrace hn hη w hw ⟨0, le_rfl, hη.le⟩ θ = u θ := by rw [hTa]; exact hRight
    exact hLeft.trans ((congrArg Q hOld).trans ((hfix _ hN).trans hRight.symm))
  · have hτhi : τ ⟨r, hlor.le, le_rfl⟩ = ⟨η, hη.le, le_rfl⟩ := by
      apply Subtype.ext
      change r / lo - 1 = η
      rw [← hscale, mul_div_cancel_right₀ _ hlo.ne']
      ring
    change H (τ ⟨r, hlor.le, le_rfl⟩) = _
    rw [hτhi]
    obtain ⟨hT, hEq⟩ := cylinderTrace_postcompose hn hη w hw Q hQ L hQL ⟨η, hη.le, le_rfl⟩
    change cylinderTrace hn hη (Q ∘ w) hQw _ = _
    rw [hEq]
    apply Lp.ext
    filter_upwards [hT.coeFn_toLp, hv.1.coeFn_toLp, hvN] with θ hLeft hRight hN
    have hOld : cylinderTrace hn hη w hw ⟨η, hη.le, le_rfl⟩ θ = v θ := by rw [hTb]; exact hRight
    exact hLeft.trans ((congrArg Q hOld).trans ((hfix _ hN).trans hRight.symm))
  · intro t
    exact cylinderTrace_mem_closed hn hη (Q ∘ w) hQw N.isClosed
      (hValues.mono fun _ hc => hc.1) (τ t)

end StratificationTheory.Interpolation
