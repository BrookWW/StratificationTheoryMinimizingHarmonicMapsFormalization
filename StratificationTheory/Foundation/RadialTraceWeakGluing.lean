module

public import StratificationTheory.Foundation.RadialPiecewiseSobolevData
public import StratificationTheory.Foundation.RadialTraceFlux
public import StratificationTheory.Foundation.RadialCutoffFluxIntegral
public import StratificationTheory.Foundation.ContinuousRadialCutoffLimit
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HarmonicMaps.Analysis.SobolevCutoff

/-!
# Distributional radial gluing from matching native traces

Actual compact tests on the two open pieces leave opposite scalar radial
fluxes. Their continuous native trace classes identify the limiting flux at
the common sphere.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

private theorem tendsto_integral_bounded_multiplier {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : Integrable g μ)
    (a : ℕ → α → ℝ) (ha : ∀ k, AEStronglyMeasurable (a k) μ)
    (hb : ∀ k, ∀ᵐ x ∂μ, |a k x| ≤ 1)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun k => a k x) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun k => ∫ x, a k x * g x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun k => (ha k).mul hg.aestronglyMeasurable) hg.norm
    (fun k => (hb k).mono fun x hx => by
      change ‖a k x * g x‖ ≤ ‖g x‖
      rw [norm_mul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq (one_mul _))
    (ht.mono fun x hx => by simpa only [one_mul, Pi.mul_apply] using hx.mul_const (g x))
  exact h

private theorem weak_gradient_mul_cutoff_scalar {n q : ℕ}
    (Ω : OpenDomain n) (u : Domain n → Ambient q) (D : Domain n → Gradient n q)
    (hu : MemW12 Ω u D) (hfinite : (volume : Measure (Domain n)) Ω.val ≠ ⊤)
    (φ χ : Domain n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (hcφ : HasCompactSupport φ)
    (hs : tsupport (fun x => φ x * χ x) ⊆ Ω.val) (i : Fin n) (j : Fin q) :
    (∫ x in Ω.val, χ x * (coordinateDerivative φ hφ i x * (u x) j)) +
      (∫ x in Ω.val, (φ x * coordinateDerivative χ hχ i x) * (u x) j) =
        -(∫ x in Ω.val, χ x * (φ x * (D x i) j)) := by
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hfinite
  let ψ : Domain n → ℝ := fun x => φ x * χ x
  have hψ : ContDiff ℝ ∞ ψ := hφ.mul hχ
  have hcψ : HasCompactSupport ψ := hcφ.mul_right
  have hweak := hu.1.2.2 i ψ hψ hcψ hs
  have hscalar := congrArg (EuclideanSpace.proj (𝕜 := ℝ) j) hweak
  rw [← (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm
      (hu.1.integrable_test_derivative i hψ hcψ hs), map_neg,
    ← (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm
      (hu.1.integrable_test_gradient i hψ hcψ hs)] at hscalar
  change (∫ x in Ω.val, coordinateDerivative ψ hψ i x * (u x) j) =
    -(∫ x in Ω.val, ψ x * (D x i) j) at hscalar
  have huI : IntegrableOn (fun x => (u x) j) Ω.val :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp (hu.2.1.integrable (by norm_num))
  have hAI : IntegrableOn (fun x => χ x * (coordinateDerivative φ hφ i x * (u x) j)) Ω.val := by
    have hc : HasCompactSupport (coordinateDerivative φ hφ i) :=
      hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
    have hw : MemLp (fun x => χ x * coordinateDerivative φ hφ i x) ∞ (volume.restrict Ω.val) :=
      (hχ.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_top_of_hasCompactSupport
        hc.mul_left _
    have hh : IntegrableOn (fun x => (χ x * coordinateDerivative φ hφ i x) * (u x) j) Ω.val :=
      huI.smul_of_top_right hw
    simpa only [mul_assoc] using hh
  have hBI : IntegrableOn (fun x => (φ x * coordinateDerivative χ hχ i x) * (u x) j) Ω.val := by
    have hw : MemLp (fun x => φ x * coordinateDerivative χ hχ i x) ∞ (volume.restrict Ω.val) :=
      (hφ.continuous.mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_top_of_hasCompactSupport
        hcφ.mul_right _
    exact huI.smul_of_top_right hw
  have hpoint (x : Domain n) : coordinateDerivative ψ hψ i x * (u x) j =
      χ x * (coordinateDerivative φ hφ i x * (u x) j) +
        (φ x * coordinateDerivative χ hχ i x) * (u x) j := by
    rw [coordinateDerivative_mul hφ hχ]
    ring
  simp_rw [hpoint] at hscalar
  rw [integral_add hAI hBI] at hscalar
  convert hscalar using 1
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by dsimp only [ψ]; ring

/-- Matching actual continuous native radial trace classes yield the actual
distributional weak gradient of the literal original piecewise map. -/
theorem hasWeakGradient_radial_piecewise_of_matching_native_traces {n q : ℕ}
    (hn : 2 ≤ n) (c : Domain n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u w : Domain n → Ambient q) (Du Dw : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain c r) u Du)
    (hw : MemW12 ⟨{x | r < ‖x - c‖ ∧ ‖x - c‖ < R},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ w Dw) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let a := r / 2
    let b := (r + R) / 2
    ∀ (H : C(Icc a r, Lp (Ambient q) 2 σ)) (K : C(Icc r b, Lp (Ambient q) 2 σ)),
      (∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo a r,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + s • θ.val)) 2 σ,
          H ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + s • θ.val))) →
      (∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo r b,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => w (c + s • θ.val)) 2 σ,
          K ⟨s, hs.1.le, hs.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => w (c + s • θ.val))) →
      H ⟨r, by dsimp only [a]; linarith only [hr], le_rfl⟩ =
        K ⟨r, le_rfl, by dsimp only [b]; linarith only [hrR]⟩ →
      HasWeakGradient (ballDomain c R)
        (fun x => if ‖x - c‖ < r then u x else w x)
        (fun x i => if ‖x - c‖ < r then Du x i else Dw x i) := by
  intro σ a b H K hH hK hmatch
  have hnpos : 0 < n := by omega
  have har : a < r := by dsimp only [a]; linarith only [hr]
  have hrb : r < b := by dsimp only [b]; linarith only [hrR]
  have hbR : b < R := by dsimp only [b]; linarith only [hrR]
  let Ωu : OpenDomain n := ballDomain c r
  let Ωw : OpenDomain n := ⟨{x | r < ‖x - c‖ ∧ ‖x - c‖ < R},
    isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩
  have hfiniteu : (volume : Measure (Domain n)) Ωu.val ≠ ⊤ := measure_ball_ne_top
  have hfinitew : (volume : Measure (Domain n)) Ωw.val ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_ne_top
      (measure_mono fun x hx => mem_ball_iff_norm.mpr hx.2)
  letI : IsFiniteMeasure (volume.restrict Ωu.val) := isFiniteMeasure_restrict.mpr hfiniteu
  letI : IsFiniteMeasure (volume.restrict Ωw.val) := isFiniteMeasure_restrict.mpr hfinitew
  letI : IsFiniteMeasure (volume.restrict (ball c R)) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let f : Domain n → Ambient q := fun x => if ‖x - c‖ < r then u x else w x
  let Df : Domain n → Gradient n q := fun x i => if ‖x - c‖ < r then Du x i else Dw x i
  obtain ⟨hfL, hDfL, _hEnergy⟩ := radial_piecewise_sobolev_L2_energy c hr hrR u w Du Dw hu hw
  have hfI : IntegrableOn f (ball c R) := hfL.integrable (by norm_num)
  have hDfI (i : Fin n) : IntegrableOn (fun x => Df x i) (ball c R) :=
    (hDfL i).integrable (by norm_num)
  let d : ℝ := min (r / 8) ((R - r) / 8)
  have hd : 0 < d := lt_min (by linarith only [hr]) (by linarith only [hrR])
  let ε : ℕ → PositiveRadius := fun k => ⟨d / ((k : ℝ) + 1), by positivity⟩
  have hεle (k : ℕ) : (ε k).val ≤ d := by
    exact div_le_self hd.le (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hεr (k : ℕ) : (ε k).val ≤ r / 8 := (hεle k).trans (min_le_left _ _)
  have hεR (k : ℕ) : (ε k).val ≤ (R - r) / 8 := (hεle k).trans (min_le_right _ _)
  have hεlim : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [ε, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d
  let tu : ℕ → PositiveRadius := fun k => ⟨r - 2 * (ε k).val, by linarith [hεr k]⟩
  let tw : ℕ → PositiveRadius := fun k => ⟨r + (ε k).val, by linarith [(ε k).property]⟩
  have htulim : Tendsto (fun k => (tu k).val) atTop (𝓝 r) := by
    simpa only [tu, mul_zero, sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hεlim)
  have htwlim : Tendsto (fun k => (tw k).val) atTop (𝓝 r) := by
    simpa only [tw, add_zero] using tendsto_const_nhds.add hεlim
  let χu : ℕ → Domain n → ℝ := fun k x => radialCutoffProfile (tu k) (ε k) ‖x - c‖
  let χw : ℕ → Domain n → ℝ := fun k x => 1 - radialCutoffProfile (tw k) (ε k) ‖x - c‖
  have hχu (k : ℕ) : ContDiff ℝ ∞ (χu k) := radialCutoffScalar_contDiff (tu k) (ε k) c
  have hχw (k : ℕ) : ContDiff ℝ ∞ (χw k) :=
    contDiff_const.sub (radialCutoffScalar_contDiff (tw k) (ε k) c)
  have hχub (k : ℕ) : ∀ᵐ x ∂volume.restrict Ωu.val, |χu k x| ≤ 1 := by
    apply ae_of_all
    intro x
    exact abs_le.mpr ⟨by linarith [(radialCutoffProfile_mem_Icc (tu k) (ε k) ‖x - c‖).1],
      (radialCutoffProfile_mem_Icc (tu k) (ε k) ‖x - c‖).2⟩
  have hχwb (k : ℕ) : ∀ᵐ x ∂volume.restrict Ωw.val, |χw k x| ≤ 1 := by
    apply ae_of_all
    intro x
    have hv := radialCutoffProfile_mem_Icc (tw k) (ε k) ‖x - c‖
    exact abs_le.mpr ⟨by dsimp only [χw]; linarith [hv.2], by dsimp only [χw]; linarith [hv.1]⟩
  have hχulim : ∀ᵐ x ∂volume.restrict Ωu.val,
      Tendsto (fun k => χu k x) atTop (𝓝 (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem Ωu.property.measurableSet] with x hx
    have hxnorm : ‖x - c‖ < r := mem_ball_iff_norm.mp hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hεlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < (r - ‖x - c‖) / 2))] with k hk
    exact (radialCutoffProfile_eq_one (tu k) (ε k) (by change ‖x - c‖ ≤ r - 2 * (ε k).val; linarith)).symm
  have hχwlim : ∀ᵐ x ∂volume.restrict Ωw.val,
      Tendsto (fun k => χw k x) atTop (𝓝 (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem Ωw.property.measurableSet] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hεlim.eventually (Iio_mem_nhds (by linarith [hx.1] : (0 : ℝ) < (‖x - c‖ - r) / 2))] with k hk
    change 1 = 1 - radialCutoffProfile (tw k) (ε k) ‖x - c‖
    rw [radialCutoffProfile_eq_zero (tw k) (ε k) (by change r + (ε k).val + (ε k).val ≤ ‖x - c‖; linarith), sub_zero]
  refine ⟨hfI.locallyIntegrableOn, fun i => (hDfI i).locallyIntegrableOn, ?_⟩
  intro i φ hφ hcφ hsφ
  have hφu : MemLp φ ∞ (volume.restrict Ωu.val) := hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hφw : MemLp φ ∞ (volume.restrict Ωw.val) := hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hdφu : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict Ωu.val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have hdφw : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict Ωw.val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have htestu (k : ℕ) : tsupport (fun x => φ x * χu k x) ⊆ Ωu.val :=
    tsupport_mul_subset_right.trans
      ((radialCutoffScalar_tsupport_subset_closedBall (tu k) (ε k) c).trans
        (closedBall_subset_ball (by change r - 2 * (ε k).val + (ε k).val < r; linarith [(ε k).property])))
  have htestw (k : ℕ) : tsupport (fun x => φ x * χw k x) ⊆ Ωw.val := by
    intro x hx
    have hlo := one_sub_radialCutoffScalar_tsupport_subset (tw k) (ε k) c
      (tsupport_mul_subset_right hx)
    have hhi := mem_ball_iff_norm.mp (hsφ (tsupport_mul_subset_left hx))
    exact ⟨by change r + (ε k).val ≤ ‖x - c‖ at hlo; linarith [(ε k).property], hhi⟩
  have hbandu (k : ℕ) :
      {x : Domain n | (tu k).val ≤ ‖x - c‖ ∧ ‖x - c‖ ≤ (tu k).val + (ε k).val} ⊆ Ωu.val := by
    intro x hx
    apply mem_ball_iff_norm.mpr
    change r - 2 * (ε k).val ≤ ‖x - c‖ ∧ ‖x - c‖ ≤ r - 2 * (ε k).val + (ε k).val at hx
    linarith [hx.2, (ε k).property]
  have hbandw (k : ℕ) :
      {x : Domain n | (tw k).val ≤ ‖x - c‖ ∧ ‖x - c‖ ≤ (tw k).val + (ε k).val} ⊆ Ωw.val := by
    intro x hx
    change r + (ε k).val ≤ ‖x - c‖ ∧ ‖x - c‖ ≤ r + (ε k).val + (ε k).val at hx
    exact ⟨by linarith [(ε k).property, hx.1], by linarith [hεR k, hx.2]⟩
  have hφR : MemLp φ ∞ (volume.restrict (ball c R)) := hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hdφR : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict (ball c R)) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have hleftI : IntegrableOn (fun x => coordinateDerivative φ hφ i x • f x) (ball c R) :=
    hfI.smul_of_top_right hdφR
  have hrightI : IntegrableOn (fun x => φ x • Df x i) (ball c R) :=
    (hDfI i).smul_of_top_right hφR
  ext j
  have huj : IntegrableOn (fun x => (u x) j) Ωu.val :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp (hu.2.1.integrable (by norm_num))
  have hwj : IntegrableOn (fun x => (w x) j) Ωw.val :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp (hw.2.1.integrable (by norm_num))
  have hDuj : IntegrableOn (fun x => (Du x i) j) Ωu.val :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp ((hu.2.2 i).integrable (by norm_num))
  have hDwj : IntegrableOn (fun x => (Dw x i) j) Ωw.val :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp ((hw.2.2 i).integrable (by norm_num))
  have hAu : IntegrableOn (fun x => coordinateDerivative φ hφ i x * (u x) j) Ωu.val :=
    huj.smul_of_top_right hdφu
  have hAw : IntegrableOn (fun x => coordinateDerivative φ hφ i x * (w x) j) Ωw.val :=
    hwj.smul_of_top_right hdφw
  have hCu : IntegrableOn (fun x => φ x * (Du x i) j) Ωu.val :=
    hDuj.smul_of_top_right hφu
  have hCw : IntegrableOn (fun x => φ x * (Dw x i) j) Ωw.val :=
    hDwj.smul_of_top_right hφw
  have hAulim := tendsto_integral_bounded_multiplier hAu χu
    (fun k => (hχu k).continuous.aestronglyMeasurable) hχub hχulim
  have hAwlim := tendsto_integral_bounded_multiplier hAw χw
    (fun k => (hχw k).continuous.aestronglyMeasurable) hχwb hχwlim
  have hCulim := tendsto_integral_bounded_multiplier hCu χu
    (fun k => (hχu k).continuous.aestronglyMeasurable) hχub hχulim
  have hCwlim := tendsto_integral_bounded_multiplier hCw χw
    (fun k => (hχw k).continuous.aestronglyMeasurable) hχwb hχwlim
  obtain ⟨Ju, hJu, hJuRaw⟩ := exists_continuous_radial_flux_of_raw_trace hnpos c u H hH φ hφ.continuous i j
  obtain ⟨Jw, hJw, hJwRaw⟩ := exists_continuous_radial_flux_of_raw_trace hnpos c w K hK φ hφ.continuous i j
  let Eu : ℝ → ℝ := fun s => Ju (projIcc a r har.le s)
  let Ew : ℝ → ℝ := fun s => Jw (projIcc r b hrb.le s)
  have hEu : Continuous Eu := Ju.continuous.comp continuous_projIcc
  have hEw : Continuous Ew := Jw.continuous.comp continuous_projIcc
  have hEr : Eu r = Ew r := by
    dsimp only [Eu, Ew]
    rw [projIcc_of_mem har.le ⟨har.le, le_rfl⟩, projIcc_of_mem hrb.le ⟨le_rfl, hrb.le⟩,
      hJu, hJw, hmatch]
  have hBu (k : ℕ) :
      (∫ x in Ωu.val, (φ x * coordinateDerivative (χu k) (hχu k) i x) * (u x) j) =
        ∫ s in (tu k).val..((tu k).val + (ε k).val),
          deriv (radialCutoffProfile (tu k) (ε k)) s * Eu s := by
    apply integral_radial_cutoff_eq_flux hnpos Ωu c u
      (hu.2.1.integrable (by norm_num)) φ hφ.continuous hcφ i j (tu k) (ε k) (hbandu k) Eu
    filter_upwards [hJuRaw] with s hs hsband
    have hsar : s ∈ Ioo a r := by
      dsimp only [tu] at hsband
      dsimp only [a]
      constructor <;> linarith [hsband.1, hsband.2, hεr k, (ε k).property]
    dsimp only [Eu]
    rw [projIcc_of_mem har.le ⟨hsar.1.le, hsar.2.le⟩]
    exact (hs hsar).2
  have hBw (k : ℕ) :
      (∫ x in Ωw.val, (φ x * coordinateDerivative (χw k) (hχw k) i x) * (w x) j) =
        -(∫ s in (tw k).val..((tw k).val + (ε k).val),
          deriv (radialCutoffProfile (tw k) (ε k)) s * Ew s) := by
    have hraw := integral_radial_cutoff_eq_flux hnpos Ωw c w
      (hw.2.1.integrable (by norm_num)) φ hφ.continuous hcφ i j (tw k) (ε k) (hbandw k) Ew
    have hJraw : ∀ᵐ s : ℝ ∂volume, s ∈ Icc (tw k).val ((tw k).val + (ε k).val) →
        Ew s = s ^ (n - 1) * ∫ θ : sphere (0 : Domain n) 1,
          (w (c + s • θ.val)) j * φ (c + s • θ.val) * θ.val i
            ∂Measure.euclideanHausdorffMeasure (n - 1) := by
      filter_upwards [hJwRaw] with s hs hsband
      have hsrb : s ∈ Ioo r b := by
        dsimp only [tw] at hsband
        dsimp only [b]
        constructor <;> linarith [hsband.1, hsband.2, hεR k, (ε k).property]
      dsimp only [Ew]
      rw [projIcc_of_mem hrb.le ⟨hsrb.1.le, hsrb.2.le⟩]
      exact (hs hsrb).2
    rw [← hraw hJraw, ← integral_neg]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change (φ x * coordinateDerivative (fun y => 1 - radialCutoffProfile (tw k) (ε k) ‖y - c‖)
      (hχw k) i x) * (w x) j = _
    simp only [coordinateDerivative, fderiv_const_sub, neg_apply]
    ring
  have hBulim := (tendsto_radialCutoff_derivative_integral_of_continuous tu ε htulim hεlim Eu hEu).congr'
    (Eventually.of_forall fun k => (hBu k).symm)
  have hBwlim := ((tendsto_radialCutoff_derivative_integral_of_continuous tw ε htwlim hεlim Ew hEw).neg).congr'
    (Eventually.of_forall fun k => (hBw k).symm)
  have hId (k : ℕ) := (weak_gradient_mul_cutoff_scalar Ωu u Du hu hfiniteu φ (χu k) hφ (hχu k)
    hcφ (htestu k) i j)
  have hIw (k : ℕ) := weak_gradient_mul_cutoff_scalar Ωw w Dw hw hfinitew φ (χw k) hφ (hχw k)
    hcφ (htestw k) i j
  have hsumId (k : ℕ) := congrArg₂ (fun x y : ℝ => x + y) (hId k) (hIw k)
  have hleftlim := (hAulim.add hBulim).add (hAwlim.add hBwlim)
  have hrightlim := hCulim.neg.add hCwlim.neg
  have hsum := tendsto_nhds_unique hleftlim (hrightlim.congr' (Eventually.of_forall fun k => (hsumId k).symm))
  have hscalar :
      (∫ x in Ωu.val, coordinateDerivative φ hφ i x * (u x) j) +
        (∫ x in Ωw.val, coordinateDerivative φ hφ i x * (w x) j) =
      -((∫ x in Ωu.val, φ x * (Du x i) j) + (∫ x in Ωw.val, φ x * (Dw x i) j)) := by
    rw [neg_neg, ← hEr] at hsum
    linarith only [hsum]
  have hsplitLeft := integral_radial_piecewise c hr hrR
    (fun x => coordinateDerivative φ hφ i x * (u x) j)
    (fun x => coordinateDerivative φ hφ i x * (w x) j) hAu hAw
  have hsplitRight := integral_radial_piecewise c hr hrR
    (fun x => φ x * (Du x i) j) (fun x => φ x * (Dw x i) j) hCu hCw
  have hleftProj := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hleftI
  have hrightProj := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hrightI
  change (∫ x in ball c R, coordinateDerivative φ hφ i x * (f x) j) =
    (∫ x in ball c R, coordinateDerivative φ hφ i x • f x) j at hleftProj
  change (∫ x in ball c R, φ x * Df x i j) =
    (∫ x in ball c R, φ x • Df x i) j at hrightProj
  change (∫ x in ball c R, coordinateDerivative φ hφ i x • f x) j =
    -(∫ x in ball c R, φ x • Df x i) j
  rw [← hleftProj, ← hrightProj]
  have hleftPoint (x : Domain n) : coordinateDerivative φ hφ i x * (f x) j =
      if ‖x - c‖ < r then coordinateDerivative φ hφ i x * (u x) j
        else coordinateDerivative φ hφ i x * (w x) j := by dsimp only [f]; split_ifs <;> rfl
  have hrightPoint (x : Domain n) : φ x * Df x i j =
      if ‖x - c‖ < r then φ x * (Du x i) j else φ x * (Dw x i) j := by dsimp only [Df]; split_ifs <;> rfl
  simp_rw [hleftPoint, hrightPoint]
  rw [hsplitLeft, hsplitRight]
  exact hscalar

end StratificationTheory
