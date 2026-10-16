module

public import StratificationTheory.Foundation.CircleNativeMeasure
public import StratificationTheory.Frozen.SphereGradientCharacterization
import StratificationTheory.Foundation.SphereInteriorCutoff
import StratificationTheory.Foundation.CompactSobolevCutoff
import StratificationTheory.Foundation.SobolevAngularApproximation
import StratificationTheory.Foundation.RadialL2Transfer
import HarmonicMaps.Analysis.RadialIntegrability
import HarmonicMaps.Analysis.SobolevCutoffBoundary
import StratificationTheory.Foundation.IntervalWeakDerivativeClosure
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Actual weak data along the native unit circle

Coherent radial sphere Sobolev data yield one smooth angular graph
approximation with the original named gradient as limit. The classical
unit-circle chain rule and native measure transport give real-interval L2
weak data, with derivative energy bounded by the native sphere energy.
The interval is open at both ends; no endpoint identification is imposed.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff

namespace StratificationTheory

/-- One positive radius and one sequence of genuinely smooth ambient maps
approximate the original circle map and every named sphere-gradient column
in native L2, with the same radius in all columns. -/
theorem exists_smooth_circle_angular_approximation {q : ℕ}
    (u : sphere (0 : Domain 2) 1 → Ambient q) (hu : MemSphereW12 (Nat.le_refl 2) u) :
    let σ : Measure (sphere (0 : Domain 2) 1) := Measure.euclideanHausdorffMeasure 1
    ∃ r : ℝ, 0 < r ∧ ∃ m : ℕ → Domain 2 → Ambient q, ∃ hm : ∀ k, ContDiff ℝ ∞ (m k),
      (∀ k, MemLp (fun θ : sphere (0 : Domain 2) 1 => m k (r • θ.val)) 2 σ ∧
        ∀ i : Fin 2, MemLp (fun θ : sphere (0 : Domain 2) 1 =>
          r • coordinateDerivative (m k) (hm k) i (r • θ.val)) 2 σ) ∧
      Tendsto (fun k => eLpNorm (fun θ : sphere (0 : Domain 2) 1 => m k (r • θ.val) - u θ) 2 σ)
        atTop (𝓝 0) ∧
      ∀ i : Fin 2, Tendsto (fun k => eLpNorm (fun θ : sphere (0 : Domain 2) 1 =>
        r • coordinateDerivative (m k) (hm k) i (r • θ.val) -
          (sphereGradient (Nat.le_refl 2) u hu i) θ) 2 σ) atTop (𝓝 0) := by
  intro σ
  obtain ⟨w, D, hw, hraw, hscale⟩ := (sphereGradient_characterization (Nat.le_refl 2) u hu).1.1
  obtain ⟨χ, hχ, hcχ, _hχbounds, hχsupport, hχone, hχzero⟩ :=
    exists_sphere_interior_cutoff (n := 2) (δ := 1 / 4) (by norm_num) (by norm_num)
  have hsχ : tsupport χ ⊆ ({0}ᶜ : Set (Domain 2)) := by
    intro x hx
    change x ≠ 0
    intro hx0
    have hlo := (hχsupport hx).1
    rw [hx0, norm_zero] at hlo
    norm_num at hlo
  let wχ : Domain 2 → Ambient q := fun x => χ x • w x
  let Dχ : Domain 2 → Gradient 2 q := fun x i =>
    coordinateDerivative χ hχ i x • w x + χ x • D x i
  have hwχ : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain 2) wχ Dχ :=
    hw.smoothCutoff_univ hχ hcχ hsχ
  obtain ⟨m, hm, _hmW, κ, _hκ, hae⟩ := exists_smooth_subseq_ae_angular_graph_approximation
    (by decide : 0 < 2) hwχ.to_memW12Loc (a := (0 : Domain 2)) (R := 2)
      (by norm_num) (subset_univ _)
  have hband : Ioo (7 / 8 : ℝ) (9 / 8) ⊆ Ioo (0 : ℝ) 2 := by
    intro r hr
    constructor <;> linarith only [hr.1, hr.2]
  have hbandpos : (volume : Measure ℝ) (Ioo (7 / 8 : ℝ) (9 / 8)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨r, hr, hdata⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hbandpos
    (hae.filter_mono (ae_mono (Measure.restrict_mono_set volume hband)))
  obtain ⟨_hwLp, _hDLp, hmLp, _herrInt, hconv, hDconv⟩ := hdata
  have hrpos : 0 < r := by linarith only [hr.1]
  have hnorm (θ : sphere (0 : Domain 2) 1) : ‖r • θ.val‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hrpos.le, mem_sphere_zero_iff_norm.mp θ.property, mul_one]
  have hin (θ : sphere (0 : Domain 2) 1) :
      r • θ.val ∈ {x : Domain 2 | 1 - (1 / 4 : ℝ) / 2 < ‖x‖ ∧ ‖x‖ < 1 + (1 / 4 : ℝ) / 2} := by
    change 1 - (1 / 4 : ℝ) / 2 < ‖r • θ.val‖ ∧ ‖r • θ.val‖ < 1 + (1 / 4 : ℝ) / 2
    rw [hnorm]
    norm_num
    exact hr
  have hval (θ : sphere (0 : Domain 2) 1) : wχ (r • θ.val) = u θ := by
    simp only [wχ, hχone _ (hin θ), one_smul]
    exact hraw ⟨r, hrpos⟩ θ
  have hcol (θ : sphere (0 : Domain 2) 1) (i : Fin 2) : Dχ (r • θ.val) i = D (r • θ.val) i := by
    simp only [Dχ, hχzero _ (hin θ) i, hχone _ (hin θ), zero_smul, one_smul, zero_add]
  have hnative : (volume : Measure (Domain 2)).toSphere = σ :=
    (euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)).symm
  simp only [hnative, hval, hcol, zero_add] at hmLp hconv hDconv
  let M : ℕ → Domain 2 → Ambient q := fun k => m (κ k)
  have hM (k : ℕ) : ContDiff ℝ ∞ (M k) := hm (κ k)
  have hML (k : ℕ) : MemLp (fun θ : sphere (0 : Domain 2) 1 => M k (r • θ.val)) 2 σ :=
    (hmLp (κ k)).1
  have hMDL (k : ℕ) (i : Fin 2) : MemLp (fun θ : sphere (0 : Domain 2) 1 =>
      r • coordinateDerivative (M k) (hM k) i (r • θ.val)) 2 σ :=
    ((hmLp (κ k)).2 i).const_smul r
  have hmapconv : Tendsto (fun k => eLpNorm (fun θ : sphere (0 : Domain 2) 1 =>
      M k (r • θ.val) - u θ) 2 σ) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_zero_of_integral_norm_sq (fun k => (hML k).sub hu.1) hconv
  refine ⟨r, hrpos, M, hM, fun k => ⟨hML k, hMDL k⟩, hmapconv, ?_⟩
  intro i
  have hnamed := hscale ⟨r, hrpos⟩ i
  have heq (k : ℕ) :
      (∫ θ : sphere (0 : Domain 2) 1,
        ‖r • coordinateDerivative (M k) (hM k) i (r • θ.val) -
          (sphereGradient (Nat.le_refl 2) u hu i) θ‖ ^ 2 ∂σ) =
      r ^ 2 * ∫ θ : sphere (0 : Domain 2) 1,
        ‖coordinateDerivative (M k) (hM k) i (r • θ.val) - D (r • θ.val) i‖ ^ 2 ∂σ := by
    calc
      _ = ∫ θ : sphere (0 : Domain 2) 1,
          ‖r • (coordinateDerivative (M k) (hM k) i (r • θ.val) - D (r • θ.val) i)‖ ^ 2 ∂σ := by
        apply integral_congr_ae
        filter_upwards [hnamed] with θ hθ
        rw [← hθ, smul_sub]
      _ = _ := by
        simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        exact integral_const_mul _ _
  have hconvI : Tendsto (fun k => ∫ θ : sphere (0 : Domain 2) 1,
      ‖r • coordinateDerivative (M k) (hM k) i (r • θ.val) -
        (sphereGradient (Nat.le_refl 2) u hu i) θ‖ ^ 2 ∂σ) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa only [mul_zero] using (tendsto_const_nhds.mul (hDconv i))
  exact tendsto_eLpNorm_two_zero_of_integral_norm_sq
    (fun k => (hMDL k i).sub (Lp.memLp (sphereGradient (Nat.le_refl 2) u hu i))) hconvI


/-- The literal native circle curve is smooth as an ambient Euclidean curve. -/
theorem contDiff_circleNativeParam_val :
    ContDiff ℝ ∞ (fun t : ℝ => (circleNativeParam t).val) := by
  let c := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
  change ContDiff ℝ ∞ (fun t : ℝ => c ![Real.cos t, Real.sin t])
  apply c.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact Real.contDiff_cos
  · exact Real.contDiff_sin

/-- The actual ambient derivative of the native circle parametrization is
its unit tangent `(-sin t, cos t)`. -/
theorem hasDerivAt_circleNativeParam_val (t : ℝ) :
    HasDerivAt (fun s : ℝ => (circleNativeParam s).val)
      (WithLp.toLp 2 ![-Real.sin t, Real.cos t] : Domain 2) t := by
  let c := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
  have hpi : HasDerivAt (fun s : ℝ => ![Real.cos s, Real.sin s]) ![-Real.sin t, Real.cos t] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos t
    · exact Real.hasDerivAt_sin t
  exact c.hasFDerivAt.comp_hasDerivAt t hpi

private theorem circle_tangent_norm_sq (t : ℝ) :
    ‖(WithLp.toLp 2 ![-Real.sin t, Real.cos t] : Domain 2)‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [Fin.sum_univ_two, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, neg_sq] using Real.sin_sq_add_cos_sq t

private theorem circle_tangent_memLp_top (μ : Measure ℝ) (i : Fin 2) :
    MemLp (fun t : ℝ => (WithLp.toLp 2 ![-Real.sin t, Real.cos t] : Domain 2) i) ∞ μ := by
  fin_cases i
  · change MemLp (fun t : ℝ => -Real.sin t) ∞ μ
    apply memLp_top_of_bound Real.continuous_sin.neg.aestronglyMeasurable 1
    exact Eventually.of_forall fun t => by simpa only [Pi.neg_apply, norm_neg, Real.norm_eq_abs] using Real.abs_sin_le_one t
  · change MemLp Real.cos ∞ μ
    apply memLp_top_of_bound Real.continuous_cos.aestronglyMeasurable 1
    exact Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one t

private theorem hasDerivAt_smooth_circle_composition {q : ℕ}
    {m : Domain 2 → Ambient q} (hm : ContDiff ℝ ∞ m) (r t : ℝ) :
    HasDerivAt (fun s : ℝ => m (r • (circleNativeParam s).val))
      (∑ i : Fin 2, (WithLp.toLp 2 ![-Real.sin t, Real.cos t] : Domain 2) i •
        (r • coordinateDerivative m hm i (r • (circleNativeParam t).val))) t := by
  let τ : Domain 2 := WithLp.toLp 2 ![-Real.sin t, Real.cos t]
  have hd : HasDerivAt (fun s : ℝ => m (r • (circleNativeParam s).val))
      (fderiv ℝ m (r • (circleNativeParam t).val) (r • τ)) t :=
    ((hm.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_circleNativeParam_val t).const_smul r)
  have heq : fderiv ℝ m (r • (circleNativeParam t).val) (r • τ) =
      ∑ i : Fin 2, τ i • (r • coordinateDerivative m hm i (r • (circleNativeParam t).val)) := by
    rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr (r • τ)]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      PiLp.smul_apply, smul_eq_mul, mul_smul, coordinateDerivative]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm r (τ i) _
  rwa [heq] at hd

private theorem smooth_circle_weak_identity {q : ℕ} {m : Domain 2 → Ambient q}
    (hm : ContDiff ℝ ∞ m) (r : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ t, deriv φ t • m (r • (circleNativeParam t).val)) =
      -(∫ t, φ t • (∑ i : Fin 2,
        (WithLp.toLp 2 ![-Real.sin t, Real.cos t] : Domain 2) i •
          (r • coordinateDerivative m hm i (r • (circleNativeParam t).val)))) := by
  let F : ℝ → Ambient q := fun t => m (r • (circleNativeParam t).val)
  let G : ℝ → Ambient q := fun t => ∑ i : Fin 2,
    (WithLp.toLp 2 ![-Real.sin t, Real.cos t] : Domain 2) i •
      (r • coordinateDerivative m hm i (r • (circleNativeParam t).val))
  have hF : ContDiff ℝ ∞ F := hm.comp (contDiff_circleNativeParam_val.const_smul r)
  have hder : ∀ t, HasDerivAt F (G t) t := fun t => hasDerivAt_smooth_circle_composition hm r t
  have hG : Continuous G := by
    have heq : G = deriv F := funext fun t => (hder t).deriv.symm
    rw [heq]
    exact hF.continuous_deriv (by simp)
  have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hcdφ : HasCompactSupport (deriv φ) := hcφ.deriv
  have hparts := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (u := φ) (u' := deriv φ) (v := F) (v' := G)
    (fun t _ => (hφ.differentiable (by simp) t).hasDerivAt)
    (fun t _ => hder t)
    ((hφ.continuous.smul hG).integrable_of_hasCompactSupport hcφ.smul_right)
    ((hdφ.smul hF.continuous).integrable_of_hasCompactSupport hcdφ.smul_right)
    ((hφ.continuous.smul hF.continuous).integrable_of_hasCompactSupport hcφ.smul_right)
  change (∫ t, deriv φ t • F t) = -(∫ t, φ t • G t)
  simpa only [ContinuousLinearMap.lsmul_apply, neg_neg] using congrArg Neg.neg hparts.symm

private theorem tendsto_eLpNorm_circle_sum {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} {v : Fin 2 → ℕ → ℝ → E}
    (hv : ∀ i k, AEStronglyMeasurable (v i k) μ)
    (hlim : ∀ i, Tendsto (fun k => eLpNorm (v i k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun t => ∑ i, v i k t) 2 μ) atTop (𝓝 0) := by
  have hs : Tendsto (fun k => ∑ i, eLpNorm (v i k) 2 μ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
  intro k
  have heq : (fun t => ∑ i, v i k t) = ∑ i, v i k := by
    funext t
    simp only [Finset.sum_apply]
  dsimp only
  rw [heq]
  exact eLpNorm_sum_le (fun i (_ : i ∈ Finset.univ) => hv i k) (by norm_num : (1 : ℝ≥0∞) ≤ 2)


/-- A genuine circle Sobolev map pulls back to real-interval weak data with
its original named sphere gradient contracted against the unit tangent.
The derivative energy is bounded by the full native sphere-gradient energy. -/
theorem sphere_circle_weak_data {q : ℕ}
    (u : sphere (0 : Domain 2) 1 → Ambient q) (hu : MemSphereW12 (Nat.le_refl 2) u) :
    let G := sphereGradient (Nat.le_refl 2) u hu
    let τ : ℝ → Domain 2 := fun t => WithLp.toLp 2 ![-Real.sin t, Real.cos t]
    let f : ℝ → Ambient q := fun t => u (circleNativeParam t)
    let g : ℝ → Ambient q := fun t => ∑ i : Fin 2, τ t i • (G i) (circleNativeParam t)
    MemLp f 2 (volume.restrict (Ioo (-Real.pi) Real.pi)) ∧
    MemLp g 2 (volume.restrict (Ioo (-Real.pi) Real.pi)) ∧
    (∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (-Real.pi) Real.pi →
      (∫ t, deriv φ t • f t) = -(∫ t, φ t • g t)) ∧
    (∫ t in Ioo (-Real.pi) Real.pi, ‖g t‖ ^ 2) ≤
      ∫ θ : sphere (0 : Domain 2) 1, ∑ i : Fin 2, ‖(G i) θ‖ ^ 2
        ∂Measure.euclideanHausdorffMeasure 1 := by
  intro G τ f g
  let σ : Measure (sphere (0 : Domain 2) 1) := Measure.euclideanHausdorffMeasure 1
  let ν : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  have hMP : MeasurePreserving circleNativeParam ν σ :=
    ⟨continuous_circleNativeParam.measurable, map_circleNativeParam_Ioo_eq_native⟩
  have hτ (i : Fin 2) : MemLp (fun t => τ t i) ∞ ν := circle_tangent_memLp_top ν i
  have hf : MemLp f 2 ν := hu.1.comp_measurePreserving hMP
  have hGi (i : Fin 2) : MemLp (fun t => (G i) (circleNativeParam t)) 2 ν :=
    (Lp.memLp (G i)).comp_measurePreserving hMP
  have hg : MemLp g 2 ν := memLp_finsetSum Finset.univ
    (fun i _ => (hGi i).smul (r := 2) (hτ i))
  obtain ⟨r, _hr, m, hm, hmL, hmconv, hmDconv⟩ := exists_smooth_circle_angular_approximation u hu
  let F : ℕ → ℝ → Ambient q := fun k t => m k (r • (circleNativeParam t).val)
  let B : ℕ → Fin 2 → ℝ → Ambient q := fun k i t =>
    r • coordinateDerivative (m k) (hm k) i (r • (circleNativeParam t).val)
  let H : ℕ → ℝ → Ambient q := fun k t => ∑ i : Fin 2, τ t i • B k i t
  have hFL (k : ℕ) : MemLp (F k) 2 ν := (hmL k).1.comp_measurePreserving hMP
  have hBL (k : ℕ) (i : Fin 2) : MemLp (B k i) 2 ν := ((hmL k).2 i).comp_measurePreserving hMP
  have hHL (k : ℕ) : MemLp (H k) 2 ν := memLp_finsetSum Finset.univ
    (fun i _ => (hBL k i).smul (r := 2) (hτ i))
  have hFNorm (k : ℕ) : eLpNorm (F k - f) 2 ν =
      eLpNorm (fun θ : sphere (0 : Domain 2) 1 => m k (r • θ.val) - u θ) 2 σ := by
    change eLpNorm ((fun θ : sphere (0 : Domain 2) 1 => m k (r • θ.val) - u θ) ∘
      circleNativeParam) 2 ν = _
    exact eLpNorm_comp_measurePreserving ((hmL k).1.sub hu.1).aestronglyMeasurable hMP
  have hFc : Tendsto (fun k => eLpNorm (F k - f) 2 ν) atTop (𝓝 0) := by
    simp_rw [hFNorm]
    exact hmconv
  have hBc (i : Fin 2) : Tendsto (fun k => eLpNorm
      (fun t => B k i t - (G i) (circleNativeParam t)) 2 ν) atTop (𝓝 0) := by
    have heq (k : ℕ) : eLpNorm (fun t => B k i t - (G i) (circleNativeParam t)) 2 ν =
        eLpNorm (fun θ : sphere (0 : Domain 2) 1 =>
          r • coordinateDerivative (m k) (hm k) i (r • θ.val) - (G i) θ) 2 σ := by
      change eLpNorm ((fun θ : sphere (0 : Domain 2) 1 =>
          r • coordinateDerivative (m k) (hm k) i (r • θ.val) - (G i) θ) ∘
          circleNativeParam) 2 ν = _
      exact eLpNorm_comp_measurePreserving (((hmL k).2 i).sub (Lp.memLp (G i))).aestronglyMeasurable hMP
    simp_rw [heq]
    exact hmDconv i
  let V : Fin 2 → ℕ → ℝ → Ambient q := fun i k t =>
    τ t i • (B k i t - (G i) (circleNativeParam t))
  have hVL (i : Fin 2) (k : ℕ) : MemLp (V i k) 2 ν :=
    ((hBL k i).sub (hGi i)).smul (r := 2) (hτ i)
  have hVc (i : Fin 2) : Tendsto (fun k => eLpNorm (V i k) 2 ν) atTop (𝓝 0) :=
    tendsto_eLpNorm_smul_of_top (hτ i)
      (fun k => ((hBL k i).sub (hGi i)).aestronglyMeasurable) (hBc i)
  have hHc : Tendsto (fun k => eLpNorm (H k - g) 2 ν) atTop (𝓝 0) := by
    have heq (k : ℕ) : H k - g = fun t => ∑ i : Fin 2, V i k t := by
      funext t
      simp only [H, g, V, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
    simp_rw [heq]
    exact tendsto_eLpNorm_circle_sum (fun i k => (hVL i k).aestronglyMeasurable) hVc
  have hweak : ∀ k (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (-Real.pi) Real.pi →
      (∫ t, deriv φ t • F k t) = -(∫ t, φ t • H k t) := by
    intro k φ hφ hcφ _hsφ
    exact smooth_circle_weak_identity (hm k) r hφ hcφ
  have hlimit := interval_weakDerivative_of_L2_convergence hFL hHL hf hg hFc hHc hweak
  refine ⟨hf, hg, hlimit, ?_⟩
  have hEI : Integrable (fun θ : sphere (0 : Domain 2) 1 => ∑ i : Fin 2, ‖(G i) θ‖ ^ 2) σ :=
    integrable_finsetSum Finset.univ
      (fun i _ => (Lp.memLp (G i)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hEt : Integrable (fun t => ∑ i : Fin 2, ‖(G i) (circleNativeParam t)‖ ^ 2) ν :=
    hMP.integrable_comp_of_integrable hEI
  have hbound (t : ℝ) : ‖g t‖ ^ 2 ≤ ∑ i : Fin 2, ‖(G i) (circleNativeParam t)‖ ^ 2 := by
    have h := norm_sq_sum_gradient_le (fun i => (G i) (circleNativeParam t)) (τ t)
    rw [circle_tangent_norm_sq, one_mul] at h
    exact h
  have hmono := integral_mono (hg.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) hEt hbound
  have hmap := integral_map hMP.aemeasurable (hMP.map_eq.symm ▸ hEI.aestronglyMeasurable)
  rw [hMP.map_eq] at hmap
  exact hmono.trans_eq hmap.symm

end StratificationTheory
