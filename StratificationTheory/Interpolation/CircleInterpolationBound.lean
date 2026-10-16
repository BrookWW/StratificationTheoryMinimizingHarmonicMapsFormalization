module

public import StratificationTheory.Foundation.SphereCircleWeakData
public import StratificationTheory.Foundation.IntervalInterpolationBound

/-!
# Native almost-everywhere interpolation bound on the circle

The actual interval weak data of two sphere Sobolev maps subtract. Their
common interval representative gives a uniform bound, which transfers back
to the original native circle classes using measurable representatives.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

private theorem integrable_interval_compact_test_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ioo a b) :
    Integrable (fun t => ψ t • f t) volume := by
  have hi : IntegrableOn (fun t => ψ t • f t) (Ioo a b) :=
    (hf.integrable (by norm_num)).smul_of_top_right
      (hψ.memLp_top_of_hasCompactSupport hcψ _)
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro t ht
  apply hsψ
  apply subset_tsupport ψ
  intro hz
  exact ht (by simp only [hz, zero_smul])

private theorem norm_sub_sq_le_twice {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  calc
    ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖x‖ - ‖y‖)]

private theorem ae_bound_of_comp_measurePreserving {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {p : X → Y} (hp : MeasurePreserving p μ ν) {f : Y → ℝ}
    (hf : AEStronglyMeasurable f ν) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, f (p x) ≤ C) : ∀ᵐ y ∂ν, f y ≤ C := by
  let F := hf.mk f
  have hFmeas : Measurable F := hf.stronglyMeasurable_mk.measurable
  have hFcomp : ∀ᵐ x ∂μ, F (p x) ≤ C := by
    filter_upwards [hp.quasiMeasurePreserving.ae hf.ae_eq_mk, hbound] with x hx hb
    change hf.mk f (p x) ≤ C
    rw [← hx]
    exact hb
  have hFnative : ∀ᵐ y ∂ν, F y ≤ C := by
    rw [← hp.map_eq]
    exact (ae_map_iff hp.aemeasurable (measurableSet_le hFmeas measurable_const)).mpr hFcomp
  filter_upwards [hf.ae_eq_mk, hFnative] with y hy hb
  calc
    f y = F y := hy
    _ ≤ C := hb

private theorem circle_GN_constants {D A B X : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hB : B ≤ 2 * A)
    (hX : X ≤ (4 / (Real.pi - -Real.pi)) * D + 4 * Real.sqrt (D * B)) :
    X ≤ 8 * Real.sqrt (A * D) + 8 * D := by
  have hlen : 0 < Real.pi - -Real.pi := by linarith only [Real.pi_pos]
  have hc : 4 / (Real.pi - -Real.pi) ≤ 8 :=
    (div_le_iff₀ hlen).mpr (by linarith only [Real.two_le_pi])
  have hfirst := mul_le_mul_of_nonneg_right hc hD
  have hprod : D * B ≤ 2 * (A * D) := by
    have h := mul_le_mul_of_nonneg_left hB hD
    nlinarith only [h]
  have hsquare := Real.sq_sqrt (mul_nonneg hA hD)
  have hroot : Real.sqrt (D * B) ≤ 2 * Real.sqrt (A * D) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
    nlinarith only [hprod, hsquare, mul_nonneg hA hD]
  linarith only [hX, hfirst, hroot]

/-- Two genuine circle Sobolev maps satisfy a uniform native-a.e. bound for
their raw difference. The energies use their original named sphere-gradient
classes, and the universal constant is independent of the target dimension. -/
theorem circle_sobolev_difference_interpolation_bound {q : ℕ}
    (u v : sphere (0 : Domain 2) 1 → Ambient q)
    (hu : MemSphereW12 (Nat.le_refl 2) u) (hv : MemSphereW12 (Nat.le_refl 2) v) :
    let σ : Measure (sphere (0 : Domain 2) 1) := Measure.euclideanHausdorffMeasure 1
    let A := ∫ θ : sphere (0 : Domain 2) 1,
      ∑ i : Fin 2, (‖(sphereGradient (Nat.le_refl 2) u hu i) θ‖ ^ 2 +
        ‖(sphereGradient (Nat.le_refl 2) v hv i) θ‖ ^ 2) ∂σ
    let D := ∫ θ : sphere (0 : Domain 2) 1, ‖u θ - v θ‖ ^ 2 ∂σ
    ∀ᵐ θ ∂σ, ‖u θ - v θ‖ ^ 2 ≤ 8 * Real.sqrt (A * D) + 8 * D := by
  intro σ A D
  let ν : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  let τ : ℝ → Domain 2 := fun t => WithLp.toLp 2 ![-Real.sin t, Real.cos t]
  let fu : ℝ → Ambient q := fun t => u (circleNativeParam t)
  let fv : ℝ → Ambient q := fun t => v (circleNativeParam t)
  let gu : ℝ → Ambient q := fun t => ∑ i : Fin 2,
    τ t i • (sphereGradient (Nat.le_refl 2) u hu i) (circleNativeParam t)
  let gv : ℝ → Ambient q := fun t => ∑ i : Fin 2,
    τ t i • (sphereGradient (Nat.le_refl 2) v hv i) (circleNativeParam t)
  obtain ⟨hfu, hgu, hwu, hEu⟩ := sphere_circle_weak_data u hu
  obtain ⟨hfv, hgv, hwv, hEv⟩ := sphere_circle_weak_data v hv
  have hweak : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (-Real.pi) Real.pi →
      (∫ t, deriv φ t • (fu - fv) t) = -(∫ t, φ t • (gu - gv) t) := by
    intro φ hφ hcφ hsφ
    have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    have hcdφ : HasCompactSupport (deriv φ) := hcφ.deriv
    have hsdφ : tsupport (deriv φ) ⊆ Ioo (-Real.pi) Real.pi := tsupport_deriv_subset.trans hsφ
    have huTest := integrable_interval_compact_test_smul hfu hdφ hcdφ hsdφ
    have hvTest := integrable_interval_compact_test_smul hfv hdφ hcdφ hsdφ
    have hguTest := integrable_interval_compact_test_smul hgu hφ.continuous hcφ hsφ
    have hgvTest := integrable_interval_compact_test_smul hgv hφ.continuous hcφ hsφ
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub huTest hvTest, integral_sub hguTest hgvTest,
      hwu φ hφ hcφ hsφ, hwv φ hφ hcφ hsφ]
    abel
  have hAu : Integrable (fun θ : sphere (0 : Domain 2) 1 =>
      ∑ i : Fin 2, ‖(sphereGradient (Nat.le_refl 2) u hu i) θ‖ ^ 2) σ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      (Lp.memLp (sphereGradient (Nat.le_refl 2) u hu i)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hAv : Integrable (fun θ : sphere (0 : Domain 2) 1 =>
      ∑ i : Fin 2, ‖(sphereGradient (Nat.le_refl 2) v hv i) θ‖ ^ 2) σ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      (Lp.memLp (sphereGradient (Nat.le_refl 2) v hv i)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hAeq : A = (∫ θ : sphere (0 : Domain 2) 1,
      ∑ i : Fin 2, ‖(sphereGradient (Nat.le_refl 2) u hu i) θ‖ ^ 2 ∂σ) +
      (∫ θ : sphere (0 : Domain 2) 1,
        ∑ i : Fin 2, ‖(sphereGradient (Nat.le_refl 2) v hv i) θ‖ ^ 2 ∂σ) := by
    dsimp only [A]
    simp_rw [Finset.sum_add_distrib]
    exact integral_add hAu hAv
  have hgu2 : Integrable (fun t => ‖gu t‖ ^ 2) ν := hgu.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hgv2 : Integrable (fun t => ‖gv t‖ ^ 2) ν := hgv.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hB : (∫ t, ‖(gu - gv) t‖ ^ 2 ∂ν) ≤ 2 * A := by
    have hmono := integral_mono ((hgu.sub hgv).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      ((hgu2.const_mul 2).add (hgv2.const_mul 2)) (fun t => norm_sub_sq_le_twice (gu t) (gv t))
    change (∫ t, ‖gu t - gv t‖ ^ 2 ∂ν) ≤ ∫ t, 2 * ‖gu t‖ ^ 2 + 2 * ‖gv t‖ ^ 2 ∂ν at hmono
    rw [integral_add (hgu2.const_mul 2) (hgv2.const_mul 2), integral_const_mul, integral_const_mul] at hmono
    rw [hAeq]
    have hh := hmono.trans (add_le_add
      (mul_le_mul_of_nonneg_left hEu (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hEv (by norm_num : (0 : ℝ) ≤ 2)))
    convert hh using 1
    · rfl
    · rfl
    · simp only [σ, mul_add]
  have hMP : MeasurePreserving circleNativeParam ν σ :=
    ⟨continuous_circleNativeParam.measurable, map_circleNativeParam_Ioo_eq_native⟩
  have hDnative : Integrable (fun θ : sphere (0 : Domain 2) 1 => ‖u θ - v θ‖ ^ 2) σ :=
    (hu.1.sub hv.1).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hDint : (∫ t, ‖(fu - fv) t‖ ^ 2 ∂ν) = D := by
    have heq := integral_map hMP.aemeasurable (hMP.map_eq.symm ▸ hDnative.aestronglyMeasurable)
    rw [hMP.map_eq] at heq
    exact heq.symm
  have hApos : 0 ≤ A := integral_nonneg (fun θ => Finset.sum_nonneg (fun i _ =>
    add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hDpos : 0 ≤ D := integral_nonneg (fun θ => sq_nonneg ‖u θ - v θ‖)
  have hpi : -Real.pi < Real.pi := by linarith only [Real.pi_pos]
  obtain ⟨F, hF, _hUnique⟩ :=
    banach_interval_weakDerivative_exists_unique_interpolation_representative hpi
      (hfu.sub hfv) (hgu.sub hgv) hweak
  have hFbound (t : Icc (-Real.pi) Real.pi) : ‖F t‖ ^ 2 ≤ 8 * Real.sqrt (A * D) + 8 * D := by
    have hb := hF.2.2.2.2 t
    rw [hDint] at hb
    exact circle_GN_constants hDpos hApos hB hb
  have hraw : ∀ᵐ t ∂ν, ‖u (circleNativeParam t) - v (circleNativeParam t)‖ ^ 2 ≤
      8 * Real.sqrt (A * D) + 8 * D := by
    filter_upwards [ae_restrict_of_ae hF.1, ae_restrict_mem measurableSet_Ioo] with t ht htI
    have hb := hFbound ⟨t, htI.1.le, htI.2.le⟩
    rw [ht htI] at hb
    exact hb
  exact ae_bound_of_comp_measurePreserving hMP hDnative.aestronglyMeasurable hraw

end StratificationTheory
