module

public import StratificationTheory.Foundation.HigherDimensionalRadialL2
public import HarmonicMaps.SobolevRestriction
import StratificationTheory.Interpolation.RadialCutoffConstruction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removal of the center from a radial weak-gradient identity

An integrable reciprocal-radius multiple of the map controls the error from
shrinking smooth tests around the origin. The original weak-gradient witness
is retained.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff

namespace StratificationTheory

private theorem exists_puncture_cutoffs {n : ℕ} :
    ∃ χ : ℕ → Domain n → ℝ, ∃ hχ : ∀ k, ContDiff ℝ ∞ (χ k),
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧
      (∀ k, tsupport (χ k) ⊆ closedBall (0 : Domain n) (2 / ((k : ℝ) + 1))) ∧
      (∀ (k : ℕ) x, ‖x‖ ≤ 1 / ((k : ℝ) + 1) → χ k x = 1) ∧
      (∀ k x (i : Fin n), |coordinateDerivative (χ k) (hχ k) i x| * ‖x‖ ≤ 4) ∧
      ∀ x : Domain n, x ≠ 0 → ∀ᶠ k in atTop,
        χ k x = 0 ∧ ∀ i : Fin n, coordinateDerivative (χ k) (hχ k) i x = 0 := by
  classical
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp only [δ]; positivity
  have hcut (k : ℕ) := Interpolation.exists_quantitative_radial_cutoff
    (0 : Domain n) (hδ k) (hδ k)
  choose χ hχ hcχ hsχ hvχ honχ hoffχ hDχ hdχ using hcut
  have hs (k : ℕ) : tsupport (χ k) ⊆ closedBall (0 : Domain n) (2 * δ k) := by
    simpa only [two_mul] using hsχ k
  have hzero (k : ℕ) (x : Domain n) (hx : 2 * δ k < ‖x‖) :
      χ k x = 0 ∧ ∀ i : Fin n, coordinateDerivative (χ k) (hχ k) i x = 0 := by
    have hout : x ∉ tsupport (χ k) := by
      intro hm
      exact (not_le.mpr hx) (mem_closedBall_zero_iff.mp (hs k hm))
    refine ⟨image_eq_zero_of_notMem_tsupport hout, fun i => ?_⟩
    change fderiv ℝ (χ k) x (EuclideanSpace.single i 1) = 0
    rw [fderiv_of_notMem_tsupport ℝ hout]
    rfl
  refine ⟨χ, hχ, hvχ, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [δ, mul_one_div] using hs k
  · intro k x hx
    exact honχ k x (mem_closedBall_zero_iff.mpr hx)
  · intro k x i
    by_cases hx : ‖x‖ ≤ 2 * δ k
    · calc
        |coordinateDerivative (χ k) (hχ k) i x| * ‖x‖ ≤ (2 / δ k) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (hdχ k x i) (norm_nonneg x)
        _ ≤ (2 / δ k) * (2 * δ k) :=
          mul_le_mul_of_nonneg_left hx (div_nonneg (by norm_num) (hδ k).le)
        _ = 4 := by field_simp [(hδ k).ne']; norm_num
    · rw [(hzero k x (lt_of_not_ge hx)).2 i, abs_zero, zero_mul]
      norm_num
  · intro x hx
    have ht : Tendsto (fun k => 2 * δ k) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using
        tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [ht.eventually (Iio_mem_nhds (norm_pos_iff.mpr hx))] with k hk
    exact hzero k x hk

private theorem tendsto_integral_bounded_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    {f : α → E} (hf : Integrable f μ) {a : ℕ → α → ℝ}
    (ha : ∀ k, AEStronglyMeasurable (a k) μ) {C c : ℝ}
    (hb : ∀ k, ∀ᵐ x ∂μ, |a k x| ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun k => a k x) atTop (𝓝 c)) :
    Tendsto (fun k => ∫ x, a k x • f x ∂μ) atTop (𝓝 (∫ x, c • f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
    (fun k => (ha k).smul hf.aestronglyMeasurable) (hf.norm.const_mul C)
  · intro k
    filter_upwards [hb k] with x hx
    change ‖a k x • f x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  · filter_upwards [ht] with x hx
    exact hx.smul_const (f x)

/-- An integrable reciprocal-radius multiple removes the puncture in the
actual distributional weak-gradient identity on a finite ball. -/
theorem hasWeakGradient_ball_of_punctured_and_integrable_inverse {n q : ℕ}
    (hn : 0 < n) {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    (hP : HasWeakGradient ⟨{(0 : Domain n)}ᶜ, isOpen_compl_singleton⟩ w D)
    {R : ℝ}
    (hw : IntegrableOn w (ball (0 : Domain n) R) volume)
    (hD : ∀ i : Fin n, IntegrableOn (fun x => D x i) (ball (0 : Domain n) R) volume)
    (hinv : IntegrableOn (fun x => ‖x‖⁻¹ • w x) (ball (0 : Domain n) R) volume) :
    HasWeakGradient (ballDomain 0 R) w D := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := volume.restrict (ball (0 : Domain n) R)
  obtain ⟨χ, hχ, hvalues, hsupport, hone, hderiv, hevent⟩ :=
    exists_puncture_cutoffs (n := n)
  refine ⟨hw.locallyIntegrableOn, fun i => (hD i).locallyIntegrableOn, ?_⟩
  intro i φ hφ hcφ hsφ
  have hφL : MemLp φ ∞ μ := hφ.continuous.memLp_top_of_hasCompactSupport hcφ μ
  have hdφL : MemLp (coordinateDerivative φ hφ i) ∞ μ :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) μ
  have hleft : Integrable (fun x => coordinateDerivative φ hφ i x • w x) μ :=
    hw.smul_of_top_right hdφL
  have hright : Integrable (fun x => φ x • D x i) μ :=
    (hD i).smul_of_top_right hφL
  have hae0 : ∀ᵐ x ∂μ, x ≠ 0 := by
    have hnull := measure_eq_zero_iff_ae_notMem.mp
      (measure_singleton (μ := volume) (0 : Domain n))
    simpa only [mem_singleton_iff] using ae_restrict_of_ae hnull (s := ball 0 R)
  have hpoint : ∀ᵐ x ∂μ, ∀ᶠ k in atTop,
      χ k x = 0 ∧ ∀ j : Fin n, coordinateDerivative (χ k) (hχ k) j x = 0 :=
    hae0.mono fun x hx => hevent x hx
  have hmul_lim : ∀ᵐ x ∂μ, Tendsto (fun k => 1 - χ k x) atTop (𝓝 (1 : ℝ)) := by
    filter_upwards [hpoint] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with k hk
    rw [hk.1, sub_zero]
  have hmul_bound (k : ℕ) : ∀ᵐ x ∂μ, |1 - χ k x| ≤ 1 :=
    Eventually.of_forall fun x => by
      rw [abs_of_nonneg (sub_nonneg.mpr (hvalues k x).2)]
      linarith only [(hvalues k x).1]
  have hlimLeft := tendsto_integral_bounded_smul hleft
    (a := fun k x => 1 - χ k x)
    (fun k => (continuous_const.sub (hχ k).continuous).aestronglyMeasurable)
    hmul_bound hmul_lim
  have hlimRight := tendsto_integral_bounded_smul hright
    (a := fun k x => 1 - χ k x)
    (fun k => (continuous_const.sub (hχ k).continuous).aestronglyMeasurable)
    hmul_bound hmul_lim
  obtain ⟨B, hB⟩ := hφ.continuous.norm.bddAbove_range_of_hasCompactSupport hcφ.norm
  have hφB (x : Domain n) : |φ x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB (mem_range_self x)
  let α : ℕ → Domain n → ℝ := fun k x =>
    φ x * coordinateDerivative (χ k) (hχ k) i x * ‖x‖
  have hα (k : ℕ) : AEStronglyMeasurable (α k) μ :=
    ((hφ.continuous.mul
      ((hχ k).continuous_fderiv (by simp) |>.clm_apply continuous_const)).mul
        continuous_norm).aestronglyMeasurable
  have hαbound (k : ℕ) : ∀ᵐ x ∂μ, |α k x| ≤ B * 4 :=
    Eventually.of_forall fun x => by
      dsimp only [α]
      rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg x), mul_assoc]
      exact mul_le_mul (hφB x) (hderiv k x i)
        (mul_nonneg (abs_nonneg _) (norm_nonneg _))
        ((abs_nonneg _).trans (hφB x))
  have hαlim : ∀ᵐ x ∂μ, Tendsto (fun k => α k x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpoint] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with k hk
    simp only [α, hk.2 i, mul_zero, zero_mul]
  have hlimError := tendsto_integral_bounded_smul hinv hα hαbound hαlim
  have herrorEq (k : ℕ) :
      (fun x => α k x • (‖x‖⁻¹ • w x)) =ᵐ[μ]
        (fun x => φ x • (coordinateDerivative (χ k) (hχ k) i x • w x)) := by
    filter_upwards [hae0] with x hx
    simp only [α, smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),
      mul_one]
  have herrorI (k : ℕ) : Integrable
      (fun x => φ x • (coordinateDerivative (χ k) (hχ k) i x • w x)) μ := by
    apply Integrable.congr ?_ (herrorEq k)
    exact hinv.bdd_smul (B * 4) (hα k) (by simpa only [Real.norm_eq_abs] using hαbound k)
  have hχL (k : ℕ) : MemLp (fun x => 1 - χ k x) ∞ μ :=
    memLp_top_of_bound
      (continuous_const.sub (hχ k).continuous).aestronglyMeasurable 1 (hmul_bound k)
  have hId (k : ℕ) :
      (∫ x, (1 - χ k x) • (coordinateDerivative φ hφ i x • w x) ∂μ) -
          (∫ x, φ x • (coordinateDerivative (χ k) (hχ k) i x • w x) ∂μ) =
        -(∫ x, (1 - χ k x) • (φ x • D x i) ∂μ) := by
    let ψ : Domain n → ℝ := fun x => φ x * (1 - χ k x)
    have hψ : ContDiff ℝ ∞ ψ := hφ.mul (contDiff_const.sub (hχ k))
    have hcψ : HasCompactSupport ψ := hcφ.mul_right
    have hsψ : tsupport ψ ⊆ ball (0 : Domain n) R ∩ {(0 : Domain n)}ᶜ := by
      refine subset_inter (tsupport_mul_subset_left.trans hsφ) ?_
      have hz : tsupport ψ ⊆ (ball (0 : Domain n) (1 / ((k : ℝ) + 1)))ᶜ := by
        apply closure_minimal _ isOpen_ball.isClosed_compl
        intro x hx hxball
        have hxnorm : ‖x‖ < 1 / ((k : ℝ) + 1) := mem_ball_zero_iff.mp hxball
        exact hx (by simp only [ψ, hone k x hxnorm.le, sub_self, mul_zero])
      intro x hx hx0
      have heq : x = 0 := mem_singleton_iff.mp hx0
      exact hz hx (heq ▸ mem_ball_self (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    let U : OpenDomain n := ⟨ball (0 : Domain n) R ∩ {(0 : Domain n)}ᶜ,
      isOpen_ball.inter isOpen_compl_singleton⟩
    have hU : HasWeakGradient U w D := hP.mono inter_subset_right
    have hid := hU.2.2 i ψ hψ hcψ hsψ
    have hμ : volume.restrict U.val = μ := by
      change volume.restrict (ball (0 : Domain n) R ∩ {(0 : Domain n)}ᶜ) = μ
      rw [← Measure.restrict_restrict measurableSet_ball, restrict_compl_singleton]
    rw [hμ] at hid
    have hd (x : Domain n) : coordinateDerivative ψ hψ i x =
        (1 - χ k x) * coordinateDerivative φ hφ i x -
          φ x * coordinateDerivative (χ k) (hχ k) i x := by
      rw [coordinateDerivative_mul hφ (contDiff_const.sub (hχ k))]
      simp only [coordinateDerivative, fderiv_const_sub, neg_apply]
      ring
    simp_rw [hd, sub_smul] at hid
    have ha : Integrable (fun x => (1 - χ k x) •
        (coordinateDerivative φ hφ i x • w x)) μ := hleft.smul_of_top_right (hχL k)
    rw [← integral_sub ha (herrorI k)]
    calc
      _ = ∫ x, ((1 - χ k x) * coordinateDerivative φ hφ i x) • w x -
          (φ x * coordinateDerivative (χ k) (hχ k) i x) • w x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => by
          dsimp only
          rw [smul_smul, smul_smul]
      _ = -(∫ x, ψ x • D x i ∂μ) := hid
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [ψ, smul_smul]
          rw [mul_comm]
  have hlimError' : Tendsto (fun k =>
      ∫ x, φ x • (coordinateDerivative (χ k) (hχ k) i x • w x) ∂μ)
      atTop (𝓝 (0 : Ambient q)) := by
    have ht := hlimError.congr' (Eventually.of_forall fun k => integral_congr_ae (herrorEq k))
    simpa only [zero_smul, integral_zero] using ht
  have hleftlim := hlimLeft.sub hlimError'
  have hrightlim := hlimRight.neg
  have hleftfinal : Tendsto (fun k =>
      (∫ x, (1 - χ k x) • (coordinateDerivative φ hφ i x • w x) ∂μ) -
        ∫ x, φ x • (coordinateDerivative (χ k) (hχ k) i x • w x) ∂μ)
      atTop (𝓝 (∫ x, coordinateDerivative φ hφ i x • w x ∂μ)) := by
    simpa only [one_smul, sub_zero] using hleftlim
  have hrightfinal : Tendsto (fun k =>
      -(∫ x, (1 - χ k x) • (φ x • D x i) ∂μ))
      atTop (𝓝 (-(∫ x, φ x • D x i ∂μ))) := by
    simpa only [one_smul] using hrightlim
  exact tendsto_nhds_unique hleftfinal
    (hrightfinal.congr' (Eventually.of_forall fun k => (hId k).symm))

end StratificationTheory
