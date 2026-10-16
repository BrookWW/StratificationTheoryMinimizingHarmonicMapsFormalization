module

public import HarmonicMaps.SobolevRestriction
public import StratificationTheory.Interpolation.RadialCutoffConstruction
public import StratificationTheory.Foundation.CylinderCoordinateMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Removal of affine flats from the original weak graph

Shrinking smooth transverse cutoffs remove a null affine kernel when the
original map divided by its transverse norm is integrable. Bounded maps
satisfy that condition in transverse dimension at least two.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology ContDiff
namespace StratificationTheory

private theorem exists_linear_kernel_cutoffs {d m : ℕ} (P : Domain d →L[ℝ] Domain m) (c : Domain d) :
    ∃ χ : ℕ → Domain d → ℝ, ∃ hχ : ∀ k, ContDiff ℝ ∞ (χ k),
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧
      (∀ k, tsupport (χ k) ⊆ {x | ‖P (x - c)‖ ≤ 2 / ((k : ℝ) + 1)}) ∧
      (∀ (k : ℕ) x, ‖P (x - c)‖ ≤ 1 / ((k : ℝ) + 1) → χ k x = 1) ∧
      (∀ k x (i : Fin d), |coordinateDerivative (χ k) (hχ k) i x| * ‖P (x - c)‖ ≤ 4 * ‖P‖) ∧
      ∀ x : Domain d, P (x - c) ≠ 0 → ∀ᶠ k in atTop,
        χ k x = 0 ∧ ∀ i : Fin d, coordinateDerivative (χ k) (hχ k) i x = 0 := by
  classical
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp only [δ]; positivity
  have hcut (k : ℕ) := Interpolation.exists_quantitative_radial_cutoff
    (0 : Domain m) (hδ k) (hδ k)
  choose ψ hψ hcψ hsψ hvψ honψ hoffψ hDψ hdψ using hcut
  let χ : ℕ → Domain d → ℝ := fun k => ψ k ∘ (fun x => P (x - c))
  have hχ (k : ℕ) : ContDiff ℝ ∞ (χ k) := (hψ k).comp (P.contDiff.comp (contDiff_id.sub contDiff_const))
  have hs (k : ℕ) : tsupport (χ k) ⊆ {x | ‖P (x - c)‖ ≤ 2 * δ k} := by
    apply closure_minimal _ (isClosed_le (P.continuous.comp (continuous_id.sub continuous_const)).norm continuous_const)
    intro x hx
    have hxp : P (x - c) ∈ tsupport (ψ k) := subset_tsupport _ hx
    have hnorm := mem_closedBall_zero_iff.mp (hsψ k hxp)
    simpa only [mem_setOf_eq, Function.comp_apply, Pi.sub_apply, id_eq, two_mul] using hnorm
  have hzero (k : ℕ) (x : Domain d) (hx : 2 * δ k < ‖P (x - c)‖) :
      χ k x = 0 ∧ ∀ i : Fin d, coordinateDerivative (χ k) (hχ k) i x = 0 := by
    have hout : x ∉ tsupport (χ k) := fun hm => (not_le.mpr hx) (hs k hm)
    refine ⟨image_eq_zero_of_notMem_tsupport hout, fun i => ?_⟩
    change fderiv ℝ (χ k) x (EuclideanSpace.single i 1) = 0
    rw [fderiv_of_notMem_tsupport ℝ hout]
    rfl
  have hderiv (k : ℕ) (x : Domain d) (i : Fin d) :
      |coordinateDerivative (χ k) (hχ k) i x| ≤ (2 / δ k) * ‖P‖ := by
    have hPder : HasFDerivAt (fun x => P (x - c)) P x := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
        P.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)
    have hf : fderiv ℝ (χ k) x = (fderiv ℝ (ψ k) (P (x - c))).comp P :=
      (((hψ k).differentiable (by simp) (P (x - c))).hasFDerivAt.comp x hPder).fderiv
    calc
      _ = ‖fderiv ℝ (χ k) x (EuclideanSpace.single i 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (χ k) x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (χ k) x‖ := by simp only [PiLp.norm_single, norm_one, mul_one]
      _ ≤ ‖fderiv ℝ (ψ k) (P (x - c))‖ * ‖P‖ := by rw [hf]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hDψ k (P (x - c))) (norm_nonneg P)
  refine ⟨χ, hχ, (fun k x => hvψ k (P (x - c))), ?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [δ, mul_one_div] using hs k
  · intro k x hx
    exact honψ k (P (x - c)) (mem_closedBall_zero_iff.mpr hx)
  · intro k x i
    by_cases hx : ‖P (x - c)‖ ≤ 2 * δ k
    · calc
        _ ≤ ((2 / δ k) * ‖P‖) * (2 * δ k) :=
          mul_le_mul (hderiv k x i) hx (norm_nonneg _) (by positivity)
        _ = _ := by field_simp [(hδ k).ne']; ring
    · rw [(hzero k x (lt_of_not_ge hx)).2 i, abs_zero, zero_mul]
      positivity
  · intro x hx
    have ht : Tendsto (fun k => 2 * δ k) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
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

/-- Original weak data off a null affine kernel extend across it when the
same map divided by its transverse norm is integrable. -/
theorem hasWeakGradient_of_affine_kernel_and_integrable_inverse {n m q : ℕ}
    (P : Domain n →L[ℝ] Domain m) (c : Domain n) {Ω : OpenDomain n}
    (hnull : (volume : Measure (Domain n)) ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)}) = 0)
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    (hP : HasWeakGradient
      ⟨Ω.val ∩ ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)})ᶜ,
        Ω.property.inter (isClosed_singleton.preimage (P.continuous.comp (continuous_id.sub continuous_const))).isOpen_compl⟩ w D)
    (hw : IntegrableOn w (Ω.val) volume)
    (hD : ∀ i : Fin n, IntegrableOn (fun x => D x i) (Ω.val) volume)
    (hinv : IntegrableOn (fun x => ‖P (x - c)‖⁻¹ • w x) (Ω.val) volume) :
    HasWeakGradient Ω w D := by
  classical
  let μ := volume.restrict (Ω.val)
  obtain ⟨χ, hχ, hvalues, hsupport, hone, hderiv, hevent⟩ :=
    exists_linear_kernel_cutoffs P c
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
  have hae0 : ∀ᵐ x ∂μ, P (x - c) ≠ 0 := by
    have hzero := measure_eq_zero_iff_ae_notMem.mp hnull
    simpa only [mem_preimage, mem_singleton_iff] using
      ae_restrict_of_ae hzero (s := Ω.val)
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
    φ x * coordinateDerivative (χ k) (hχ k) i x * ‖P (x - c)‖
  have hα (k : ℕ) : AEStronglyMeasurable (α k) μ :=
    ((hφ.continuous.mul
      ((hχ k).continuous_fderiv (by simp) |>.clm_apply continuous_const)).mul
        (P.continuous.comp (continuous_id.sub continuous_const)).norm).aestronglyMeasurable
  have hαbound (k : ℕ) : ∀ᵐ x ∂μ, |α k x| ≤ B * (4 * ‖P‖) :=
    Eventually.of_forall fun x => by
      dsimp only [α]
      rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg (P (x - c))), mul_assoc]
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
      (fun x => α k x • (‖P (x - c)‖⁻¹ • w x)) =ᵐ[μ]
        (fun x => φ x • (coordinateDerivative (χ k) (hχ k) i x • w x)) := by
    filter_upwards [hae0] with x hx
    simp only [α, smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),
      mul_one]
  have herrorI (k : ℕ) : Integrable
      (fun x => φ x • (coordinateDerivative (χ k) (hχ k) i x • w x)) μ := by
    apply Integrable.congr ?_ (herrorEq k)
    exact hinv.bdd_smul (B * (4 * ‖P‖)) (hα k) (by simpa only [Real.norm_eq_abs] using hαbound k)
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
    have hsψ : tsupport ψ ⊆ Ω.val ∩ ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)})ᶜ := by
      refine subset_inter (tsupport_mul_subset_left.trans hsφ) ?_
      have hz : tsupport ψ ⊆ ((fun x => P (x - c)) ⁻¹' ball (0 : Domain m) (1 / ((k : ℝ) + 1)))ᶜ := by
        apply closure_minimal _ (isOpen_ball.preimage (P.continuous.comp (continuous_id.sub continuous_const))).isClosed_compl
        intro x hx hxball
        have hxnorm : ‖P (x - c)‖ < 1 / ((k : ℝ) + 1) := mem_ball_zero_iff.mp hxball
        exact hx (by simp only [ψ, hone k x hxnorm.le, sub_self, mul_zero])
      intro x hx hx0
      have heq : P (x - c) = 0 := hx0
      apply hz hx
      change P (x - c) ∈ ball (0 : Domain m) (1 / ((k : ℝ) + 1))
      rw [heq]
      exact mem_ball_self (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
    let U : OpenDomain n := ⟨Ω.val ∩ ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)})ᶜ,
      Ω.property.inter (isClosed_singleton.preimage (P.continuous.comp (continuous_id.sub continuous_const))).isOpen_compl⟩
    have hU : HasWeakGradient U w D := hP
    have hid := hU.2.2 i ψ hψ hcψ hsψ
    have hμ : volume.restrict U.val = μ := by
      apply Measure.restrict_congr_set
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
      change (x ∈ Ω.val ∩ ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)})ᶜ) =
        (x ∈ Ω.val)
      simp only [mem_inter_iff, mem_compl_iff, hx, not_false_eq_true, and_true]
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

private theorem locallyIntegrable_inverse_transverse_norm {n m : ℕ} (hm : 2 ≤ m)
    (Q : Domain (n + m) ≃ₗᵢ[ℝ] Domain (n + m)) (c : Domain (n + m)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    LocallyIntegrable (fun x : Domain (n + m) => ‖(e (Q (x - c))).2‖⁻¹) volume := by
  intro e
  have hd : 1 ≤ Module.finrank ℝ (Domain m) := by simpa using (show 1 ≤ m by omega)
  have ha : (1 : ℝ) < Module.finrank ℝ (Domain m) := by
    have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    simpa using hm'
  have hscalar : LocallyIntegrable (fun z : Domain m => ‖z‖⁻¹) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := (1 : ℝ)) (α := (1 : ℝ)) hd ha
    · exact Eventually.of_forall fun z => by
        simp only [Real.rpow_neg_one, one_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
        exact le_rfl
    · exact continuous_norm.measurable.inv.aestronglyMeasurable
  let F : Domain (n + m) → Domain n × Domain m := fun x => e (Q (x - c))
  have hF : Continuous F := e.continuous.comp (Q.continuous.comp (continuous_id.sub continuous_const))
  have hMP : MeasurePreserving F volume (volume.prod volume) := by
    have ht := (measurePreserving_finAddEquivProd n m).comp
      (Q.measurePreserving.comp (measurePreserving_add_right volume (-c)))
    simpa only [F, Function.comp_def, sub_eq_add_neg] using ht
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨r, hr, hbound⟩ := (hK.image hF).isBounded.exists_pos_norm_lt
  let μ : Measure (Domain n) := volume.restrict (ball (0 : Domain n) r)
  let ν : Measure (Domain m) := volume.restrict (ball (0 : Domain m) r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hI : Integrable (fun z : Domain m => ‖z‖⁻¹) ν :=
    (hscalar.integrableOn_isCompact (isCompact_closedBall (0 : Domain m) r)).mono_set ball_subset_closedBall
  have hprod : Integrable (fun p : Domain n × Domain m => ‖p.2‖⁻¹) (μ.prod ν) := hI.comp_snd μ
  have hM := hMP.restrict_preimage
    ((measurableSet_ball (x := (0 : Domain n)) (ε := r)).prod
      (measurableSet_ball (x := (0 : Domain m)) (ε := r)))
  rw [← Measure.prod_restrict] at hM
  have hwhole : IntegrableOn (fun x : Domain (n + m) => ‖(F x).2‖⁻¹)
      (F ⁻¹' (ball (0 : Domain n) r ×ˢ ball (0 : Domain m) r)) volume :=
    hM.integrable_comp_of_integrable hprod
  apply hwhole.mono_set
  intro x hx
  have hb := hbound (F x) ⟨x, hx, rfl⟩
  exact ⟨mem_ball_zero_iff.mpr ((norm_fst_le (F x)).trans_lt hb),
    mem_ball_zero_iff.mpr ((norm_snd_le (F x)).trans_lt hb)⟩

/-- A bounded original map and full original L2 columns have no weak-gradient
singularity on an affine flat of codimension at least two. The same raw map
and the same physical columns extend over the flat. -/
theorem memW12_of_bounded_off_affine_coordinate_flat {n m q : ℕ} (hm : 2 ≤ m)
    (Q : Domain (n + m) ≃ₗᵢ[ℝ] Domain (n + m)) (c : Domain (n + m))
    {Ω : OpenDomain (n + m)} (hΩ : Bornology.IsBounded Ω.val)
    {w : Domain (n + m) → Ambient q} {D : Domain (n + m) → Gradient (n + m) q}
    (hw : MemLp w 2 (volume.restrict Ω.val))
    (hD : ∀ i : Fin (n + m), MemLp (fun x => D x i) 2 (volume.restrict Ω.val))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ ≤ B) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let P : Domain (n + m) →L[ℝ] Domain m :=
      (ContinuousLinearMap.snd ℝ (Domain n) (Domain m)).comp
        (e.toContinuousLinearMap.comp Q.toContinuousLinearEquiv.toContinuousLinearMap)
    HasWeakGradient
      ⟨Ω.val ∩ ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)})ᶜ,
        Ω.property.inter (isClosed_singleton.preimage
          (P.continuous.comp (continuous_id.sub continuous_const))).isOpen_compl⟩ w D →
    MemW12 Ω w D := by
  intro e P hweak
  have hΩfinite : (volume : Measure (Domain (n + m))) Ω.val ≠ ⊤ :=
    ne_top_of_le_ne_top hΩ.isCompact_closure.measure_lt_top.ne (measure_mono subset_closure)
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩfinite
  have hweight : LocallyIntegrable (fun x : Domain (n + m) => ‖P (x - c)‖⁻¹) volume :=
    locallyIntegrable_inverse_transverse_norm hm Q c
  have hweightI : IntegrableOn (fun x : Domain (n + m) => ‖P (x - c)‖⁻¹) Ω.val volume :=
    (hweight.integrableOn_isCompact hΩ.isCompact_closure).mono_set subset_closure
  have hAS : AEStronglyMeasurable (fun x : Domain (n + m) => ‖P (x - c)‖⁻¹ • w x)
      (volume.restrict Ω.val) :=
    ((P.continuous.comp (continuous_id.sub continuous_const)).norm.measurable.inv.aestronglyMeasurable).smul
      hw.aestronglyMeasurable
  have hinv : IntegrableOn (fun x : Domain (n + m) => ‖P (x - c)‖⁻¹ • w x) Ω.val volume := by
    apply (hweightI.const_mul B).mono' hAS
    filter_upwards [hB] with x hx
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (norm_nonneg (P (x - c))))
  have hnull : (volume : Measure (Domain (n + m)))
      ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)}) = 0 := by
    letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    let F : Domain (n + m) → Domain n × Domain m := fun x => e (Q (x - c))
    have hMP : MeasurePreserving F volume (volume.prod volume) := by
      have ht := (measurePreserving_finAddEquivProd n m).comp
        (Q.measurePreserving.comp (measurePreserving_add_right volume (-c)))
      simpa only [F, Function.comp_def, sub_eq_add_neg] using ht
    have hs : ((fun x => P (x - c)) ⁻¹' {(0 : Domain m)}) =
        F ⁻¹' (univ ×ˢ {(0 : Domain m)}) := by
      ext x
      simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_singleton_iff]
      rfl
    rw [hs, hMP.measure_preimage (MeasurableSet.univ.prod (measurableSet_singleton (0 : Domain m))).nullMeasurableSet,
      Measure.prod_prod]
    simp
  exact ⟨hasWeakGradient_of_affine_kernel_and_integrable_inverse P c hnull hweak
      (hw.integrable (by norm_num)) (fun i => (hD i).integrable (by norm_num)) hinv,
    hw, hD⟩

/-- The same bounded original weak graph extends across any fixed finite
family of affine coordinate flats of codimension two. -/
theorem memW12_of_bounded_off_finite_affine_coordinate_flats {n q : ℕ} {ι : Type*}
    (s : Finset ι) (Q : ι → Domain (n + 2) ≃ₗᵢ[ℝ] Domain (n + 2))
    (c : ι → Domain (n + 2)) {Ω : OpenDomain (n + 2)} (hΩ : Bornology.IsBounded Ω.val)
    {w : Domain (n + 2) → Ambient q} {D : Domain (n + 2) → Gradient (n + 2) q}
    (hw : MemLp w 2 (volume.restrict Ω.val))
    (hD : ∀ i : Fin (n + 2), MemLp (fun x => D x i) 2 (volume.restrict Ω.val))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ ≤ B) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 2)
    let P : ι → Domain (n + 2) →L[ℝ] Domain 2 := fun j =>
      (ContinuousLinearMap.snd ℝ (Domain n) (Domain 2)).comp
        (e.toContinuousLinearMap.comp (Q j).toContinuousLinearEquiv.toContinuousLinearMap)
    let Z : ι → Set (Domain (n + 2)) := fun j => (fun x => P j (x - c j)) ⁻¹' {(0 : Domain 2)}
    let V : OpenDomain (n + 2) :=
      ⟨Ω.val ∩ (⋃ j ∈ s, Z j)ᶜ,
        Ω.property.inter (isClosed_biUnion_finset (fun j _ =>
          isClosed_singleton.preimage ((P j).continuous.comp
            (continuous_id.sub continuous_const)))).isOpen_compl⟩
    HasWeakGradient V w D → MemW12 Ω w D := by
  classical
  induction s using Finset.induction_on generalizing Ω with
  | empty =>
      intro e P Z V hweak
      have hV : V = Ω := by
        apply Subtype.ext
        ext x
        simp [V]
      exact ⟨by simpa only [hV] using hweak, hw, hD⟩
  | @insert a s _ha ih =>
      intro e P Z V hweak
      let Ωa : OpenDomain (n + 2) :=
        ⟨Ω.val ∩ (Z a)ᶜ, Ω.property.inter (isClosed_singleton.preimage
          ((P a).continuous.comp (continuous_id.sub continuous_const))).isOpen_compl⟩
      have hsub : Ωa.val ⊆ Ω.val := inter_subset_left
      have hΩa : Bornology.IsBounded Ωa.val := hΩ.subset hsub
      have hwA : MemLp w 2 (volume.restrict Ωa.val) := hw.mono_measure (Measure.restrict_mono_set volume hsub)
      have hDA (i : Fin (n + 2)) : MemLp (fun x => D x i) 2 (volume.restrict Ωa.val) :=
        (hD i).mono_measure (Measure.restrict_mono_set volume hsub)
      have hBA : ∀ᵐ x ∂volume.restrict Ωa.val, ‖w x‖ ≤ B :=
        ae_restrict_of_ae_restrict_of_subset hsub hB
      let V' : OpenDomain (n + 2) :=
        ⟨Ωa.val ∩ (⋃ j ∈ s, Z j)ᶜ,
          Ωa.property.inter (isClosed_biUnion_finset (fun j _ =>
            isClosed_singleton.preimage ((P j).continuous.comp
              (continuous_id.sub continuous_const)))).isOpen_compl⟩
      have hVV : V' = V := by
        apply Subtype.ext
        ext x
        simp only [V', V, Ωa, Finset.mem_insert, mem_inter_iff, mem_compl_iff, mem_iUnion,
          exists_prop, not_exists, not_and]
        constructor
        · rintro ⟨⟨hxΩ, hxa⟩, hxs⟩
          refine ⟨hxΩ, ?_⟩
          intro j hj
          rcases hj with rfl | hjs
          · exact hxa
          · exact hxs j hjs
        · rintro ⟨hxΩ, hxs⟩
          refine ⟨⟨hxΩ, hxs a (Or.inl rfl)⟩, ?_⟩
          intro j hj
          exact hxs j (Or.inr hj)
      have hweakA : HasWeakGradient V' w D := by rw [hVV]; exact hweak
      have hWA : MemW12 Ωa w D := ih hΩa hwA hDA hBA hweakA
      exact memW12_of_bounded_off_affine_coordinate_flat (n := n) (m := 2) (q := q)
        (by decide) (Q a) (c a) hΩ hw hD hB hWA.1

end StratificationTheory
