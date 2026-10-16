module

public import StratificationTheory.Foundation.IntervalInterpolationBound
public import StratificationTheory.Foundation.IntervalClosedConstraints

/-!
# Quantitative bounds for integral representatives on a closed line

Original L2 data and exact integral increments identify a representative with
the unique Banach weak representative. Its interpolation bound therefore holds
at every closed-interval point.
-/

public section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
namespace StratificationTheory

/-- Exact original-gradient increments imply the distributional derivative
identity for the original interior a.e. class. -/
theorem interval_weakDerivative_of_integral_increments
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {F f g : ℝ → E}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y) :
    ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, deriv φ x • f x) = -(∫ x, φ x • g x) := by
  intro φ hφ hcφ hsφ
  let G : ℝ → E := fun x => ∫ y in a..x, g y
  have hGInt : IntegrableOn G (Ioo a b) volume :=
    (intervalPrimitive_absolutelyContinuous (intervalIntegrable_of_memLp_two hab.le hg)
      left_mem_uIcc).continuousOn.intervalIntegrable.1.mono_set Ioo_subset_Ioc_self
  have hφD := hφ.continuous_deriv (by simp)
  have hconstInt : IntegrableOn (fun x => deriv φ x • F a) (Ioo a b) volume :=
    (integrable_const (F a)).smul_of_top_right
      (hφD.memLp_top_of_hasCompactSupport hcφ.deriv _)
  have hprimInt : IntegrableOn (fun x => deriv φ x • G x) (Ioo a b) volume :=
    hGInt.smul_of_top_right (hφD.memLp_top_of_hasCompactSupport hcφ.deriv _)
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
    (fun hx => (lt_irrefl a) (hsφ hx).1)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun hx => (lt_irrefl b) (hsφ hx).2)
  have hderivInt : (∫ x in Ioo a b, deriv φ x) = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => (hφ.differentiable (by simp) x)) (hφD.intervalIntegrable a b),
      hφa, hφb, sub_self]
  have hleft : (∫ x in Ioo a b, deriv φ x • f x) = ∫ x, deriv φ x • f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun hm => hx (hsφ (tsupport_deriv_subset hm))), zero_smul]
  have hright : (∫ x in Ioo a b, φ x • g x) = ∫ x, φ x • g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hsφ hm)), zero_smul]
  rw [← hleft, ← hright]
  have hEq : (fun x => deriv φ x • f x) =ᵐ[volume.restrict (Ioo a b)]
      (fun x => deriv φ x • (F a + G x)) := by
    filter_upwards [hFae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [← hx]
    congr 1
    have hi := hinc a ⟨le_rfl, hab.le⟩ x ⟨hxI.1.le, hxI.2.le⟩
    dsimp only [G]
    exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
  rw [integral_congr_ae hEq]
  simp_rw [smul_add]
  rw [integral_add hconstInt hprimInt, integral_smul_const, hderivInt,
    zero_smul, zero_add]
  exact banach_intervalPrimitive_weakDerivative hab.le hg hφ hcφ hsφ

/-- An integral representative of actual L2 data obeys the optimized uniform
interpolation estimate at every point, including both endpoints. -/
theorem interval_integral_representative_interpolation_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {F f g : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y) :
    ∀ t ∈ Icc a b, ‖F t‖ ^ 2 ≤
      (4 / (b - a)) * (∫ y in Ioo a b, ‖f y‖ ^ 2) +
      4 * Real.sqrt ((∫ y in Ioo a b, ‖f y‖ ^ 2) *
        (∫ y in Ioo a b, ‖g y‖ ^ 2)) := by
  have hw := interval_weakDerivative_of_integral_increments hab hg hFae hinc
  obtain ⟨H, hH, _⟩ :=
    banach_interval_weakDerivative_exists_unique_interpolation_representative hab hf hg hw
  have hGcont : ContinuousOn (fun x => ∫ y in a..x, g y) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (intervalPrimitive_absolutelyContinuous (intervalIntegrable_of_memLp_two hab.le hg)
        left_mem_uIcc).continuousOn
  have hFcont : ContinuousOn F (Icc a b) := by
    apply (continuousOn_const.add hGcont).congr
    intro x hx
    exact (sub_eq_iff_eq_add.mp (hinc a ⟨le_rfl, hab.le⟩ x hx)).trans (add_comm _ _)
  let D : C(Icc a b, E) := ⟨fun x => F x - H x,
    hFcont.restrict.sub H.continuous⟩
  have hDae : ∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b,
      D ⟨x, hx.1.le, hx.2.le⟩ ∈ ({0} : Set E) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hFae, hH.1] with x hx hHx hxI
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mpr ((hx hxI).trans (hHx hxI).symm))
  have hD := continuous_interval_mem_closed_of_ae hab D isClosed_singleton hDae
  intro t ht
  have heq : F t = H ⟨t, ht⟩ :=
    sub_eq_zero.mp (Set.mem_singleton_iff.mp (hD ⟨t, ht⟩))
  rw [heq]
  exact hH.2.2.2.2 ⟨t, ht⟩

/-- The same estimate applies to the difference of two representatives, with
the difference of their original weak-gradient data. -/
theorem interval_integral_pair_interpolation_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {F G f h g k : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hk : MemLp k 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo a b)] h)
    (hFinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      G t - G s = ∫ y in s..t, k y) :
    ∀ t ∈ Icc a b, ‖F t - G t‖ ^ 2 ≤
      (4 / (b - a)) * (∫ y in Ioo a b, ‖f y - h y‖ ^ 2) +
      4 * Real.sqrt ((∫ y in Ioo a b, ‖f y - h y‖ ^ 2) *
        (∫ y in Ioo a b, ‖g y - k y‖ ^ 2)) := by
  have hdiffinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (F t - G t) - (F s - G s) = ∫ y in s..t, g y - k y := by
    intro s hs t ht
    have hsub : uIcc s t ⊆ uIcc a b := by
      rw [uIcc_of_le hab.le]
      exact uIcc_subset_Icc hs ht
    calc
      _ = (F t - F s) - (G t - G s) := by abel
      _ = (∫ y in s..t, g y) - ∫ y in s..t, k y := by rw [hFinc s hs t ht, hGinc s hs t ht]
      _ = _ := (intervalIntegral.integral_sub
        ((intervalIntegrable_of_memLp_two hab.le hg).mono_set hsub)
        ((intervalIntegrable_of_memLp_two hab.le hk).mono_set hsub)).symm
  exact interval_integral_representative_interpolation_bound hab (hf.sub hh) (hg.sub hk)
    (hFae.sub hGae) hdiffinc

/-- The uniform pair bound uses the sum of the original quadratic derivative
energies, rather than requiring a new gradient witness for the difference. -/
theorem interval_integral_pair_interpolation_bound_original_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {F G f h g k : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hh : MemLp h 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hk : MemLp k 2 (volume.restrict (Ioo a b)))
    (hFae : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hGae : G =ᵐ[volume.restrict (Ioo a b)] h)
    (hFinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      G t - G s = ∫ y in s..t, k y) :
    ∀ t ∈ Icc a b, ‖F t - G t‖ ^ 2 ≤
      (4 / (b - a)) * (∫ y in Ioo a b, ‖f y - h y‖ ^ 2) +
      4 * Real.sqrt (2 * (∫ y in Ioo a b, ‖f y - h y‖ ^ 2) *
        (∫ y in Ioo a b, ‖g y‖ ^ 2 + ‖k y‖ ^ 2)) := by
  have henergy : (∫ y in Ioo a b, ‖g y - k y‖ ^ 2) ≤
      2 * (∫ y in Ioo a b, ‖g y‖ ^ 2 + ‖k y‖ ^ 2) := by
    have hnormsq (y : ℝ) : ‖g y - k y‖ ^ 2 ≤ 2 * (‖g y‖ ^ 2 + ‖k y‖ ^ 2) := by
      calc
        _ ≤ (‖g y‖ + ‖k y‖) ^ 2 := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by nlinarith only [sq_nonneg (‖g y‖ - ‖k y‖)]
    have hInt := integral_mono_ae ((hg.sub hk).integrable_norm_pow (by decide))
      (((hg.integrable_norm_pow (by decide)).add
        (hk.integrable_norm_pow (by decide))).const_mul 2)
      (Eventually.of_forall hnormsq)
    rwa [integral_const_mul] at hInt
  intro t ht
  apply (interval_integral_pair_interpolation_bound hab hf hh hg hk hFae hGae
    hFinc hGinc t ht).trans
  have hD : 0 ≤ ∫ y in Ioo a b, ‖f y - h y‖ ^ 2 :=
    integral_nonneg (fun y => sq_nonneg _)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (∫ y in Ioo a b, ‖f y - h y‖ ^ 2) *
        (2 * ∫ y in Ioo a b, ‖g y‖ ^ 2 + ‖k y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left henergy hD
    _ = _ := by ring

end StratificationTheory
