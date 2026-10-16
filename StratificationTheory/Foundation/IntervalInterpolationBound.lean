module

public import StratificationTheory.Foundation.BanachIntervalWeakRepresentative
public import Mathlib.Analysis.Real.Sqrt

/-!
# A uniform interpolation bound on a finite interval

Local averaging of a continuous representative with its actual weak-gradient
modulus gives a bound at every closed-interval point. Optimizing the averaging
length gives the product of the L2 norms of the map and its weak derivative.
-/

public section
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

private theorem interval_representative_local_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    {f : ℝ → E} (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (F : C(Icc a b, E))
    (hFae : ∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ = f x)
    {A : ℝ} (hA : 0 ≤ A)
    (hFbound : ∀ s t : Icc a b, ‖F t - F s‖ ^ 2 ≤ |(t : ℝ) - (s : ℝ)| * A)
    {δ : ℝ} (hδ : 0 < δ) (hδL : δ ≤ b - a) (t : Icc a b) :
    ‖F t‖ ^ 2 ≤ (2 / δ) * (∫ x in Ioo a b, ‖f x‖ ^ 2) + 2 * δ * A := by
  let l := max a ((t : ℝ) - δ)
  let r := l + δ
  have hal : a ≤ l := le_max_left _ _
  have hlt : l ≤ (t : ℝ) := max_le t.property.1 (sub_le_self _ hδ.le)
  have htr : (t : ℝ) ≤ r := by
    have h := le_max_right a ((t : ℝ) - δ)
    dsimp only [r]
    linarith only [h]
  have hlb : l ≤ b - δ := max_le (by linarith only [hδL])
    (sub_le_sub_right t.property.2 δ)
  have hrb : r ≤ b := by dsimp only [r]; linarith only [hlb]
  have hlen : r - l = δ := by dsimp only [r]; ring
  have hsub : Ioo l r ⊆ Ioo a b :=
    fun x hx => ⟨lt_of_le_of_lt hal hx.1, lt_of_lt_of_le hx.2 hrb⟩
  let μ := (volume : Measure ℝ).restrict (Ioo l r)
  have hpoint : ∀ᵐ x ∂μ, ‖F t‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * δ * A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hFae] with x hx hEq
    have hxI := hsub hx
    let s : Icc a b := ⟨x, hxI.1.le, hxI.2.le⟩
    have hdist : |(t : ℝ) - x| ≤ δ := abs_le.mpr
      ⟨by linarith only [hlt, hx.2, hlen], by linarith only [htr, hx.1, hlen]⟩
    have hinc : ‖F t - F s‖ ^ 2 ≤ δ * A :=
      (hFbound s t).trans (mul_le_mul_of_nonneg_right hdist hA)
    have hnorm : ‖F t‖ ≤ ‖F s‖ + ‖F t - F s‖ := by
      calc
        ‖F t‖ = ‖F s + (F t - F s)‖ := by congr 1; abel
        _ ≤ ‖F s‖ + ‖F t - F s‖ := norm_add_le _ _
    have hsquare : ‖F t‖ ^ 2 ≤ 2 * ‖F s‖ ^ 2 + 2 * ‖F t - F s‖ ^ 2 := by
      calc
        ‖F t‖ ^ 2 ≤ (‖F s‖ + ‖F t - F s‖) ^ 2 := by gcongr
        _ ≤ 2 * ‖F s‖ ^ 2 + 2 * ‖F t - F s‖ ^ 2 := by
          nlinarith only [sq_nonneg (‖F s‖ - ‖F t - F s‖)]
    rw [show F s = f x from hEq hxI] at hsquare hinc
    linarith only [hsquare, hinc]
  have hf2total : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Ioo a b)) :=
    hf.integrable_norm_pow (by decide)
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    hf2total.mono_measure (Measure.restrict_mono_set volume hsub)
  have hD : (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ ∫ x in Ioo a b, ‖f x‖ ^ 2 :=
    integral_mono_measure (Measure.restrict_mono_set volume hsub)
      (Eventually.of_forall fun x => sq_nonneg ‖f x‖) hf2total
  have hmono := integral_mono_ae (integrable_const (‖F t‖ ^ 2))
    ((hf2.const_mul 2).add (integrable_const (2 * δ * A))) hpoint
  have hμ : μ.real univ = δ := by
    simp only [μ, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      hlen, ENNReal.toReal_ofReal hδ.le]
  change (∫ x : ℝ, ‖F t‖ ^ 2 ∂μ) ≤
    ∫ x, 2 * ‖f x‖ ^ 2 + 2 * δ * A ∂μ at hmono
  rw [integral_const, integral_add (hf2.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const, smul_eq_mul, smul_eq_mul, hμ] at hmono
  calc
    ‖F t‖ ^ 2 ≤ (2 * (∫ x in Ioo a b, ‖f x‖ ^ 2) + δ * (2 * δ * A)) / δ :=
      (le_div_iff₀ hδ).mpr (by linarith only [hmono, hD])
    _ = (2 / δ) * (∫ x in Ioo a b, ‖f x‖ ^ 2) + 2 * δ * A := by
      field_simp [hδ.ne']

private theorem interpolation_length_optimization {X D A L : ℝ}
    (hL : 0 < L) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ L → X ≤ (2 / δ) * D + 2 * δ * A) :
    X ≤ (4 / L) * D + 4 * Real.sqrt (D * A) := by
  have hfour : (4 / L) * D = 2 * ((2 / L) * D) := by ring
  by_cases hAzero : A = 0
  · subst A
    have hX := h L hL le_rfl
    have hnonneg : 0 ≤ (2 / L) * D := mul_nonneg (div_nonneg (by norm_num) hL.le) hD
    simp only [mul_zero, add_zero, Real.sqrt_zero] at hX ⊢
    rw [hfour]
    linarith only [hX, hnonneg]
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  by_cases hDzero : D = 0
  · subst D
    have hX : X ≤ 0 := by
      by_contra hn
      have hXpos : 0 < X := lt_of_not_ge hn
      let δ := min L (X / (4 * A))
      have hδ : 0 < δ := lt_min hL (div_pos hXpos (by positivity))
      have hbound := h δ hδ (min_le_left _ _)
      have hprod : δ * (4 * A) ≤ X :=
        (le_div_iff₀ (by positivity : 0 < 4 * A)).mp (min_le_right _ _)
      simp only [mul_zero, zero_add] at hbound
      nlinarith only [hbound, hprod, hXpos]
    simpa only [zero_mul, mul_zero, Real.sqrt_zero, add_zero] using hX
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDzero)
  by_cases hsmall : D ≤ L ^ 2 * A
  · let δ := Real.sqrt (D / A)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (div_pos hDpos hApos)
    have hδL : δ ≤ L := Real.sqrt_le_iff.mpr
      ⟨hL.le, (div_le_iff₀ hApos).mpr hsmall⟩
    have hδsq : δ ^ 2 * A = D := by
      rw [show δ ^ 2 = D / A from Real.sq_sqrt (div_nonneg hD hA)]
      exact div_mul_cancel₀ D hAzero
    have hroot : Real.sqrt (D * A) = δ * A := by
      apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hD hA) (mul_nonneg hδ.le hA)).mpr
      calc
        D * A = (δ ^ 2 * A) * A := by rw [hδsq]
        _ = (δ * A) ^ 2 := by ring
    have hquot : (2 / δ) * D = 2 * δ * A := by
      rw [← hδsq]
      field_simp [hδ.ne']
    have hX := h δ hδ hδL
    rw [hquot] at hX
    rw [hroot]
    have hnonneg : 0 ≤ (4 / L) * D := mul_nonneg (div_nonneg (by norm_num) hL.le) hD
    nlinarith only [hX, hnonneg]
  · have hlarge : L ^ 2 * A ≤ D := (lt_of_not_ge hsmall).le
    have hcompare : 2 * L * A ≤ (2 / L) * D := by
      calc
        2 * L * A ≤ (2 * D) / L :=
          (le_div_iff₀ hL).mpr (by nlinarith only [hlarge])
        _ = (2 / L) * D := by ring
    have hX := h L hL le_rfl
    have hroot := Real.sqrt_nonneg (D * A)
    rw [hfour]
    linarith only [hX, hcompare, hroot]

/-- Actual Banach-valued L2 weak data have one unique continuous representative
with the exact integral increments and a uniform interpolation bound. The
constants are independent of the Banach space, interval and original data. -/
theorem banach_interval_weakDerivative_exists_unique_interpolation_representative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x, deriv φ x • f x) = -(∫ x, φ x • g x)) :
    ∃! F : C(Icc a b, E),
      (∀ᵐ x ∂volume, ∀ hx : x ∈ Ioo a b, F ⟨x, hx.1.le, hx.2.le⟩ = f x) ∧
      (∃ G : ℝ → E, AbsolutelyContinuousOnInterval G a b ∧
        ∀ x : Icc a b, G x = F x) ∧
      (∀ s t : Icc a b, F t - F s = ∫ y in (s : ℝ)..(t : ℝ), g y) ∧
      (∀ s t : Icc a b, ‖F t - F s‖ ^ 2 ≤
        |(t : ℝ) - (s : ℝ)| * ∫ y in Ioo a b, ‖g y‖ ^ 2) ∧
      ∀ t : Icc a b, ‖F t‖ ^ 2 ≤
        (4 / (b - a)) * (∫ y in Ioo a b, ‖f y‖ ^ 2) +
        4 * Real.sqrt ((∫ y in Ioo a b, ‖f y‖ ^ 2) *
          (∫ y in Ioo a b, ‖g y‖ ^ 2)) := by
  obtain ⟨F, hF, hUnique⟩ :=
    banach_interval_weakDerivative_exists_unique_continuous_representative hab hf hg hw
  have hL : 0 < b - a := sub_pos.mpr hab
  have hD : 0 ≤ ∫ y in Ioo a b, ‖f y‖ ^ 2 := integral_nonneg (fun y => sq_nonneg ‖f y‖)
  have hA : 0 ≤ ∫ y in Ioo a b, ‖g y‖ ^ 2 := integral_nonneg (fun y => sq_nonneg ‖g y‖)
  refine ⟨F, ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, ?_⟩, ?_⟩
  · intro t
    apply interpolation_length_optimization hL hD hA
    intro δ hδ hδL
    exact interval_representative_local_average hf F hF.1 hA hF.2.2.2.1 hδ hδL t
  · intro H hH
    apply hUnique H
    refine ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1, ?_⟩
    intro t
    exact interval_representative_local_average hf H hH.1 hA hH.2.2.2.1 hL le_rfl t

end StratificationTheory
