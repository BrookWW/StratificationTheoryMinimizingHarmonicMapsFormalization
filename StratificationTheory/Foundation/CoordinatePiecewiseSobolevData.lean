module

public import StratificationTheory.Foundation.CylinderCoordinateMeasure
public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Literal piecewise data on adjacent native rectangles

The native time coordinate has null level sets. Two adjacent rectangles
therefore partition their union up to the common null face, preserving
original L2 data and additive integrals of the displayed piecewise fields.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal
namespace StratificationTheory

/-- Every native last-coordinate affine hyperplane has zero ambient volume. -/
theorem ae_native_time_ne (n : ℕ) (b : ℝ) :
    ∀ᵐ y : Domain (n + 1) ∂volume,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ≠ b := by
  have hb : ∀ᵐ t : ℝ ∂volume, t ≠ b := by
    exact ae_iff.mpr (by simpa only [not_not, Set.setOf_eq_eq_singleton] using
      (measure_singleton b : (volume : Measure ℝ) {b} = 0))
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Domain n))) (ν := (volume : Measure ℝ))).ae hb
  exact (measurePreserving_cylinder_coordinates n).quasiMeasurePreserving.ae hp

/-- The original whole-rectangle piecewise indicator is the sum of the
original half-rectangle indicators outside the null common time face. -/
theorem coordinate_rectangle_piecewise_indicator_ae {n : ℕ} {E : Type*} [AddZeroClass E]
    (S : Set (Domain n)) {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (u v : Domain (n + 1) → E) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    {y | X y ∈ S ∧ T y ∈ Ioo a c}.indicator (fun y => if T y < b then u y else v y) =ᵐ[volume]
      fun y => {z | X z ∈ S ∧ T z ∈ Ioo a b}.indicator u y +
        {z | X z ∈ S ∧ T z ∈ Ioo b c}.indicator v y := by
  intro e X T
  filter_upwards [ae_native_time_ne n b] with y hy
  change T y ≠ b at hy
  by_cases hT : T y < b
  · have hnotR : y ∉ {z | X z ∈ S ∧ T z ∈ Ioo b c} :=
      fun h => (not_lt_of_ge hT.le) h.2.1
    by_cases hL : X y ∈ S ∧ a < T y
    · have hfull : y ∈ {z | X z ∈ S ∧ T z ∈ Ioo a c} := ⟨hL.1, hL.2, hT.trans hbc⟩
      have hleft : y ∈ {z | X z ∈ S ∧ T z ∈ Ioo a b} := ⟨hL.1, hL.2, hT⟩
      simp only [indicator_of_mem hfull, if_pos hT, indicator_of_mem hleft,
        indicator_of_notMem hnotR, add_zero]
    · have hnotFull : y ∉ {z | X z ∈ S ∧ T z ∈ Ioo a c} := fun h => hL ⟨h.1, h.2.1⟩
      have hnotLeft : y ∉ {z | X z ∈ S ∧ T z ∈ Ioo a b} := fun h => hL ⟨h.1, h.2.1⟩
      simp only [indicator_of_notMem hnotFull, indicator_of_notMem hnotLeft,
        indicator_of_notMem hnotR, add_zero]
  · have hgt : b < T y := lt_of_le_of_ne (le_of_not_gt hT) hy.symm
    have hnotL : y ∉ {z | X z ∈ S ∧ T z ∈ Ioo a b} := fun h => hT h.2.2
    by_cases hR : X y ∈ S ∧ T y < c
    · have hfull : y ∈ {z | X z ∈ S ∧ T z ∈ Ioo a c} := ⟨hR.1, hab.trans hgt, hR.2⟩
      have hright : y ∈ {z | X z ∈ S ∧ T z ∈ Ioo b c} := ⟨hR.1, hgt, hR.2⟩
      simp only [indicator_of_mem hfull, if_neg hT, indicator_of_notMem hnotL,
        indicator_of_mem hright, zero_add]
    · have hnotFull : y ∉ {z | X z ∈ S ∧ T z ∈ Ioo a c} := fun h => hR ⟨h.1, h.2.2⟩
      have hnotRight : y ∉ {z | X z ∈ S ∧ T z ∈ Ioo b c} := fun h => hR ⟨h.1, h.2.2⟩
      simp only [indicator_of_notMem hnotFull, indicator_of_notMem hnotL,
        indicator_of_notMem hnotRight, zero_add]

/-- Two original L2 fields on adjacent native rectangles give the literal
whole-rectangle piecewise L2 field. -/
theorem memLp_coordinate_rectangle_piecewise {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (u v : Domain (n + 1) → E) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    MemLp u 2 (volume.restrict {y | X y ∈ S ∧ T y ∈ Ioo a b}) →
    MemLp v 2 (volume.restrict {y | X y ∈ S ∧ T y ∈ Ioo b c}) →
    MemLp (fun y => if T y < b then u y else v y) 2
      (volume.restrict {y | X y ∈ S ∧ T y ∈ Ioo a c}) := by
  intro e X T hu hv
  have hMeas (d e' : ℝ) : MeasurableSet {y : Domain (n + 1) | X y ∈ S ∧ T y ∈ Ioo d e'} :=
    (hS.preimage (continuous_fst.comp e.continuous).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous)).measurable)
  have hleft := (memLp_indicator_iff_restrict (hMeas a b)).mpr hu
  have hright := (memLp_indicator_iff_restrict (hMeas b c)).mpr hv
  exact (memLp_indicator_iff_restrict (hMeas a c)).mp
    ((hleft.add hright).ae_eq (coordinate_rectangle_piecewise_indicator_ae S hab hbc u v).symm)

/-- The literal adjacent split retains the exact additive native integral. -/
theorem integral_coordinate_rectangle_piecewise {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set (Domain n)} (hS : MeasurableSet S)
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (u v : Domain (n + 1) → E) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    IntegrableOn u {y | X y ∈ S ∧ T y ∈ Ioo a b} volume →
    IntegrableOn v {y | X y ∈ S ∧ T y ∈ Ioo b c} volume →
    (∫ y in {z | X z ∈ S ∧ T z ∈ Ioo a c}, if T y < b then u y else v y) =
      (∫ y in {z | X z ∈ S ∧ T z ∈ Ioo a b}, u y) +
        ∫ y in {z | X z ∈ S ∧ T z ∈ Ioo b c}, v y := by
  intro e X T hu hv
  have hMeas (d e' : ℝ) : MeasurableSet {y : Domain (n + 1) | X y ∈ S ∧ T y ∈ Ioo d e'} :=
    (hS.preimage (continuous_fst.comp e.continuous).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous)).measurable)
  rw [← integral_indicator (hMeas a c),
    integral_congr_ae (coordinate_rectangle_piecewise_indicator_ae S hab hbc u v),
    integral_add ((integrable_indicator_iff (hMeas a b)).mpr hu)
      ((integrable_indicator_iff (hMeas b c)).mpr hv),
    integral_indicator (hMeas a b), integral_indicator (hMeas b c)]

/-- Actual inverse rectangle coordinates preserve native volume as the
original restricted spatial-time product volume. -/
theorem measurePreserving_inverse_native_rectangle {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MeasurePreserving (fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
      ((volume.restrict S).prod (volume.restrict J))
      (volume.restrict {y : Domain (n + 1) | (e y).1 ∈ S ∧ (e y).2 0 ∈ J}) := by
  intro e
  let Ω := {y : Domain (n + 1) | (e y).1 ∈ S ∧ (e y).2 0 ∈ J}
  have hΩ : MeasurableSet Ω :=
    (hS.preimage (continuous_fst.comp e.continuous).measurable).inter
      (hJ.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous)).measurable)
  have hMP := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage hΩ
  have hpre : (fun p : Domain n × ℝ =>
      e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)) ⁻¹' Ω = S ×ˢ J := by
    ext p
    simp only [Ω, mem_preimage, mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply,
      PiLp.single_apply, ite_true, mem_prod]
  rw [hpre, ← Measure.prod_restrict] at hMP
  exact hMP

/-- Fubini in the actual native rectangle uses the original raw fields and
has unit Jacobian. -/
theorem integral_native_rectangle {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := {y : Domain (n + 1) | (e y).1 ∈ S ∧ (e y).2 0 ∈ J}
    ∀ {f : Domain (n + 1) → E}, IntegrableOn f Ω volume →
      (∫ y in Ω, f y) = ∫ t in J, ∫ x in S,
        f (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) := by
  intro e Ω f hf
  let P : Domain n × ℝ → Domain (n + 1) := fun p =>
    e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  have hMP := measurePreserving_inverse_native_rectangle hS hJ
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let A := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Domain n))
    τ.symm).trans e.symm
  have hsingle (t : ℝ) : τ.symm t = EuclideanSpace.single (0 : Fin 1) t := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  have hAP : (A : Domain n × ℝ → Domain (n + 1)) = P := by
    funext p
    change e.symm (p.1, τ.symm p.2) = e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
    rw [hsingle]
  have hPE : MeasurableEmbedding P := by
    rw [← hAP]
    exact A.toHomeomorph.measurableEmbedding
  have hFI : Integrable (f ∘ P) ((volume.restrict S).prod (volume.restrict J)) :=
    hMP.integrable_comp_of_integrable hf
  exact (hMP.integral_comp hPE f).symm.trans (integral_prod_symm _ hFI)

end StratificationTheory
