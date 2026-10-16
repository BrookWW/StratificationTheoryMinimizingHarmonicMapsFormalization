module

public import StratificationTheory.Foundation.IntervalWeakRepresentative
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Original Sobolev line data on a translated subinterval

Finite original Lp classes and a.e. identities pull back to a contained
translated interval under the actual measure-preserving translation.
The original integral increments retain their orientation and derivative.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original L2 derivative increments imply absolute continuity on the
whole closed interval, without a separate regularity qualification. -/
theorem absolutelyContinuousOnInterval_of_integral_increments {q : ℕ}
    {a b : ℝ} (hab : a ≤ b) {F g : ℝ → Ambient q}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F t - F s = ∫ y in s..t, g y) :
    AbsolutelyContinuousOnInterval F a b := by
  have hp := intervalPrimitive_absolutelyContinuous_of_memLp_two hab hg
  rw [absolutelyContinuousOnInterval_iff] at hp ⊢
  intro δ hδ
  obtain ⟨η, hη, hηbound⟩ := hp δ hδ
  refine ⟨η, hη, ?_⟩
  intro J hJ hsmall
  have hends : ∀ i ∈ Finset.range J.1,
      (J.2 i).1 ∈ Icc a b ∧ (J.2 i).2 ∈ Icc a b := by
    simpa only [uIcc_of_le hab] using hJ.1
  have heq : (∑ i ∈ Finset.range J.1, dist (F (J.2 i).1) (F (J.2 i).2)) =
      ∑ i ∈ Finset.range J.1,
        dist (∫ y in a..(J.2 i).1, g y) (∫ y in a..(J.2 i).2, g y) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [dist_eq_norm, dist_eq_norm,
      hinc _ (hends i hi).2 _ (hends i hi).1,
      intervalPrimitive_sub hab hg (hends i hi).2 (hends i hi).1]
  rw [heq]
  exact hηbound J hJ hsmall

private theorem interval_translation_preimage (t₀ ε : ℝ) :
    (fun t : ℝ => t₀ + t) ⁻¹' Ioo t₀ (t₀ + ε) = Ioo (0 : ℝ) ε := by
  ext t
  simp only [mem_preimage, mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]

/-- Restricting an original finite Lp function and translating its real
parameter gives the actual finite class on the positive interval. -/
theorem memLp_translated_subinterval {E : Type*} [NormedAddCommGroup E]
    {a b t₀ ε : ℝ} (ha : a ≤ t₀) (hb : t₀ + ε ≤ b) {p : ℝ≥0∞}
    {f : ℝ → E} (hf : MemLp f p (volume.restrict (Ioo a b))) :
    MemLp (fun t => f (t₀ + t)) p (volume.restrict (Ioo (0 : ℝ) ε)) := by
  have hsub : Ioo t₀ (t₀ + ε) ⊆ Ioo a b := by
    intro t ht
    exact ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  have hsmall : MemLp f p (volume.restrict (Ioo t₀ (t₀ + ε))) :=
    hf.mono_measure (Measure.restrict_mono_set volume hsub)
  have hm := (measurePreserving_add_left (volume : Measure ℝ) t₀).restrict_preimage
    (measurableSet_Ioo (a := t₀) (b := t₀ + ε))
  rw [interval_translation_preimage] at hm
  exact hsmall.comp_measurePreserving hm

/-- Every original a.e. property pulls back on the same contained
translated interval; no pointwise representative substitution is used. -/
theorem ae_translated_subinterval {a b t₀ ε : ℝ}
    (ha : a ≤ t₀) (hb : t₀ + ε ≤ b) {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Ioo a b), P t) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) ε), P (t₀ + t) := by
  have hsub : Ioo t₀ (t₀ + ε) ⊆ Ioo a b := by
    intro t ht
    exact ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  have hsmall : ∀ᵐ t ∂volume.restrict (Ioo t₀ (t₀ + ε)), P t :=
    hP.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  have hm := (measurePreserving_add_left (volume : Measure ℝ) t₀).restrict_preimage
    (measurableSet_Ioo (a := t₀) (b := t₀ + ε))
  rw [interval_translation_preimage] at hm
  exact hm.quasiMeasurePreserving.ae hsmall

/-- The same original weak derivative supplies every oriented increment
of the translated closed-line representative. -/
theorem integral_increments_translated_subinterval {q : ℕ} {a b t₀ ε : ℝ}
    (ha : a ≤ t₀) (hb : t₀ + ε ≤ b) {F g : ℝ → Ambient q}
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, F t - F s = ∫ y in s..t, g y) :
    ∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
      F (t₀ + t) - F (t₀ + s) = ∫ y in s..t, g (t₀ + y) := by
  intro s hs t ht
  have hs' : t₀ + s ∈ Icc a b := ⟨by linarith only [ha, hs.1], by linarith only [hb, hs.2]⟩
  have ht' : t₀ + t ∈ Icc a b := ⟨by linarith only [ha, ht.1], by linarith only [hb, ht.2]⟩
  rw [hinc _ hs' _ ht', intervalIntegral.integral_comp_add_left]

end StratificationTheory
