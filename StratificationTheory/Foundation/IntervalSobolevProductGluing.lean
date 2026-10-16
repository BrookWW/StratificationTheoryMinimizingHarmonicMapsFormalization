module

public import StratificationTheory.Foundation.IntervalSobolevProductBase
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Adjacent interval data with a common endpoint value

Piecewise original Lp data retain their native classes and integrals on the
combined interval. Matching endpoint values glue exact integral increments
across the cut, without assuming a weak identity for the glued map.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

private theorem restrict_adjacent_interval_parts {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    ((volume : Measure ℝ).restrict (Ioo a c)).restrict (Iic b) = volume.restrict (Ioo a b) ∧
    ((volume : Measure ℝ).restrict (Ioo a c)).restrict (Iic b)ᶜ = volume.restrict (Ioo b c) := by
  constructor
  · rw [Measure.restrict_restrict measurableSet_Iic]
    have hs : Iic b ∩ Ioo a c = Ioc a b := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.2.1, hx.1⟩
      · intro hx
        exact ⟨hx.2, hx.1, hx.2.trans_lt hbc⟩
    rw [hs]
    exact Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  · rw [Measure.restrict_restrict measurableSet_Iic.compl]
    have hs : (Iic b)ᶜ ∩ Ioo a c = Ioo b c := by
      ext x
      constructor
      · intro hx
        exact ⟨lt_of_not_ge hx.1, hx.2.2⟩
      · intro hx
        exact ⟨not_le_of_gt hx.1, hab.trans hx.1, hx.2⟩
    rw [hs]

/-- Adjacent original Lp functions give a finite piecewise Lp function on the
whole interval, with no boundedness or matching-value premise. -/
theorem memLp_piecewise_adjacent_intervals {E : Type*} [NormedAddCommGroup E]
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {p : ℝ≥0∞} {f g : ℝ → E}
    (hf : MemLp f p (volume.restrict (Ioo a b)))
    (hg : MemLp g p (volume.restrict (Ioo b c))) :
    MemLp ((Iic b).piecewise f g) p (volume.restrict (Ioo a c)) := by
  obtain ⟨hleft, hright⟩ := restrict_adjacent_interval_parts hab hbc
  apply MemLp.piecewise measurableSet_Iic
  · rw [hleft]
    exact hf
  · rw [hright]
    exact hg

/-- Native a.e. identifications on both adjacent intervals give the a.e.
identification of their piecewise maps on the combined interval. -/
theorem ae_eq_piecewise_adjacent_intervals {E : Type*}
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {F G f g : ℝ → E}
    (hF : F =ᵐ[volume.restrict (Ioo a b)] f)
    (hG : G =ᵐ[volume.restrict (Ioo b c)] g) :
    (Iic b).piecewise F G =ᵐ[volume.restrict (Ioo a c)] (Iic b).piecewise f g := by
  obtain ⟨hleft, hright⟩ := restrict_adjacent_interval_parts hab hbc
  apply ae_of_ae_restrict_of_ae_restrict_compl (Iic b)
  · have hFl : F =ᵐ[(volume.restrict (Ioo a c)).restrict (Iic b)] f := by
      rw [hleft]
      exact hF
    filter_upwards [hFl, ae_restrict_mem measurableSet_Iic] with x hx hxI
    simpa only [Set.piecewise_eq_of_mem (Iic b) F G hxI,
      Set.piecewise_eq_of_mem (Iic b) f g hxI] using hx
  · have hGr : G =ᵐ[(volume.restrict (Ioo a c)).restrict (Iic b)ᶜ] g := by
      rw [hright]
      exact hG
    filter_upwards [hGr, ae_restrict_mem measurableSet_Iic.compl] with x hx hxI
    simpa only [Set.piecewise_eq_of_notMem (Iic b) F G hxI,
      Set.piecewise_eq_of_notMem (Iic b) f g hxI] using hx

/-- The actual piecewise Bochner integral is the sum of the two original
interval integrals; the common cut contributes no atom. -/
theorem integral_piecewise_adjacent_intervals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {f g : ℝ → E}
    (hf : IntegrableOn f (Ioo a b) volume) (hg : IntegrableOn g (Ioo b c) volume) :
    (∫ x in Ioo a c, (Iic b).piecewise f g x) =
      (∫ x in Ioo a b, f x) + ∫ x in Ioo b c, g x := by
  obtain ⟨hleft, hright⟩ := restrict_adjacent_interval_parts hab hbc
  have hf' : IntegrableOn f (Iic b) (volume.restrict (Ioo a c)) := by
    change Integrable f ((volume.restrict (Ioo a c)).restrict (Iic b))
    rw [hleft]
    exact hf
  have hg' : IntegrableOn g (Iic b)ᶜ (volume.restrict (Ioo a c)) := by
    change Integrable g ((volume.restrict (Ioo a c)).restrict (Iic b)ᶜ)
    rw [hright]
    exact hg
  simpa only [hleft, hright] using integral_piecewise measurableSet_Iic hf' hg'

/-- Matching endpoint values and original L2 derivative data produce the
exact oriented integral increments of the actual piecewise representative on
the whole closed interval. -/
theorem interval_piecewise_integral_increments {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {F G g k : ℝ → E}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hk : MemLp k 2 (volume.restrict (Ioo b c))) (hmatch : F b = G b)
    (hFinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y)
    (hGinc : ∀ s ∈ Icc b c, ∀ t ∈ Icc b c,
      G t - G s = ∫ y in s..t, k y) :
    let H := (Iic b).piecewise F G
    let D := (Iic b).piecewise g k
    ∀ s ∈ Icc a c, ∀ t ∈ Icc a c, H t - H s = ∫ y in s..t, D y := by
  intro H D
  have hac : a < c := hab.trans hbc
  have hD : MemLp D 2 (volume.restrict (Ioo a c)) :=
    memLp_piecewise_adjacent_intervals hab hbc hg hk
  have hi := intervalIntegrable_of_memLp_two hac.le hD
  have hleft (s : ℝ) (hs : s ∈ Icc a b) : (∫ y in a..s, D y) = ∫ y in a..s, g y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hs.1] at hy
    exact Set.piecewise_eq_of_mem (Iic b) g k (hy.2.trans hs.2)
  have hformula : ∀ s ∈ Icc a c, H s = F a + ∫ y in a..s, D y := by
    intro s hs
    by_cases hsb : s ≤ b
    · have hsL : s ∈ Icc a b := ⟨hs.1, hsb⟩
      rw [show H s = F s from Set.piecewise_eq_of_mem (Iic b) F G hsb, hleft s hsL]
      exact (sub_eq_iff_eq_add.mp (hFinc a ⟨le_rfl, hab.le⟩ s hsL)).trans (add_comm _ _)
    · have hbs : b < s := lt_of_not_ge hsb
      have hright : (∫ y in b..s, D y) = ∫ y in b..s, k y := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with y hy
        rw [uIoc_of_le hbs.le] at hy
        exact Set.piecewise_eq_of_notMem (Iic b) g k (not_le_of_gt hy.1)
      have hiab : IntervalIntegrable D volume a b := by
        apply hi.mono_set
        rw [uIcc_of_le hac.le]
        exact uIcc_subset_Icc ⟨le_rfl, hac.le⟩ ⟨hab.le, hbc.le⟩
      have hibs : IntervalIntegrable D volume b s := by
        apply hi.mono_set
        rw [uIcc_of_le hac.le]
        exact uIcc_subset_Icc ⟨hab.le, hbc.le⟩ hs
      have hsum := intervalIntegral.integral_add_adjacent_intervals hiab hibs
      have hFL := hFinc a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
      have hGR := hGinc b ⟨le_rfl, hbc.le⟩ s ⟨hbs.le, hs.2⟩
      rw [← hmatch] at hGR
      rw [show H s = G s from Set.piecewise_eq_of_notMem (Iic b) F G hsb, ← hsum,
        hleft b ⟨hab.le, le_rfl⟩, hright]
      rw [← hFL, ← hGR]
      abel
  intro s hs t ht
  rw [hformula s hs, hformula t ht, add_sub_add_left_eq_sub]
  exact intervalPrimitive_sub hac.le hD hs ht

/-- Finite original derivative data and exact closed-interval increments
make that same representative continuous through both endpoints. -/
theorem continuousOn_interval_of_integral_increments {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a ≤ b) {F g : ℝ → E}
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      F t - F s = ∫ y in s..t, g y) : ContinuousOn F (Icc a b) := by
  have hprimitive : ContinuousOn (fun x => ∫ y in a..x, g y) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (intervalPrimitive_absolutelyContinuous (intervalIntegrable_of_memLp_two hab hg)
        left_mem_uIcc).continuousOn
  apply (continuousOn_const.add hprimitive).congr
  intro x hx
  exact (sub_eq_iff_eq_add.mp (hinc a ⟨le_rfl, hab⟩ x hx)).trans (add_comm _ _)

end StratificationTheory
