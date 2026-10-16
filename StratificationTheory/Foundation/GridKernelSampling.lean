module

public import StratificationTheory.Foundation.TranslatedGridSampling
public import HarmonicMaps.EnergyLemmas
import Mathlib.MeasureTheory.Integral.Prod

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
namespace StratificationTheory

private theorem lintegral_comp_of_aemeasurable_kernel {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {h : α → β} (hh : MeasurePreserving h μ ν)
    {f : β → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (∫⁻ x, f (h x) ∂μ) = ∫⁻ y, f y ∂ν := by
  calc
    _ = ∫⁻ x, hf.mk f (h x) ∂μ :=
      lintegral_congr_ae (hh.quasiMeasurePreserving.ae hf.ae_eq_mk)
    _ = ∫⁻ y, hf.mk f y ∂ν := hh.lintegral_comp hf.measurable_mk
    _ = _ := (lintegral_congr_ae hf.ae_eq_mk).symm

theorem translated_kernel_density_aemeasurable_and_lintegral {N : ℕ}
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (shift : α → (Fin N → ℝ)) (hshift : Measurable shift)
    {f : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume) :
    AEMeasurable (fun x : Fin N → ℝ =>
      ∫⁻ t, f (WithLp.toLp 2 (x + shift t)) ∂ν) volume ∧
      (∫⁻ x : Fin N → ℝ, ∫⁻ t, f (WithLp.toLp 2 (x + shift t)) ∂ν) =
        ν univ * ∫⁻ y, f y := by
  let T : (Fin N → ℝ) × α → (Fin N → ℝ) := fun p => p.1 + shift p.2
  have hT : Measure.QuasiMeasurePreserving T
      ((volume : Measure (Fin N → ℝ)).prod ν) volume :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (hshift.comp measurable_snd))
      (Eventually.of_forall fun t =>
        (measurePreserving_add_right volume (shift t)).quasiMeasurePreserving)
  have hmap := (PiLp.volume_preserving_toLp (Fin N)).quasiMeasurePreserving.comp hT
  have hprod : AEMeasurable (fun p : (Fin N → ℝ) × α =>
      f (WithLp.toLp 2 (T p))) ((volume : Measure (Fin N → ℝ)).prod ν) :=
    hf.comp_quasiMeasurePreserving hmap
  refine ⟨hprod.lintegral_prod_right', ?_⟩
  change (∫⁻ x, ∫⁻ t, f (WithLp.toLp 2 (T (x, t))) ∂ν) = _
  rw [lintegral_lintegral_swap hprod]
  have hfixed (t : α) : (∫⁻ x, f (WithLp.toLp 2 (T (x, t)))) = ∫⁻ y, f y :=
    lintegral_comp_of_aemeasurable_kernel
      ((PiLp.volume_preserving_toLp (Fin N)).comp (measurePreserving_add_right volume (shift t))) hf
  simp_rw [hfixed]
  rw [lintegral_const, mul_comm]

/-- A raw almost-everywhere property survives almost every translated kernel
fiber, without requiring measurability of the predicate. -/
theorem ae_translated_kernel_property {N : ℕ}
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (shift : α → (Fin N → ℝ)) (hshift : Measurable shift)
    {P : Domain N → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x : Fin N → ℝ ∂volume, ∀ᵐ t ∂ν,
      P (WithLp.toLp 2 (x + shift t)) := by
  let T : (Fin N → ℝ) × α → (Fin N → ℝ) := fun p => p.1 + shift p.2
  have hT : Measure.QuasiMeasurePreserving T
      ((volume : Measure (Fin N → ℝ)).prod ν) volume :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (hshift.comp measurable_snd))
      (Eventually.of_forall fun t =>
        (measurePreserving_add_right volume (shift t)).quasiMeasurePreserving)
  have hmap := (PiLp.volume_preserving_toLp (Fin N)).quasiMeasurePreserving.comp hT
  exact Measure.ae_ae_of_ae_prod (hmap.ae hP)

theorem translated_kernel_family_density_aemeasurable_and_lintegral
    {N : ℕ} {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, SFinite (ν i)]
    (shift : ∀ i, α i → (Fin N → ℝ)) (hshift : ∀ i, Measurable (shift i))
    (weights : ι → ℝ≥0∞) {f : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume) :
    AEMeasurable (fun x : Fin N → ℝ => ∑ i : ι,
      weights i * ∫⁻ t, f (WithLp.toLp 2 (x + shift i t)) ∂ν i) volume ∧
      (∫⁻ x : Fin N → ℝ, ∑ i : ι,
        weights i * ∫⁻ t, f (WithLp.toLp 2 (x + shift i t)) ∂ν i) =
        (∑ i : ι, weights i * ν i univ) * ∫⁻ y, f y := by
  have hi (i : ι) := translated_kernel_density_aemeasurable_and_lintegral (ν i) (shift i) (hshift i) hf
  have hterm (i : ι) : AEMeasurable (fun x : Fin N → ℝ =>
      weights i * ∫⁻ t, f (WithLp.toLp 2 (x + shift i t)) ∂ν i) volume :=
    aemeasurable_const.mul (hi i).1
  refine ⟨Finset.aemeasurable_fun_sum Finset.univ (fun i _ => hterm i), ?_⟩
  rw [lintegral_finsetSum' Finset.univ (fun i _ => hterm i)]
  calc
    _ = ∑ i : ι, weights i * (ν i univ * ∫⁻ y, f y) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_const_mul'' _ (hi i).1, (hi i).2]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc _ _ _).symm

/-- One offset controls two densities for every member of a finite family of
translated kernels. The bound uses the total weighted kernel mass. -/
theorem exists_grid_translate_kernel_family_pair_tsum_le
    {N : ℕ} {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, SFinite (ν i)]
    (shift : ∀ i, α i → (Fin N → ℝ)) (hshift : ∀ i, Measurable (shift i))
    (weights : ι → ℝ≥0∞) (hMass : (∑ i : ι, weights i * ν i univ) ≠ ⊤)
    {f g : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hfFinite : (∫⁻ x, f x) ≠ ⊤)
    (hgFinite : (∫⁻ x, g x) ≠ ⊤)
    {P : Domain N → Prop} (hP : ∀ᵐ x ∂volume, P x)
    {ε : ℝ} (hε : 0 < ε) :
    let b := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _i : Fin N => ε) (fun _i => hε.ne'.isUnit)
    let M := ∑ i : ι, weights i * ν i univ
    ∃ a : Fin N → ℝ,
      (∀ j, a j ∈ Ico (0 : ℝ) ε) ∧
      (∀ z : Submodule.span ℤ (Set.range b),
        P (WithLp.toLp 2 ((z : Fin N → ℝ) + a))) ∧
      (∀ (i : ι) (z : Submodule.span ℤ (Set.range b)), ∀ᵐ t ∂ν i,
        P (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t))) ∧
      (∑' z : Submodule.span ℤ (Set.range b), ∑ i : ι,
        weights i * ∫⁻ t, f (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t)) ∂ν i) ≤
          2 * (ENNReal.ofReal (ε ^ N))⁻¹ * (M * ∫⁻ x, f x) ∧
      (∑' z : Submodule.span ℤ (Set.range b), ∑ i : ι,
        weights i * ∫⁻ t, g (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t)) ∂ν i) ≤
          2 * (ENNReal.ofReal (ε ^ N))⁻¹ * (M * ∫⁻ x, g x) ∧
      (∀ i : ι, weights i *
        (∑' z : Submodule.span ℤ (Set.range b),
          ∫⁻ t, f (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t)) ∂ν i) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ * (M * ∫⁻ x, f x)) ∧
      (∀ i : ι, weights i *
        (∑' z : Submodule.span ℤ (Set.range b),
          ∫⁻ t, g (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t)) ∂ν i) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ * (M * ∫⁻ x, g x)) := by
  intro b M
  have hF := translated_kernel_family_density_aemeasurable_and_lintegral ν shift hshift weights hf
  have hG := translated_kernel_family_density_aemeasurable_and_lintegral ν shift hshift weights hg
  have hFtop : (∫⁻ x : Fin N → ℝ, ∑ i : ι,
      weights i * ∫⁻ t, f (WithLp.toLp 2 (x + shift i t)) ∂ν i) ≠ ⊤ := by
    rw [hF.2]
    exact ENNReal.mul_ne_top hMass hfFinite
  have hGtop : (∫⁻ x : Fin N → ℝ, ∑ i : ι,
      weights i * ∫⁻ t, g (WithLp.toLp 2 (x + shift i t)) ∂ν i) ≠ ⊤ := by
    rw [hG.2]
    exact ENNReal.mul_ne_top hMass hgFinite
  have hP' : ∀ᵐ x : Fin N → ℝ ∂volume, P (WithLp.toLp 2 x) :=
    (PiLp.volume_preserving_toLp (Fin N)).quasiMeasurePreserving.ae hP
  have hPK : ∀ᵐ x : Fin N → ℝ ∂volume, ∀ i : ι, ∀ᵐ t ∂ν i,
      P (WithLp.toLp 2 (x + shift i t)) :=
    ae_all_iff.mpr fun i => ae_translated_kernel_property (ν i) (shift i) (hshift i) hP
  obtain ⟨a, ha, hPa, hfa, hga⟩ :=
    exists_grid_translate_pair_tsum_le hε hF.1 hG.1 hFtop hGtop (hP'.and hPK)
  rw [hF.2] at hfa
  rw [hG.2] at hga
  refine ⟨a, ha, fun z => (hPa z).1, fun i z => (hPa z).2 i, hfa, hga, ?_, ?_⟩
  · intro i
    rw [← ENNReal.tsum_mul_left]
    apply le_trans (ENNReal.tsum_le_tsum (fun z => ?_)) hfa
    exact Finset.single_le_sum (fun j _ => show (0 : ℝ≥0∞) ≤ weights j *
      ∫⁻ t, f (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) ∂ν j from zero_le)
      (Finset.mem_univ i)
  · intro i
    rw [← ENNReal.tsum_mul_left]
    apply le_trans (ENNReal.tsum_le_tsum (fun z => ?_)) hga
    exact Finset.single_le_sum (fun j _ => show (0 : ℝ≥0∞) ≤ weights j *
      ∫⁻ t, g (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) ∂ν j from zero_le)
      (Finset.mem_univ i)

end StratificationTheory
