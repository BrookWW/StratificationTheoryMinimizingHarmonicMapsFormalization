module

public import StratificationTheory.Foundation.CoordinateGridCompatibility
public import StratificationTheory.Foundation.TranslatedGridSampling
public import HarmonicMaps.EnergyLemmas
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Simultaneous energy bounds for every coordinate grid direction

Integrating each length-epsilon edge over all origins gives epsilon times
the original Euclidean integral. A single full-dimensional grid offset
therefore controls all coordinate edges for both densities.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
namespace StratificationTheory

/-- The actual integral density of one coordinate edge of length epsilon. -/
@[expose] noncomputable def gridEdgeDensity {N : ℕ} (ε : ℝ)
    (f : Domain N → ℝ≥0∞) (i : Fin N) (x : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ico (0 : ℝ) ε,
    f (WithLp.toLp 2 (x + t • Pi.single i (1 : ℝ)))

private theorem lintegral_comp_of_aemeasurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {h : α → β} (hh : MeasurePreserving h μ ν)
    {f : β → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (∫⁻ x, f (h x) ∂μ) = ∫⁻ y, f y ∂ν := by
  calc
    _ = ∫⁻ x, hf.mk f (h x) ∂μ :=
      lintegral_congr_ae (hh.quasiMeasurePreserving.ae hf.ae_eq_mk)
    _ = ∫⁻ y, hf.mk f y ∂ν := hh.lintegral_comp hf.measurable_mk
    _ = _ := (lintegral_congr_ae hf.ae_eq_mk).symm

/-- Integrating the actual edge density over all origins gives exactly
epsilon times the original density integral. -/
theorem gridEdgeDensity_aemeasurable_and_lintegral {N : ℕ} {ε : ℝ} (_hε : 0 < ε)
    {f : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume) (i : Fin N) :
    AEMeasurable (gridEdgeDensity ε f i) volume ∧
      (∫⁻ x, gridEdgeDensity ε f i x) = ENNReal.ofReal ε * ∫⁻ y, f y := by
  let ν := (volume : Measure ℝ).restrict (Ico (0 : ℝ) ε)
  let T : (Fin N → ℝ) × ℝ → (Fin N → ℝ) := fun p => p.1 + p.2 • Pi.single i 1
  have hT : Measure.QuasiMeasurePreserving T
      ((volume : Measure (Fin N → ℝ)).prod ν) volume :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_left (by fun_prop)
      (Eventually.of_forall fun t =>
        (measurePreserving_add_right volume (t • Pi.single i (1 : ℝ))).quasiMeasurePreserving)
  have hmap := (PiLp.volume_preserving_toLp (Fin N)).quasiMeasurePreserving.comp hT
  have hprod : AEMeasurable (fun p : (Fin N → ℝ) × ℝ =>
      f (WithLp.toLp 2 (T p))) ((volume : Measure (Fin N → ℝ)).prod ν) :=
    hf.comp_quasiMeasurePreserving hmap
  refine ⟨hprod.lintegral_prod_right', ?_⟩
  change (∫⁻ x, ∫⁻ t, f (WithLp.toLp 2 (T (x, t))) ∂ν) = _
  rw [lintegral_lintegral_swap hprod]
  have hfixed (t : ℝ) : (∫⁻ x, f (WithLp.toLp 2 (T (x, t)))) = ∫⁻ y, f y := by
    have htrans := (PiLp.volume_preserving_toLp (Fin N)).comp
      (measurePreserving_add_right volume (t • Pi.single i (1 : ℝ)))
    exact lintegral_comp_of_aemeasurable htrans hf
  simp_rw [hfixed]
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero, mul_comm]

/-- All coordinate edge densities have the joint exact mean, with one
factor equal to the number of coordinate directions. -/
theorem fullGridEdgeDensity_aemeasurable_and_lintegral {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume) :
    AEMeasurable (fun x => ∑ i : Fin N, gridEdgeDensity ε f i x) volume ∧
      (∫⁻ x, ∑ i : Fin N, gridEdgeDensity ε f i x) =
        N * ENNReal.ofReal ε * ∫⁻ y, f y := by
  have hi := gridEdgeDensity_aemeasurable_and_lintegral hε hf
  refine ⟨?_, ?_⟩
  · exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ => (hi i).1)
  · rw [lintegral_finsetSum' Finset.univ (fun i _ => (hi i).1)]
    simp_rw [(hi _).2]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- One full-dimensional grid offset controls every coordinate edge for two
finite densities and preserves the same a.e. property at every grid vertex. -/
theorem exists_full_grid_translate_pair_energy {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f g : Domain (n + 1) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume)
    (hfFinite : (∫⁻ y, f y) ≠ ⊤) (hgFinite : (∫⁻ y, g y) ≠ ⊤)
    {P : Domain (n + 1) → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    let basis := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul (fun _ => hε.ne'.isUnit)
    ∃ offset : Fin (n + 1) → ℝ,
      (∀ i, offset i ∈ Ico (0 : ℝ) ε) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        P (WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset))) ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), gridEdgeDensity ε f i ((l : Fin (n + 1) → ℝ) + offset)) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ * ∫⁻ y, f y ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), gridEdgeDensity ε g i ((l : Fin (n + 1) → ℝ) + offset)) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ * ∫⁻ y, g y := by
  intro basis
  let F := fun x => ∑ i : Fin (n + 1), gridEdgeDensity ε f i x
  let G := fun x => ∑ i : Fin (n + 1), gridEdgeDensity ε g i x
  obtain ⟨hF, hFI⟩ := fullGridEdgeDensity_aemeasurable_and_lintegral hε hf
  obtain ⟨hG, hGI⟩ := fullGridEdgeDensity_aemeasurable_and_lintegral hε hg
  have hFfinite : (∫⁻ x, F x) ≠ ⊤ := by
    rw [hFI]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top) hfFinite
  have hGfinite : (∫⁻ x, G x) ≠ ⊤ := by
    rw [hGI]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top) hgFinite
  have hPpi := (PiLp.volume_preserving_toLp (Fin (n + 1))).quasiMeasurePreserving.ae hP
  obtain ⟨offset, ho, hPo, hFo, hGo⟩ := exists_grid_translate_pair_tsum_le hε hF hG
    hFfinite hGfinite hPpi
  have hcoeff : 2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
      ((n + 1) * ENNReal.ofReal ε) =
      (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ := by
    rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg hε.le n),
      ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
    have hcancel : (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal ε = 1 :=
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
    calc
      _ = (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ *
          ((ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal ε) := by ac_rfl
      _ = _ := by rw [hcancel, mul_one]
  refine ⟨offset, ho, hPo, ?_, ?_⟩
  · simp only [Nat.cast_add, Nat.cast_one] at hFI
    rw [hFI, ← mul_assoc, hcoeff] at hFo
    exact hFo
  · simp only [Nat.cast_add, Nat.cast_one] at hGI
    rw [hGI, ← mul_assoc, hcoeff] at hGo
    exact hGo

end StratificationTheory
