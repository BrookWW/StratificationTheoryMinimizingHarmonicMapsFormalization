module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Quantitative sampling on a translated cubical lattice

Fundamental-domain integration gives the exact inverse-cell-volume factor.
Two finite densities share one offset, their own bounds with constant two,
and all prescribed translated almost-everywhere constraints.
-/

public section
open MeasureTheory Metric Set Filter Module
open scoped ENNReal Pointwise
namespace StratificationTheory

private theorem exists_lattice_translate_tsum_le {m : ℕ}
    (b : Basis (Fin m) ℝ (Fin m → ℝ))
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : AEMeasurable f volume)
    {P : (Fin m → ℝ) → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    ∃ a ∈ ZSpan.fundamentalDomain b,
      (∀ g : Submodule.span ℤ (Set.range b), P ((g : Fin m → ℝ) + a)) ∧
      (∑' g : Submodule.span ℤ (Set.range b), f ((g : Fin m → ℝ) + a)) ≤
        (volume (ZSpan.fundamentalDomain b))⁻¹ * ∫⁻ x, f x := by
  let L := Submodule.span ℤ (Set.range b)
  let Q := ZSpan.fundamentalDomain b
  letI : VAddInvariantMeasure L (Fin m → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure (Submodule.span ℤ (Set.range b)).toAddSubgroup
      (Fin m → ℝ) volume)
  let μ := (volume : Measure (Fin m → ℝ)).restrict Q
  have hQ := ZSpan.fundamentalDomain_measurableSet b
  have hQ0 : (volume : Measure (Fin m → ℝ)) Q ≠ 0 :=
    ZSpan.measure_fundamentalDomain_ne_zero b
  have hQtop : (volume : Measure (Fin m → ℝ)) Q ≠ ⊤ := by
    have hc : (volume : Measure (Fin m → ℝ)) (b.parallelepiped : Set (Fin m → ℝ)) ≠ ⊤ :=
      b.parallelepiped.isCompact.measure_ne_top
    apply ne_top_of_le_ne_top hc
    apply measure_mono
    exact ZSpan.fundamentalDomain_subset_parallelepiped b
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hQtop
  have hμ0 : μ ≠ 0 := by
    rw [ne_eq, Measure.restrict_eq_zero]
    exact hQ0
  let F : (Fin m → ℝ) → ℝ≥0∞ := fun a => ∑' g : L, f ((g : Fin m → ℝ) + a)
  have hg (g : L) : AEMeasurable (fun a => f ((g : Fin m → ℝ) + a)) μ :=
    (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_left volume (g : Fin m → ℝ)).quasiMeasurePreserving).restrict
  have hF : AEMeasurable F μ := AEMeasurable.tsum hg
  have hInt : (∫⁻ a, F a ∂μ) = ∫⁻ x, f x := by
    rw [lintegral_tsum hg]
    exact (ZSpan.isAddFundamentalDomain b volume).lintegral_eq_tsum'' f |>.symm
  have hPa : ∀ᵐ a ∂μ, a ∈ Q ∧ ∀ g : L, P ((g : Fin m → ℝ) + a) := by
    have hall : ∀ᵐ a ∂volume, ∀ g : L, P ((g : Fin m → ℝ) + a) :=
      ae_all_iff.mpr fun g =>
        (measurePreserving_add_left volume (g : Fin m → ℝ)).quasiMeasurePreserving.ae hP
    filter_upwards [ae_restrict_mem hQ, ae_restrict_of_ae hall] with a ha hga
    exact ⟨ha, hga⟩
  let N := {a | ¬(a ∈ Q ∧ ∀ g : L, P ((g : Fin m → ℝ) + a))}
  have hN : μ N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hPa] with a ha
    exact not_not.mpr ha
  obtain ⟨a, ha, hmean⟩ := exists_notMem_null_le_laverage hμ0 hF hN
  have ha' : a ∈ Q ∧ ∀ g : L, P ((g : Fin m → ℝ) + a) := not_not.mp ha
  refine ⟨a, ha'.1, ha'.2, ?_⟩
  rw [laverage_eq, hInt, Measure.restrict_apply_univ, div_eq_mul_inv, mul_comm] at hmean
  exact hmean

private theorem volume_scaled_grid_cell {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    let b := (Pi.basisFun ℝ (Fin m)).isUnitSMul (fun _ => hε.ne'.isUnit)
    (volume : Measure (Fin m → ℝ)) (ZSpan.fundamentalDomain b) =
      ENNReal.ofReal (ε ^ m) := by
  intro b
  have hm : Matrix.of b = Matrix.diagonal (fun _ : Fin m => ε) := by
    ext i j
    simp [Matrix.of_apply, b, Basis.isUnitSMul_apply, Pi.basisFun_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  rw [ZSpan.volume_fundamentalDomain, hm, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    abs_of_nonneg (pow_nonneg hε.le m)]

/-- One cubical grid offset controls the complete lattice sum and preserves
all translates of an almost-everywhere property. -/
theorem exists_grid_translate_tsum_le {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : AEMeasurable f volume)
    {P : (Fin m → ℝ) → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    let b := (Pi.basisFun ℝ (Fin m)).isUnitSMul (fun _ => hε.ne'.isUnit)
    ∃ a : Fin m → ℝ,
      (∀ i, a i ∈ Ico (0 : ℝ) ε) ∧
      (∀ g : Submodule.span ℤ (Set.range b), P ((g : Fin m → ℝ) + a)) ∧
      (∑' g : Submodule.span ℤ (Set.range b), f ((g : Fin m → ℝ) + a)) ≤
        (ENNReal.ofReal (ε ^ m))⁻¹ * ∫⁻ x, f x := by
  intro b
  obtain ⟨a, ha, hPa, hbound⟩ := exists_lattice_translate_tsum_le b hf hP
  refine ⟨a, ?_, hPa, ?_⟩
  · intro i
    have hi := (ZSpan.mem_fundamentalDomain b).mp ha i
    have hrepr : b.repr a i = ε⁻¹ * a i := by
      simp only [b, Basis.repr_isUnitSMul, Units.smul_def, IsUnit.unit_spec,
        Units.val_inv_eq_inv_val, Pi.basisFun_repr, smul_eq_mul]
    rw [hrepr] at hi
    constructor
    · exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hε)).mp hi.1
    · exact (inv_mul_lt_iff₀ hε).mp hi.2 |>.trans_eq (mul_one ε)
  · have hv : (volume : Measure (Fin m → ℝ)) (ZSpan.fundamentalDomain b) =
        ENNReal.ofReal (ε ^ m) := volume_scaled_grid_cell hε
    rwa [hv] at hbound


/-- Two finite nonnegative densities share one translated grid, their own
inverse-cell-volume bounds, and all translated a.e. constraints. -/
theorem exists_grid_translate_pair_tsum_le {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f g : (Fin m → ℝ) → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume)
    (hfFinite : (∫⁻ x, f x) ≠ ⊤) (hgFinite : (∫⁻ x, g x) ≠ ⊤)
    {P : (Fin m → ℝ) → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    let b := (Pi.basisFun ℝ (Fin m)).isUnitSMul (fun _ => hε.ne'.isUnit)
    ∃ a : Fin m → ℝ,
      (∀ i, a i ∈ Ico (0 : ℝ) ε) ∧
      (∀ z : Submodule.span ℤ (Set.range b), P ((z : Fin m → ℝ) + a)) ∧
      (∑' z : Submodule.span ℤ (Set.range b), f ((z : Fin m → ℝ) + a)) ≤
        2 * (ENNReal.ofReal (ε ^ m))⁻¹ * ∫⁻ x, f x ∧
      (∑' z : Submodule.span ℤ (Set.range b), g ((z : Fin m → ℝ) + a)) ≤
        2 * (ENNReal.ofReal (ε ^ m))⁻¹ * ∫⁻ x, g x := by
  intro b
  let If := ∫⁻ x, f x
  let Ig := ∫⁻ x, g x
  let H := fun x => If⁻¹ * f x + Ig⁻¹ * g x
  have hH : AEMeasurable H volume := (hf.const_mul If⁻¹).add (hg.const_mul Ig⁻¹)
  have hIf : If⁻¹ * If ≤ 1 := by
    by_cases hf0 : If = 0
    · simp only [hf0, mul_zero]; exact zero_le
    · exact (ENNReal.inv_mul_cancel hf0 hfFinite).le
  have hIg : Ig⁻¹ * Ig ≤ 1 := by
    by_cases hg0 : Ig = 0
    · simp only [hg0, mul_zero]; exact zero_le
    · exact (ENNReal.inv_mul_cancel hg0 hgFinite).le
  have hInt : (∫⁻ x, H x) ≤ 2 := by
    rw [lintegral_add_left' (hf.const_mul If⁻¹),
      lintegral_const_mul'' If⁻¹ hf, lintegral_const_mul'' Ig⁻¹ hg]
    calc
      _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add hIf hIg
      _ = 2 := by norm_num
  have hPzero : ∀ᵐ x ∂volume, P x ∧ (If = 0 → f x = 0) ∧ (Ig = 0 → g x = 0) := by
    have hfae : ∀ᵐ x ∂volume, If = 0 → f x = 0 := by
      by_cases hf0 : If = 0
      · exact ((lintegral_eq_zero_iff' hf).mp hf0).mono fun _ hx _ => hx
      · exact Eventually.of_forall fun _ hx => (hf0 hx).elim
    have hgae : ∀ᵐ x ∂volume, Ig = 0 → g x = 0 := by
      by_cases hg0 : Ig = 0
      · exact ((lintegral_eq_zero_iff' hg).mp hg0).mono fun _ hx _ => hx
      · exact Eventually.of_forall fun _ hx => (hg0 hx).elim
    filter_upwards [hP, hfae, hgae] with x hx hfx hgx
    exact ⟨hx, hfx, hgx⟩
  obtain ⟨a, ha, hPa, hbound⟩ := exists_grid_translate_tsum_le hε hH hPzero
  have hbound' : (∑' z : Submodule.span ℤ (Set.range b), H ((z : Fin m → ℝ) + a)) ≤
      (ENNReal.ofReal (ε ^ m))⁻¹ * 2 :=
    hbound.trans (mul_le_mul_right hInt _)
  have hsum : (∑' z : Submodule.span ℤ (Set.range b), H ((z : Fin m → ℝ) + a)) =
      If⁻¹ * (∑' z : Submodule.span ℤ (Set.range b), f ((z : Fin m → ℝ) + a)) +
      Ig⁻¹ * (∑' z : Submodule.span ℤ (Set.range b), g ((z : Fin m → ℝ) + a)) := by
    dsimp only [H]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  rw [hsum] at hbound'
  refine ⟨a, ha, fun z => (hPa z).1, ?_, ?_⟩
  · by_cases hf0 : If = 0
    · have hz (z : Submodule.span ℤ (Set.range b)) : f ((z : Fin m → ℝ) + a) = 0 :=
        (hPa z).2.1 hf0
      simp only [hz, tsum_zero, show (∫⁻ x, f x) = 0 from hf0, mul_zero, le_refl]
    · have hle : If⁻¹ * (∑' z : Submodule.span ℤ (Set.range b),
          f ((z : Fin m → ℝ) + a)) ≤ (ENNReal.ofReal (ε ^ m))⁻¹ * 2 :=
        (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from bot_le)).trans hbound'
      calc
        _ = If * (If⁻¹ * (∑' z : Submodule.span ℤ (Set.range b),
            f ((z : Fin m → ℝ) + a))) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hf0 hfFinite, one_mul]
        _ ≤ If * ((ENNReal.ofReal (ε ^ m))⁻¹ * 2) := mul_le_mul_right hle If
        _ = _ := by dsimp only [If]; ac_rfl
  · by_cases hg0 : Ig = 0
    · have hz (z : Submodule.span ℤ (Set.range b)) : g ((z : Fin m → ℝ) + a) = 0 :=
        (hPa z).2.2 hg0
      simp only [hz, tsum_zero, show (∫⁻ x, g x) = 0 from hg0, mul_zero, le_refl]
    · have hle : Ig⁻¹ * (∑' z : Submodule.span ℤ (Set.range b),
          g ((z : Fin m → ℝ) + a)) ≤ (ENNReal.ofReal (ε ^ m))⁻¹ * 2 :=
        (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ _ from bot_le)).trans hbound'
      calc
        _ = Ig * (Ig⁻¹ * (∑' z : Submodule.span ℤ (Set.range b),
            g ((z : Fin m → ℝ) + a))) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hg0 hgFinite, one_mul]
        _ ≤ Ig * ((ENNReal.ofReal (ε ^ m))⁻¹ * 2) := mul_le_mul_right hle Ig
        _ = _ := by dsimp only [Ig]; ac_rfl

end StratificationTheory
