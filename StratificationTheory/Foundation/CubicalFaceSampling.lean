module

public import StratificationTheory.Foundation.GridKernelSampling

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
namespace StratificationTheory

/-- Arbitrary finitely many coordinate faces, possibly of different
dimensions, share one grid offset and two dimensionally scaled bounds.
Raw almost-everywhere properties hold on every selected face. -/
theorem exists_grid_translate_cubical_face_pair_energy
    {N : ℕ} {ι : Type*} [Fintype ι] (k : ι → ℕ)
    (face : ∀ i, Fin (k i) ↪ Fin N) {ε : ℝ} (hε : 0 < ε)
    {f g : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hfFinite : (∫⁻ x, f x) ≠ ⊤)
    (hgFinite : (∫⁻ x, g x) ≠ ⊤)
    {P : Domain N → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    let b := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _j : Fin N => ε) (fun _j => hε.ne'.isUnit)
    let shift := fun (i : ι) (t : Fin (k i) → ℝ) (j : Fin N) =>
      ∑ l : Fin (k i), if face i l = j then t l else 0
    let cube := fun i : ι => Set.univ.pi (fun _ : Fin (k i) => Ico (0 : ℝ) ε)
    ∃ a : Fin N → ℝ,
      (∀ j, a j ∈ Ico (0 : ℝ) ε) ∧
      (∀ z : Submodule.span ℤ (Set.range b),
        P (WithLp.toLp 2 ((z : Fin N → ℝ) + a))) ∧
      (∀ (i : ι) (z : Submodule.span ℤ (Set.range b)),
        ∀ᵐ t ∂volume.restrict (cube i),
          P (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t))) ∧
      (∀ i : ι,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube i,
          f (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t))) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (ε ^ k i)) * ∫⁻ x, f x) ∧
      (∀ i : ι,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube i,
          g (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t))) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (ε ^ k i)) * ∫⁻ x, g x) := by
  intro b shift cube
  let ν := fun i : ι => (volume : Measure (Fin (k i) → ℝ)).restrict (cube i)
  let m := fun i : ι => ENNReal.ofReal (ε ^ k i)
  have hvol (i : ι) : ν i univ = m i := by
    dsimp only [ν, m]
    rw [Measure.restrict_apply_univ, Real.volume_pi_Ico]
    simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hε.le]
  have hm0 (i : ι) : m i ≠ 0 := by
    dsimp only [m]
    positivity
  have hmtop (i : ι) : m i ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmass : (∑ i : ι, (m i)⁻¹ * ν i univ) = (Fintype.card ι : ℝ≥0∞) := by
    simp_rw [hvol, ENNReal.inv_mul_cancel (hm0 _) (hmtop _)]
    simp
  have hmassFinite : (∑ i : ι, (m i)⁻¹ * ν i univ) ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.natCast_ne_top _
  have hshift (i : ι) : Measurable (shift i) := by
    apply Continuous.measurable
    apply continuous_pi
    intro j
    apply continuous_finsetSum
    intro l _
    by_cases h : face i l = j
    · simpa only [h, ite_true] using (continuous_apply l : Continuous (fun t : Fin (k i) → ℝ => t l))
    · simpa only [h, ite_false] using (continuous_const : Continuous (fun _t : Fin (k i) → ℝ => (0 : ℝ)))
  obtain ⟨a, ha, hPa, hPK, _hF, _hG, hfi, hgi⟩ :=
    exists_grid_translate_kernel_family_pair_tsum_le ν shift hshift
      (fun i => (m i)⁻¹) hmassFinite hf hg hfFinite hgFinite hP hε
  rw [hmass] at hfi hgi
  refine ⟨a, ha, hPa, hPK, ?_, ?_⟩
  · intro i
    calc
      _ = m i * ((m i)⁻¹ * (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube i,
          f (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t)))) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (hm0 i) (hmtop i), one_mul]
      _ ≤ m i * (2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
          ((Fintype.card ι : ℝ≥0∞) * ∫⁻ x, f x)) := mul_le_mul_right (hfi i) (m i)
      _ = _ := by dsimp only [m]; ac_rfl
  · intro i
    calc
      _ = m i * ((m i)⁻¹ * (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube i,
          g (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift i t)))) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (hm0 i) (hmtop i), one_mul]
      _ ≤ m i * (2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
          ((Fintype.card ι : ℝ≥0∞) * ∫⁻ x, g x)) := mul_le_mul_right (hgi i) (m i)
      _ = _ := by dsimp only [m]; ac_rfl

end StratificationTheory
