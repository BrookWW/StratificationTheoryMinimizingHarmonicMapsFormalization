module

public import StratificationTheory.Foundation.CoherentCylinderGradientEnergy
public import StratificationTheory.Foundation.NativeRadialEnergyConstants

/-!
# Dimension-only native energy transport on the fixed spatial collar

One positive constant precedes the target dimension, time interval and all
column data. Genuine ambient L2 columns and real-radius spatial/time
coherence give native full-column L2, integrable HS density and a uniform
native energy bound from the actual ambient collar energy.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- Fixed-collar transport has a dimension-only constant before every map,
target dimension and time interval, with the same native column family. -/
theorem exists_native_cylinder_coherent_energy_constant (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a b : ℝ)
      (DW : Domain (n + 1) → Gradient (n + 1) q)
      (g : unitCylinder n a b → Gradient (n + 1) q),
      (∀ i : Fin (n + 1), MemLp (fun y => DW y i) 2
        (volume.restrict {y : Domain (n + 1) |
          let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
          ((1 / 2 : ℝ) < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo a b})) →
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
      (∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2), ∀ᵐ c ∂μ,
        (e c.val).2 0 ∈ Ioo a b →
        (∀ i : Fin n, DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
          r⁻¹ • g c (Fin.castAdd 1 i)) ∧
        DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
          g c (Fin.natAdd n (0 : Fin 1))) →
      (∀ i : Fin (n + 1), MemLp (fun c => g c i) 2 μ) ∧
        Integrable (fun c => hsNormSq (g c)) μ ∧
        (∫ c, hsNormSq (g c) ∂μ) ≤ C *
          ∫ y in {y : Domain (n + 1) |
            ((1 / 2 : ℝ) < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo a b},
            hsNormSq (DW y) := by
  let η := (Measure.volumeIoiPow (n - 1)).restrict
    {ρ | (1 / 2 : ℝ) < ρ.val ∧ ρ.val < 2}
  let M : ℝ := ∫ _ρ, (1 : ℝ) ∂η
  let S : ℝ := ∫ ρ, (ρ.val⁻¹) ^ 2 ∂η
  obtain ⟨_hSI, hMpos, hSM⟩ := native_radial_collar_energy_moments n
  change 0 < M at hMpos
  change M / 4 ≤ S at hSM
  refine ⟨4 / M, div_pos (by norm_num) hMpos, ?_⟩
  intro q a b DW g hDW e μ hcoh
  obtain ⟨hg, hgI, hEnergy⟩ := native_cylinder_gradient_energy_of_real_radial_coherence hn
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 2) DW g hDW hcoh
  let ES : ℝ := ∫ c, hsNormSq (fun i : Fin n => g c (Fin.castAdd 1 i)) ∂μ
  let ET : ℝ := ∫ c, ‖g c (Fin.natAdd n (0 : Fin 1))‖ ^ 2 ∂μ
  let EA : ℝ := ∫ y in {y : Domain (n + 1) |
    ((1 / 2 : ℝ) < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo a b}, hsNormSq (DW y)
  change EA = S * ES + M * ET at hEnergy
  have hES : 0 ≤ ES := integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hET : 0 ≤ ET := integral_nonneg (fun _ => sq_nonneg _)
  have hIS : Integrable (fun c => hsNormSq (fun i : Fin n => g c (Fin.castAdd 1 i))) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      (hg (Fin.castAdd 1 i)).integrable_norm_pow (by norm_num))
  have hIT : Integrable (fun c => ‖g c (Fin.natAdd n (0 : Fin 1))‖ ^ 2) μ :=
    (hg (Fin.natAdd n (0 : Fin 1))).integrable_norm_pow (by norm_num)
  have hnative : (∫ c, hsNormSq (g c) ∂μ) = ES + ET := by
    have hsplit (c : unitCylinder n a b) : hsNormSq (g c) =
        hsNormSq (fun i : Fin n => g c (Fin.castAdd 1 i)) +
          ‖g c (Fin.natAdd n (0 : Fin 1))‖ ^ 2 := by
      rw [hsNormSq, Fin.sum_univ_add, Fin.sum_univ_one]
      rfl
    simp_rw [hsplit]
    exact integral_add hIS hIT
  have hsp := mul_le_mul_of_nonneg_right hSM hES
  have htm := mul_le_mul_of_nonneg_right (show M / 4 ≤ M by linarith) hET
  have hlow : M * (ES + ET) ≤ 4 * EA := by
    rw [hEnergy]
    nlinarith
  refine ⟨hg, hgI, ?_⟩
  change (∫ c, hsNormSq (g c) ∂μ) ≤ (4 / M) * EA
  rw [hnative]
  calc
    ES + ET ≤ (4 * EA) / M := (le_div_iff₀ hMpos).mpr (by nlinarith)
    _ = (4 / M) * EA := by ring

end StratificationTheory
