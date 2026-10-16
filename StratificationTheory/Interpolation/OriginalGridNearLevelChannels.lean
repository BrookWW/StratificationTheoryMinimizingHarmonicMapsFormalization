module

public import StratificationTheory.Foundation.CubicalNearLevelLatticeIncidence
public import StratificationTheory.Interpolation.OriginalAllFacePrismGrid

/-! # Original selected-grid energy and discrepancy on one cubical level -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The original selected native one-face channels give the actual near-cell
line energy and discrepancy on one common radius. Finite incidence shifts
are accounted for internally and the width gain comes from their windows. -/
theorem original_selected_grid_joint_near_level_channels {n q : ℕ} {I : Type*} [Fintype I]
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε a b : ℝ} (hε : 0 < ε) (hab : a < b) (count : ℕ)
    (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let C := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Eline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Eraw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let Dline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Draw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let A₀ := ENNReal.ofReal
      ((∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
        ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x))
    let D₀ := ENNReal.ofReal
      (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2)
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    ∀ (shift : I → L) (tangent : I → Fin (n + 2)),
    (∀ k, (∑' z : L, Eline k z) ≤ c * A₀) →
    (∀ k, (∑' z : L, Dline k z) ≤ c * D₀) →
    ∀ energy : ℝ → ℝ≥0∞,
    AEMeasurable energy (volume.restrict (Ioo a b)) →
    (∫⁻ r in Ioo a b, energy r) ≠ ⊤ →
    ∀ P : ℝ → Prop, (∀ᵐ r ∂volume.restrict (Ioo a b), P r) →
    ∃ r ∈ Ioo a b, P r ∧
      energy r ≤ 3 * (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ s in Ioo a b, energy s ∧
      (∑' z : L, (Icc (‖WithLp.ofLp (y z)‖ - ε) (‖WithLp.ofLp (y z)‖ + ε)).indicator
        (fun _ : ℝ => ∑ i : I, Eline (tangent i) (z + shift i)) r) ≤
          6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * (Fintype.card I : ℝ≥0∞) * c * A₀ ∧
      (∑' z : L, (Icc (‖WithLp.ofLp (y z)‖ - ε) (‖WithLp.ofLp (y z)‖ + ε)).indicator
        (fun _ : ℝ => ∑ i : I, Dline (tangent i) (z + shift i)) r) ≤
          6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * (Fintype.card I : ℝ≥0∞) * c * D₀ := by
  intro grid L y C Eraw Draw Eline Dline A₀ D₀ c shift tangent hSelectE hSelectD energy hEnergy hEnergyFinite P hP
  have hVol0 : ENNReal.ofReal (ε ^ (n + 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hε _)).ne'
  have hcFinite : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr hVol0))
      (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top)
  have hABoundFinite : c * A₀ ≠ ⊤ := ENNReal.mul_ne_top hcFinite ENNReal.ofReal_ne_top
  have hDBoundFinite : c * D₀ ≠ ⊤ := ENNReal.mul_ne_top hcFinite ENNReal.ofReal_ne_top
  let E := fun i : I => Eline (tangent i)
  let D := fun i : I => Dline (tangent i)
  have hEFinite (i : I) : (∑' z : L, E i z) ≠ ⊤ :=
    ne_top_of_le_ne_top hABoundFinite (hSelectE (tangent i))
  have hDFinite (i : I) : (∑' z : L, D i z) ≠ ⊤ :=
    ne_top_of_le_ne_top hDBoundFinite (hSelectD (tangent i))
  have hSumE : (∑ i : I, ∑' z : L, E i z) ≤ (Fintype.card I : ℝ≥0∞) * c * A₀ := by
    calc
      _ ≤ ∑ _i : I, c * A₀ := Finset.sum_le_sum fun i _ => hSelectE (tangent i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ac_rfl
  have hSumD : (∑ i : I, ∑' z : L, D i z) ≤ (Fintype.card I : ℝ≥0∞) * c * D₀ := by
    calc
      _ ≤ ∑ _i : I, c * D₀ := Finset.sum_le_sum fun i _ => hSelectD (tangent i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ac_rfl
  obtain ⟨r, hr, hPr, hE, hA, hD⟩ := exists_joint_cubical_level_shift_channel_bounds hab y shift E D
    hEFinite hDFinite energy hEnergy hEnergyFinite hP
  refine ⟨r, hr, hPr, hE, ?_, ?_⟩
  · exact hA.trans ((mul_le_mul_right hSumE _).trans_eq (by ac_rfl))
  · exact hD.trans ((mul_le_mul_right hSumD _).trans_eq (by ac_rfl))

end StratificationTheory
