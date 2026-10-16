module
public import StratificationTheory.Foundation.OriginalPhysicalCellEnergySum

/-!
# Weighted original horizontal energy over the actual full cell family

The exact physical power of every original horizontal rank cancels its
native sampling power. The finite all-rank embedding count bounds every
rank count, independently of the number of physical cells.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Every original rank embedding is an actual member of the one finite
all-rank source family. -/
theorem coordinate_embedding_card_le_all_rank_count {N r : ℕ} (hr : r ≤ N) :
    Fintype.card (Fin r ↪ Fin N) ≤
      Fintype.card ((k : Fin (N + 1)) × (Fin k.val ↪ Fin N)) := by
  let k : Fin (N + 1) := ⟨r, by omega⟩
  let f : (Fin r ↪ Fin N) → ((k : Fin (N + 1)) × (Fin k.val ↪ Fin N)) := fun c => ⟨k, c⟩
  apply Fintype.card_le_of_injective f
  intro c d h
  change (⟨k, c⟩ : (j : Fin (N + 1)) × (Fin j.val ↪ Fin N)) =
    (⟨k, d⟩ : (j : Fin (N + 1)) × (Fin j.val ↪ Fin N)) at h
  exact eq_of_heq (Sigma.mk.inj h).2

/-- Every original horizontal rank has the same mesh-linear source energy
budget after its exact physical prism weight, over all actual sorted cells. -/
theorem original_physical_cell_weighted_energy_tsum_le {n r q : ℕ} (hr : r ≤ n + 2)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε : ℝ} (hε : 0 < ε) (count : ℕ) (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _ : Fin (n + 2) => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let P := ⋂ k : Fin r, (EuclideanSpace.proj k) ⁻¹' Ioo (0 : ℝ) ε
    let C := ⋂ k : Fin r, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let channel := fun (coord : Fin r ↪ Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Eraw (y z + ∑ k : Fin r, t k • EuclideanSpace.single (coord k) (1 : ℝ))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
      ((count : ℝ≥0∞) * ENNReal.ofReal (ε ^ r)) * ENNReal.ofReal A₀
    (∀ coord, (∑' z : L, channel coord z) ≤ c) →
    let Cell := {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin (n + 2))}
    let E := fun p : Cell => ∑ l : Fin 2, ∫ t in P,
      hsNormSq (fun k : Fin r => Dw l
        (p.val.val.2 + ∑ j : Fin r, t j • EuclideanSpace.single (p.val.val.1 j) (1 : ℝ)) (p.val.val.1 k))
    ENNReal.ofReal (ε ^ (n + 2 - r + 1)) * (∑' p : Cell, ENNReal.ofReal (E p)) ≤
      2 * (count : ℝ≥0∞) *
        (Fintype.card ((k : Fin (n + 3)) × (Fin k.val ↪ Fin (n + 2))) : ℝ≥0∞) *
        ENNReal.ofReal ε * ENNReal.ofReal A₀ := by
  intro grid L y P C Eraw channel A₀ c hSelect Cell E
  have hRaw := original_physical_cell_energy_tsum_le_native_channels Dw hε count offset hSelect
  calc
    _ ≤ ENNReal.ofReal (ε ^ (n + 2 - r + 1)) *
        ((Fintype.card (Fin r ↪ Fin (n + 2)) : ℝ≥0∞) * c) := mul_le_mul_right hRaw _
    _ = 2 * (count : ℝ≥0∞) * (Fintype.card (Fin r ↪ Fin (n + 2)) : ℝ≥0∞) *
        (ENNReal.ofReal (ε ^ (n + 2 - r + 1)) * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
          ENNReal.ofReal (ε ^ r)) * ENNReal.ofReal A₀ := by dsimp only [c]; ac_rfl
    _ = 2 * (count : ℝ≥0∞) * (Fintype.card (Fin r ↪ Fin (n + 2)) : ℝ≥0∞) *
        ENNReal.ofReal ε * ENNReal.ofReal A₀ := by rw [native_rank_prism_scaling_cancel hε hr]
    _ ≤ _ := by
      have hCard : (Fintype.card (Fin r ↪ Fin (n + 2)) : ℝ≥0∞) ≤
          (Fintype.card ((k : Fin (n + 3)) × (Fin k.val ↪ Fin (n + 2))) : ℝ≥0∞) := by
        exact_mod_cast coordinate_embedding_card_le_all_rank_count hr
      gcongr

end StratificationTheory
