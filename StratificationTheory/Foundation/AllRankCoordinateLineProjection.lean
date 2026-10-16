module
public import StratificationTheory.Foundation.ScaledGridCubeEdges

/-!
# Coordinate-line projections of all-rank selected grid channels

The actual rank-one indices of the same finite all-rank family retain the
original sampling constant and the same lattice offset.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Every coordinate-line channel is an actual rank-one member of the
original all-rank family, on the same lattice with the same finite count. -/
theorem all_rank_grid_coordinate_line_channel {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (offset : Fin (n + 1) → ℝ) (f : Domain (n + 1) → ℝ≥0∞) (mass : ℝ≥0∞) :
    let J := (r : Fin (n + 2)) × (Fin r.val ↪ Fin (n + 1))
    let grid := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _ : Fin (n + 1) => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
    let C := fun r => ⋂ s : Fin r, (EuclideanSpace.proj s) ⁻¹' Ico (0 : ℝ) ε
    (∀ j : J, (∑' z : L, ∫⁻ t in C j.1.val,
      f (y z + ∑ s : Fin j.1.val, t s • EuclideanSpace.single (j.2 s) (1 : ℝ))) ≤
      2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
        ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ j.1.val)) * mass) →
    ∀ normal : Fin (n + 1), (∑' z : L, ∫⁻ t in C 1,
      f (y z + t 0 • EuclideanSpace.single normal (1 : ℝ))) ≤
      2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
        ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal ε) * mass := by
  intro J grid L y C hAll normal
  let face : Fin 1 ↪ Fin (n + 1) :=
    ⟨fun _ => normal, fun _ _ _ => Subsingleton.elim _ _⟩
  let j : J := ⟨⟨1, by omega⟩, face⟩
  have h := hAll j
  change (∑' z : L, ∫⁻ t in C 1,
    f (y z + ∑ s : Fin 1, t s • EuclideanSpace.single normal (1 : ℝ))) ≤
      2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
        ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ 1)) * mass at h
  simpa only [Fin.sum_univ_one, pow_one] using h

end StratificationTheory
