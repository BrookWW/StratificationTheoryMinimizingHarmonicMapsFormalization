module
public import StratificationTheory.Foundation.AllRankCoordinateLineProjection
public import StratificationTheory.Interpolation.OriginalGridNearLevelEdgeComplex

/-!
# Near-level edge bounds on an original all-rank selected lattice

The actual rank-one members of one original all-rank source selection
supply the joint nearby-edge estimate on exactly that fixed offset.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Actual all-rank selected channels give the original edge complex and
joint quantitative radius on the same supplied lattice offset. -/
theorem original_all_rank_selected_grid_near_level_edge_complex {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε a b : ℝ} (hε : 0 < ε) (hab : a < b)
    (offset : Fin (n + 2) → ℝ) :
    let J := (r : Fin (n + 3)) × (Fin r.val ↪ Fin (n + 2))
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let I := Fin (n + 2) × (Fin (n + 1) → Bool)
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
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
        ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal ε)
    let B := 6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * (Fintype.card I : ℝ≥0∞) * c
    let er := fun (i : I) (z : L) => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) i.1‖ ^ 2 +
        ‖Dw 1 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) i.1‖ ^ 2
    let dr := fun (i : I) (z : L) => ∫ s in Ioo (0 : ℝ) ε,
      ‖w 0 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) -
        w 1 (y z + s • EuclideanSpace.single i.1 (1 : ℝ))‖ ^ 2
    let vertex := fun i : I =>
      (WithLp.toLp 2 (fun j : Fin (n + 1) => if i.2 j then ε else 0) : Domain (n + 1))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let CAll := fun r => ⋂ s : Fin r, (EuclideanSpace.proj s) ⁻¹' Ico (0 : ℝ) ε
    (∀ j : J, (∑' z : L, ∫⁻ t in CAll j.1.val,
      Eraw (y z + ∑ s : Fin j.1.val, t s • EuclideanSpace.single (j.2 s) (1 : ℝ))) ≤
        2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
          ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ j.1.val)) * ENNReal.ofReal A₀) →
    (∀ j : J, (∑' z : L, ∫⁻ t in CAll j.1.val,
      Draw (y z + ∑ s : Fin j.1.val, t s • EuclideanSpace.single (j.2 s) (1 : ℝ))) ≤
        2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
          ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ j.1.val)) * ENNReal.ofReal D₀) →
    ∀ energy : ℝ → ℝ≥0∞,
    AEMeasurable energy (volume.restrict (Ioo a b)) →
    (∫⁻ r in Ioo a b, energy r) ≠ ⊤ →
    ∀ P : ℝ → Prop, (∀ᵐ r ∂volume.restrict (Ioo a b), P r) →
    ∃ (shift : I → L) (r : ℝ),
      r ∈ Ioo a b ∧ P r ∧
      energy r ≤ 3 * (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ s in Ioo a b, energy s ∧
      (∀ (i : I) (z : L) (s : ℝ),
        y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
          y z + cubicalSignedFaceIsometry (n + 1) i.1 true
            (e.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s))) ∧
      (∀ (i : I) (z : L) (s : ℝ), s ∈ Icc (0 : ℝ) ε → ∀ j,
        (y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ)) j - (y z) j ∈ Icc (0 : ℝ) ε) ∧
      ∀ z : L,
        (∀ x : Domain (n + 2), (∀ j, x j - (y z) j ∈ Icc (0 : ℝ) ε) →
          x ∈ ball (0 : Domain (n + 2)) ((n : ℝ) + 3)) →
        (∃ x : Domain (n + 2), (∀ j, x j - (y z) j ∈ Icc (0 : ℝ) ε) ∧ ‖WithLp.ofLp x‖ = r) →
        (∑ i : I, (dr i (z + shift i) / ε + Real.sqrt (2 * dr i (z + shift i) * er i (z + shift i)))) ≤
          (Fintype.card I : ℝ) * B.toReal * (D₀ / ε + Real.sqrt (2 * D₀ * A₀)) := by
  intro J grid L I y C Eraw Draw Eline Dline A₀ D₀ c B er dr vertex e CAll
    hSelectE hSelectD energy hEnergy hEnergyFinite P hP
  have hE₁ := all_rank_grid_coordinate_line_channel hε offset Eraw (ENNReal.ofReal A₀) hSelectE
  have hD₁ := all_rank_grid_coordinate_line_channel hε offset Draw (ENNReal.ofReal D₀) hSelectD
  exact original_selected_grid_joint_near_level_edge_complex w Dw hε hab (Fintype.card J)
    offset hE₁ hD₁ energy hEnergy hEnergyFinite P hP

end StratificationTheory
