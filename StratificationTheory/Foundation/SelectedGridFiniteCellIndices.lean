module

public import StratificationTheory.Foundation.SelectedGridFiniteMesh
public import StratificationTheory.Foundation.CoordinateCellParameterInjectivity

public section

open HarmonicMaps Set Module MeasureTheory
open scoped BigOperators ENNReal

namespace StratificationTheory

/-- Valid finite mesh indices give distinct original full-dimensional
sorted physical cells, preserving their exact axes and physical origin. -/
theorem selected_grid_finite_actual_cell_embedding {N M : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (node : (Fin N → Fin M) → Submodule.span ℤ (Set.range grid))
    (hNode : Function.Injective node) :
    let origin := fun α => WithLp.toLp 2 ((node α : Fin N → ℝ) + offset)
    let Valid := {α : Fin N → Fin M // ∀ t : Domain N,
      (∀ j, t j ∈ Icc (0 : ℝ) ε) → ∀ j, (origin α + t) j ∈ Ioo (-1 : ℝ) 1}
    let Cell := {p : originalPhysicalCellCarrier N grid offset ε //
      StrictMono (p.val.1 : Fin N → Fin N)}
    ∃ index : Valid ↪ Cell,
      (∀ α, (index α).val.val.1 = Function.Embedding.refl (Fin N)) ∧
      (∀ α, (index α).val.val.2 = origin α.val) ∧
      (∀ f : Cell → ℝ≥0∞, ∑' α : Valid, f (index α) ≤ ∑' c : Cell, f c) := by
  classical
  intro origin Valid Cell
  have hSum (t : Domain N) :
      ∑ j : Fin N, t j • EuclideanSpace.single j (1 : ℝ) = t := by
    ext j
    have h := coordinate_cell_affine_parameter_coordinate
      (Function.Embedding.refl (Fin N)) (0 : Domain N) 0 1 t j
    simpa only [zero_add, one_mul, Function.Embedding.refl_apply,
      PiLp.zero_apply] using h
  let index (α : Valid) : Cell :=
    ⟨⟨(Function.Embedding.refl (Fin N), origin α.val), by
      refine ⟨node α.val, ?_, rfl⟩
      intro t ht j
      change (origin α.val + ∑ i : Fin N,
        t i • EuclideanSpace.single i (1 : ℝ)) j ∈ Ioo (-1 : ℝ) 1
      rw [hSum]
      exact α.property t ht j⟩, by
      intro i j hij
      exact hij⟩
  have hIndex : Function.Injective index := by
    intro α β h
    apply Subtype.ext
    apply hNode
    apply Subtype.ext
    funext j
    have hj := congrArg (fun c : Cell => c.val.val.2 j) h
    change (node α.val : Fin N → ℝ) j + offset j =
      (node β.val : Fin N → ℝ) j + offset j at hj
    exact add_right_cancel hj
  refine ⟨⟨index, hIndex⟩, fun _ => rfl, fun _ => rfl, ?_⟩
  intro f
  exact ENNReal.tsum_comp_le_tsum_of_injective hIndex f

/-- Adjacent finite positive-mesh indices have exactly the physical
source-grid displacement used by canonical shared-face coherence. -/
theorem selected_grid_finite_mesh_neighbor_origin {N M : ℕ}
    (a : Domain N) (ε : ℝ) (α β : Fin N → Fin M) (i : Fin N)
    (hAt : (β i).val = (α i).val + 1)
    (hOther : ∀ j, j ≠ i → β j = α j) :
    a + WithLp.toLp 2 (fun j => ((β j).val : ℝ) * ε) =
      (a + WithLp.toLp 2 (fun j => ((α j).val : ℝ) * ε)) +
        ε • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, mul_one]
    change a i + ((β i).val : ℝ) * ε = a i + ((α i).val : ℝ) * ε + ε
    rw [hAt]
    push_cast
    ring
  · have hj := hOther j hji
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      if_neg hji, smul_eq_mul, mul_zero, add_zero]
    change a j + ((β j).val : ℝ) * ε = a j + ((α j).val : ℝ) * ε
    rw [hj]

end StratificationTheory
