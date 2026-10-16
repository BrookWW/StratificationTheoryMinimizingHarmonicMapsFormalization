module

public import StratificationTheory.Foundation.SelectedGridFiniteActiveCells

public section

open HarmonicMaps Set Module MeasureTheory
open scoped BigOperators ENNReal

namespace StratificationTheory

/-- All valid finite prisms in the first physical time slab inject into
the same original spatial-cell family, with literal source origins. -/
theorem selected_grid_first_slab_actual_cell_embedding {N M : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (node : (Fin N → Fin M) → Submodule.span ℤ (Set.range grid))
    (hNode : Function.Injective node) :
    let origin := fun α => WithLp.toLp 2 ((node α : Fin N → ℝ) + offset)
    let Valid := {α : Fin (N + 1) → Fin M //
      (α (Fin.last N)).val = 0 ∧
        ∀ t : Domain N, (∀ j, t j ∈ Icc (0 : ℝ) ε) →
          ∀ j, (origin (fun i => α i.castSucc) + t) j ∈ Ioo (-1 : ℝ) 1}
    let Cell := {p : originalPhysicalCellCarrier N grid offset ε //
      StrictMono (p.val.1 : Fin N → Fin N)}
    ∃ index : Valid ↪ Cell,
      (∀ α, (index α).val.val.1 = Function.Embedding.refl (Fin N)) ∧
      (∀ α, (index α).val.val.2 = origin (fun i => α.val i.castSucc)) ∧
      (∀ f : Cell → ℝ≥0∞, ∑' α : Valid, f (index α) ≤ ∑' c : Cell, f c) := by
  classical
  intro origin Valid Cell
  obtain ⟨spatialIndex, hAxes, hOrigin, _hSum⟩ :=
    selected_grid_finite_actual_cell_embedding grid offset ε node hNode
  let Spatial := {α : Fin N → Fin M // ∀ t : Domain N,
    (∀ j, t j ∈ Icc (0 : ℝ) ε) → ∀ j, (origin α + t) j ∈ Ioo (-1 : ℝ) 1}
  let project (α : Valid) : Spatial := ⟨fun j => α.val j.castSucc, α.property.2⟩
  have hProject : Function.Injective project := by
    intro α β h
    have hSpatial := congrArg Subtype.val h
    have hTime := finite_first_time_slab_spatial_index_injective
      (a₁ := ⟨α.val, α.property.1⟩) (a₂ := ⟨β.val, β.property.1⟩) hSpatial
    have hRaw : α.val = β.val := congrArg
      (fun c : {a : Fin (N + 1) → Fin M // (a (Fin.last N)).val = 0} => c.val) hTime
    exact Subtype.ext hRaw
  let index : Valid ↪ Cell := (⟨project, hProject⟩ : Valid ↪ Spatial).trans spatialIndex
  refine ⟨index, ?_, ?_, ?_⟩
  · intro α
    exact hAxes (project α)
  · intro α
    exact hOrigin (project α)
  · intro f
    exact ENNReal.tsum_comp_le_tsum_of_injective index.injective f

end StratificationTheory
