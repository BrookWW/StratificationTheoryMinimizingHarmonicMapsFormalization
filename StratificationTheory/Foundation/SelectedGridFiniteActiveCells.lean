module

public import StratificationTheory.Foundation.SelectedGridFiniteCellIndices

public section

open HarmonicMaps Set Module MeasureTheory
open scoped BigOperators ENNReal

namespace StratificationTheory

/-- A translated finite mesh cell that meets the inner cube is a valid
original closed cell for the selected source-grid family. -/
theorem selected_grid_finite_active_cell_contained {N M : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < (1 / 8 : ℝ)) (a : Domain N)
    (α : Fin N → Fin M)
    (hActive : ∃ x ∈ (uniformGridCell N M ε α).val,
      ∀ j, |(a + x) j| < (3 / 4 : ℝ)) :
    ∀ t : Domain N, (∀ j, t j ∈ Icc (0 : ℝ) ε) →
      ∀ j, ((a + WithLp.toLp 2 (fun j => ((α j).val : ℝ) * ε)) + t) j ∈
        Ioo (-1 : ℝ) 1 := by
  obtain ⟨x, hx, hInner⟩ := hActive
  apply selected_grid_active_closed_cell_contained hε hεsmall
  refine ⟨a + x, hInner, ?_⟩
  intro j
  have hj := (mem_uniformGridCell_iff N M ε α x).mp hx j
  change a j + x j ∈ Icc (a j + ((α j).val : ℝ) * ε)
    (a j + ((α j).val : ℝ) * ε + ε)
  constructor <;> nlinarith [hj.1, hj.2]

/-- Distinct mesh prisms in the first physical time slab have distinct
spatial mesh indices. -/
theorem finite_first_time_slab_spatial_index_injective {N M : ℕ} :
    Function.Injective (fun α : {α : Fin (N + 1) → Fin M //
      (α (Fin.last N)).val = 0} => fun j : Fin N => α.val j.castSucc) := by
  intro α β h
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply Fin.ext
    exact α.property.trans β.property.symm
  · exact congrFun h j

/-- A zero extension of an actual injectively indexed subfamily has no
additional contribution to the total nonnegative energy. -/
theorem tsum_zero_extension_le_actual_family {ι κ : Type*} (s : Set ι)
    (index : s ↪ κ) (F : κ → ℝ≥0∞) (E : ι → ℝ≥0∞)
    (hZero : ∀ i, i ∉ s → E i = 0)
    (hBound : ∀ i : s, E i.val ≤ F (index i)) :
    ∑' i : ι, E i ≤ ∑' c : κ, F c := by
  classical
  have hRestrict : ∑' i : ι, E i = ∑' i : s, E i.val := by
    rw [tsum_subtype]
    apply tsum_congr
    intro i
    by_cases hi : i ∈ s
    · simp [hi]
    · simp [hi, hZero i hi]
  rw [hRestrict]
  exact (ENNReal.tsum_le_tsum hBound).trans
    (ENNReal.tsum_comp_le_tsum_of_injective index.injective F)

/-- Closed intersection with the inner cube suffices, including cells
whose only relevant contact is on a shared mesh face. -/
theorem selected_grid_finite_closed_active_cell_contained {N M : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < (1 / 8 : ℝ)) (a : Domain N)
    (α : Fin N → Fin M)
    (hActive : ∃ x : Domain N,
      (∀ j, x j ∈ Icc (((α j).val : ℝ) * ε) ((((α j).val : ℝ) + 1) * ε)) ∧
      ∀ j, |(a + x) j| < (3 / 4 : ℝ)) :
    ∀ t : Domain N, (∀ j, t j ∈ Icc (0 : ℝ) ε) →
      ∀ j, ((a + WithLp.toLp 2 (fun j => ((α j).val : ℝ) * ε)) + t) j ∈
        Ioo (-1 : ℝ) 1 := by
  obtain ⟨x, hx, hInner⟩ := hActive
  apply selected_grid_active_closed_cell_contained hε hεsmall
  refine ⟨a + x, hInner, ?_⟩
  intro j
  have hj := hx j
  change a j + x j ∈ Icc (a j + ((α j).val : ℝ) * ε)
    (a j + ((α j).val : ℝ) * ε + ε)
  constructor <;> nlinarith [hj.1, hj.2]

end StratificationTheory
