module

public import StratificationTheory.Foundation.SelectedGridFiniteActiveCells

public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace StratificationTheory

/-- A finite unit-mesh energy bound transfers to the total original
physical-cell energy when inactive cells are genuine zero extensions. -/
theorem finite_mesh_energy_le_actual_physical_family {ι κ : Type*} [Fintype ι]
    (s : Set ι) (index : s ↪ κ) (t : ℝ) (ht : 0 ≤ t)
    (unitEnergy : ι → ℝ) (physicalEnergy : κ → ℝ)
    (hNonneg : ∀ i, 0 ≤ unitEnergy i)
    (hZero : ∀ i, i ∉ s → unitEnergy i = 0)
    (hPhysical : ∀ i : s, t * unitEnergy i.val ≤ physicalEnergy (index i))
    (meshEnergy : ℝ) (hMesh : meshEnergy ≤ t * ∑ i : ι, unitEnergy i) :
    ENNReal.ofReal meshEnergy ≤ ∑' c : κ, ENNReal.ofReal (physicalEnergy c) := by
  classical
  have hFinite : ENNReal.ofReal (t * ∑ i : ι, unitEnergy i) =
      ∑' i : ι, ENNReal.ofReal (t * unitEnergy i) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    · exact (tsum_fintype _).symm
    · intro i _
      exact mul_nonneg ht (hNonneg i)
  refine (ENNReal.ofReal_le_ofReal hMesh).trans ?_
  rw [hFinite]
  exact tsum_zero_extension_le_actual_family s index
    (fun c => ENNReal.ofReal (physicalEnergy c))
    (fun i => ENNReal.ofReal (t * unitEnergy i))
    (fun i hi => by rw [hZero i hi, mul_zero, ENNReal.ofReal_zero])
    (fun i => ENNReal.ofReal_le_ofReal (hPhysical i))

end StratificationTheory
