module

public import StratificationTheory.Foundation.PhysicalCellIndexCoherence

public section

open HarmonicMaps

namespace StratificationTheory

/-- A global family of actual canonical child indices commutes under
removal of two distinct spatial normals. Exact coordinate and physical-origin
metadata determine the same inherited lower cell, without an analytic input. -/
theorem canonical_child_physical_indices_commute {N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (child : (r : ℕ) → originalPhysicalCellCarrier (r + 1) grid offset ε →
      Fin (r + 1) → Bool → originalPhysicalCellCarrier r grid offset ε)
    (hAxes : ∀ r p i s, (child r p i s).val.1 = i.succAboveEmb.trans p.val.1)
    (hOrigin : ∀ r p i s, (child r p i s).val.2 =
      p.val.2 + (if s then ε else 0) • EuclideanSpace.single (p.val.1 i) (1 : ℝ))
    {k : ℕ} (p : originalPhysicalCellCarrier (k + 2) grid offset ε)
    (i : Fin (k + 2)) (a : Fin (k + 1)) (sideI sideJ : Bool) :
    let j := i.succAbove a
    let b := a.predAbove i
    child k (child (k + 1) p i sideI) a sideJ =
      child k (child (k + 1) p j sideJ) b sideI := by
  intro j b
  apply original_physical_cell_index_eq grid offset ε
  · rw [hAxes, hAxes, hAxes, hAxes]
    apply Function.Embedding.ext
    intro s
    change p.val.1 (i.succAbove (a.succAbove s)) =
      p.val.1 ((i.succAbove a).succAbove ((a.predAbove i).succAbove s))
    exact congrArg p.val.1 (Fin.succAbove_succAbove_succAbove_predAbove i a s).symm
  · rw [hOrigin, hOrigin, hOrigin, hOrigin, hAxes, hAxes]
    change (p.val.2 + (if sideI then ε else 0) • EuclideanSpace.single (p.val.1 i) (1 : ℝ)) +
        (if sideJ then ε else 0) • EuclideanSpace.single (p.val.1 (i.succAbove a)) (1 : ℝ) =
      (p.val.2 + (if sideJ then ε else 0) • EuclideanSpace.single (p.val.1 j) (1 : ℝ)) +
        (if sideI then ε else 0) • EuclideanSpace.single (p.val.1 (j.succAbove b)) (1 : ℝ)
    have hNormal : j.succAbove b = i := Fin.succAbove_succAbove_predAbove i a
    rw [hNormal]
    change (p.val.2 + _) + _ = (p.val.2 + _) + _
    abel

end StratificationTheory
