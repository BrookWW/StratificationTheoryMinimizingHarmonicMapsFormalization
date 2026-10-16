module

public import StratificationTheory.Foundation.OriginalCoordinateCellCarrier

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- The physical origin carrier of the original contained coordinate
cells. Lattice membership is a geometric witness and the index values are
exactly the ordered coordinate embedding and its original physical origin. -/
@[expose] def originalPhysicalCellCarrier {N : ℕ} (k : ℕ)
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    Set ((Fin k ↪ Fin N) × Domain N) :=
  {p | ∃ z : Submodule.span ℤ (Set.range grid),
    (p.1, z) ∈ originalCoordinateCellCarrier k grid offset ε ∧
      WithLp.toLp 2 ((z : Fin N → ℝ) + offset) = p.2}

/-- Every physical index has exactly its original native contained-cell
witness and its exact original translated physical origin. -/
theorem mem_originalPhysicalCellCarrier_iff {N : ℕ} (k : ℕ)
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (p : (Fin k ↪ Fin N) × Domain N) :
    p ∈ originalPhysicalCellCarrier k grid offset ε ↔
      ∃ z : Submodule.span ℤ (Set.range grid),
        (p.1, z) ∈ originalCoordinateCellCarrier k grid offset ε ∧
          WithLp.toLp 2 ((z : Fin N → ℝ) + offset) = p.2 :=
  Iff.rfl

end StratificationTheory
