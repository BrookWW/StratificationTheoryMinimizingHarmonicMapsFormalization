module

public import HarmonicMaps.Sobolev
public import Mathlib.LinearAlgebra.Basis.Basic

public section

open HarmonicMaps Set
open scoped BigOperators

namespace StratificationTheory

/-- Original closed coordinate cells contained in the open unit coordinate
cube, with literal lattice vertices and original ordered coordinate maps. -/
@[expose] def originalCoordinateCellCarrier {N : ℕ} (k : ℕ)
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    Set ((Fin k ↪ Fin N) × Submodule.span ℤ (Set.range grid)) :=
  {p | ∀ t : Domain k, (∀ j, t j ∈ Icc (0 : ℝ) ε) → ∀ j : Fin N,
    (WithLp.toLp 2 (((p.2 : Submodule.span ℤ (Set.range grid)) : Fin N → ℝ) + offset) +
      ∑ i : Fin k, t i • EuclideanSpace.single (p.1 i) (1 : ℝ)) j ∈ Ioo (-1 : ℝ) 1}

/-- Membership in the whole native carrier is exactly containment of the
original closed physical cell, for every parameter and every coordinate. -/
theorem mem_originalCoordinateCellCarrier_iff {N : ℕ} (k : ℕ)
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ)
    (p : (Fin k ↪ Fin N) × Submodule.span ℤ (Set.range grid)) :
    p ∈ originalCoordinateCellCarrier k grid offset ε ↔
      ∀ t : Domain k, (∀ j, t j ∈ Icc (0 : ℝ) ε) → ∀ j : Fin N,
        (WithLp.toLp 2 (((p.2 : Submodule.span ℤ (Set.range grid)) : Fin N → ℝ) + offset) +
          ∑ i : Fin k, t i • EuclideanSpace.single (p.1 i) (1 : ℝ)) j ∈ Ioo (-1 : ℝ) 1 :=
  Iff.rfl

end StratificationTheory
