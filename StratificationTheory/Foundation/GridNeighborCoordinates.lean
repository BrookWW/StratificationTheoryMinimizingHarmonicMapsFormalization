module

public import StratificationTheory.Foundation.FullGridEnergy

public section
open HarmonicMaps MeasureTheory Set Filter Module
namespace StratificationTheory

/-- A positive grid step in an actual ambient coordinate direction is
another point of the same selected scaled integer lattice. -/
theorem exists_scaled_grid_neighbor {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (a : Fin N → ℝ) :
    let b := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _j : Fin N => ε) (fun _j => hε.ne'.isUnit)
    ∀ (z : Submodule.span ℤ (Set.range b)) (j : Fin N),
      ∃ z' : Submodule.span ℤ (Set.range b),
        WithLp.toLp 2 ((z' : Fin N → ℝ) + a) =
          WithLp.toLp 2 ((z : Fin N → ℝ) + a) +
            ε • EuclideanSpace.single j (1 : ℝ) := by
  intro b z j
  let v : Submodule.span ℤ (Set.range b) :=
    ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨z + v, ?_⟩
  have hb : b j = ε • (Pi.single j (1 : ℝ) : Fin N → ℝ) := by
    simp only [b, Basis.isUnitSMul_apply, Pi.basisFun_apply]
  ext l
  change ((z : Fin N → ℝ) l + b j l) + a l =
    ((z : Fin N → ℝ) l + a l) + ε * (Pi.single j (1 : ℝ) : Fin N → ℝ) l
  rw [hb]
  change _ + ε * _ + _ = _
  ring

end StratificationTheory
