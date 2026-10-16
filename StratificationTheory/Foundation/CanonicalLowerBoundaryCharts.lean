module

public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier
public import StratificationTheory.Foundation.CoordinateCellParameterInjectivity

public section

open HarmonicMaps Set
open scoped BigOperators

namespace StratificationTheory

/-- The actual canonical source cap and inherited filled lower prism both
have injective native physical charts. Their common index type retains
the original physical cell and original temporal side. -/
theorem canonical_lower_boundary_charts_injective {d N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin N)}
    let L := (Cell (d + 1) × Bool) ⊕ Cell d
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let physical := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1)
    let lowerChart : L → Domain (d + 1) → Domain (N + 1) := Sum.elim
      (fun c z => physical.symm
        (c.1.val.val.2 + ∑ j : Fin (d + 1), (ε / 2 + (ε / 2) * z j) •
          EuclideanSpace.single (c.1.val.val.1 j) (1 : ℝ),
          EuclideanSpace.single (0 : Fin 1) (if c.2 then ε else 0)))
      (fun c z => physical.symm
        (c.val.val.2 + ∑ j : Fin d, (ε / 2 + (ε / 2) * (e z).1 j) •
          EuclideanSpace.single (c.val.val.1 j) (1 : ℝ),
          EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * (e z).2 0)))
    ∀ l : L, Function.Injective (lowerChart l) := by
  intro Cell L e physical lowerChart l
  have hh : ε / 2 ≠ 0 := (div_pos hε (by norm_num : (0 : ℝ) < 2)).ne'
  rcases l with ⟨c, side⟩ | c
  · intro z v hSame
    exact coordinate_cell_affine_parameter_injective c.val.val.1 c.val.val.2
      (ε / 2) (ε / 2) hh (congrArg Prod.fst (physical.symm.injective hSame))
  · exact coordinate_prism_affine_parameter_injective c.val.val.1 c.val.val.2
      (ε / 2) (ε / 2) hh

end StratificationTheory
