module

public import StratificationTheory.Foundation.CanonicalCoordinateFacetCarrier
public import StratificationTheory.Foundation.CanonicalPrismFacetData

public section

open HarmonicMaps Set
open scoped BigOperators

namespace StratificationTheory

/-- All canonical sorted physical cells inherit one global family of
actual lower-cell indices and finite native prism frames on the same grid.
The entire physical space-time chart commutes on both signed facets. -/
theorem exists_canonical_sorted_prism_facet_family {N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hGrid : ∀ j, grid j = ε • Pi.single j (1 : ℝ)) :
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin N)}
    let e := fun r : ℕ => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := r) (m := 1)
    let physical := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1)
    let P := fun (r : ℕ) (p : Cell r) (z : Domain (r + 1)) => physical.symm
      (p.val.val.2 + ∑ j : Fin r, (ε / 2 + (ε / 2) * (e r z).1 j) •
        EuclideanSpace.single (p.val.val.1 j) (1 : ℝ),
        EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * (e r z).2 0))
    ∃ (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (frame : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Equiv.Perm (Fin (r + 1))),
      ∀ (r : ℕ) (p : Cell (r + 1)) (i : Fin (r + 1)) (side : Bool),
        let c := child r p i side
        let A := cubicalSignedPermutation (r + 1) (frame r p i) (fun _ => true)
        c.val.val.1 = i.succAboveEmb.trans p.val.val.1 ∧
        c.val.val.2 = p.val.val.2 + (if side then ε else 0) •
          EuclideanSpace.single (p.val.val.1 i) (1 : ℝ) ∧
        frame r p i i = Fin.last r ∧
        (∀ a : Fin r, frame r p i (i.succAbove a) = a.castSucc) ∧
        (∀ z : Domain (r + 1), (e r (A z)).2 =
          (e r (cubicalSignedFaceIsometry r i true z)).2) ∧
        ∀ z : Domain (r + 1), P (r + 1) p
          (cubicalSignedFaceIsometry (r + 1) i.castSucc side
            ((e (r + 1)).symm (z, EuclideanSpace.single (0 : Fin 1) 1))) = P r c (A z) := by
  classical
  intro Cell e physical P
  let child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r := fun r p i side =>
    ⟨⟨((Fin.succAboveOrderEmb i).toEmbedding.trans p.val.val.1,
      p.val.val.2 + (if side then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ)),
      mem_original_physical_cell_canonical_facet grid offset hε hGrid p.val i side⟩,
      p.property.comp (Fin.succAboveOrderEmb i).strictMono⟩
  have hFrames (r : ℕ) (p : Cell (r + 1)) (i : Fin (r + 1)) :=
    exists_canonical_prism_facet_data p.val.val.1 ε p.val.val.2 i
  choose frame hTimeSlot hSpatialSlots hTime hPhysical using hFrames
  refine ⟨child, frame, ?_⟩
  intro r p i side
  refine ⟨rfl, rfl, hTimeSlot r p i, hSpatialSlots r p i, hTime r p i, ?_⟩
  exact hPhysical r p i side

end StratificationTheory
