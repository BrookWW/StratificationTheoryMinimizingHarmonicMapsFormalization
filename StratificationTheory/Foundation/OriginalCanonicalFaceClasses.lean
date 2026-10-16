module

public import StratificationTheory.Foundation.OrderedCoordinateFacetEmbedding
public import StratificationTheory.Foundation.UnitCubeCoordinateTraces

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Every original normalized face class is the same global canonical
lower-cell raw map in one actual finite native coordinate frame. The
pointwise chart identity supplies the endpoint class without choosing
another original representative or a lattice offset. -/
theorem exists_original_canonical_face_classes {d N q : ℕ}
    (w : Domain N → Ambient q) (coord : Fin (d + 1) ↪ Fin N)
    (y : Domain N) (ε : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let S := ⋂ j : Fin d, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let U := fun z : Domain (d + 1) => w (y + ∑ j : Fin (d + 1),
      (ε / 2 + (ε / 2) * z j) • EuclideanSpace.single (coord j) (1 : ℝ))
    let lower := fun i : Fin (d + 1) => i.succAboveEmb.trans coord
    let child := fun (i : Fin (d + 1)) (side : Bool) (x : Domain d) => w
      ((y + (if side then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)) +
        ∑ a : Fin d, (ε / 2 + (ε / 2) * x a) • EuclideanSpace.single (lower i a) (1 : ℝ))
    ∀ K : Fin (d + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ i side,
      (K i ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain d → Ambient q) =ᵐ[volume.restrict S]
        (fun x => U (cubicalSignedFaceIsometry d i side
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) →
    ∃ r : Fin (d + 1) → Equiv.Perm (Fin d),
      ∀ i,
        let R := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (r i)
        (∀ j : Fin d, (Equiv.swap (Fin.last d) i) j.castSucc = i.succAbove (r i j)) ∧
        (∀ (side : Bool) (x : Domain d), U (cubicalSignedFaceIsometry d i side
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = child i side (R x)) ∧
        ∀ side : Bool,
          (K i ⟨if side then 1 else -1, by cases side <;> norm_num,
            by cases side <;> norm_num⟩ : Domain d → Ambient q) =ᵐ[volume.restrict S]
              child i side ∘ R := by
  classical
  intro e S U lower child K hEnd
  have hData (i : Fin (d + 1)) := exists_ordered_coordinate_facet_affine_embedding coord ε y i
  choose r hSlots hChart _hLift using hData
  refine ⟨r, fun i => ⟨hSlots i, ?_, ?_⟩⟩
  · intro side x
    exact congrArg w (hChart i side x)
  · intro side
    filter_upwards [hEnd i side] with x hx
    exact hx.trans (congrArg w (hChart i side x))

end StratificationTheory
