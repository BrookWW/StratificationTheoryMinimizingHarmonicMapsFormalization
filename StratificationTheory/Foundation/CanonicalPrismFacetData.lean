module

public import StratificationTheory.Foundation.OrderedCoordinateFacetEmbedding
public import StratificationTheory.Foundation.PrismSpatialPermutation
public import StratificationTheory.Foundation.CubicalSignedPermutationComposition

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- One genuine finite prism frame identifies every signed spatial facet
with the same canonical ordered lower cell in actual physical space-time.
The finite slot identities expose both its original time and every ordered
spatial lower normal for subsequent native trace lookups.
Both signs use the same frame, and its native time slot is identified
with the actual time coordinate of the parent facet. -/
theorem exists_canonical_prism_facet_data {d N : ℕ}
    (coord : Fin (d + 1) ↪ Fin N) (ε : ℝ) (y : Domain N) (i : Fin (d + 1)) :
    ∃ p : Equiv.Perm (Fin (d + 1)),
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
      let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d + 1) (m := 1)
      let physical := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1)
      let lower := (Fin.succAboveOrderEmb i).toEmbedding.trans coord
      let A := cubicalSignedPermutation (d + 1) p (fun _ => true)
      let parent := fun v : Domain (d + 2) => physical.symm
        (y + ∑ k : Fin (d + 1), (ε / 2 + (ε / 2) * (E v).1 k) •
          EuclideanSpace.single (coord k) (1 : ℝ),
          EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * (E v).2 0))
      let child := fun (side : Bool) (z : Domain (d + 1)) => physical.symm
        ((y + (if side then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)) +
          ∑ k : Fin d, (ε / 2 + (ε / 2) * (e z).1 k) • EuclideanSpace.single (lower k) (1 : ℝ),
          EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * (e z).2 0))
      p i = Fin.last d ∧ (∀ a : Fin d, p (i.succAbove a) = a.castSucc) ∧
      (∀ z, (e (A z)).2 = (e (cubicalSignedFaceIsometry d i true z)).2) ∧
      ∀ (side : Bool) (z : Domain (d + 1)),
        parent (cubicalSignedFaceIsometry (d + 1) i.castSucc side
          (E.symm (z, EuclideanSpace.single (0 : Fin 1) 1))) = child side (A z) := by
  obtain ⟨r, hr, hFacet, _⟩ := exists_ordered_coordinate_facet_affine_embedding coord ε y i
  obtain ⟨pR, hp, hpLast, hR, _hRinv, hTime⟩ := exists_prism_spatial_permutation r
  let σ := Equiv.swap (Fin.last d) i
  let p := σ.trans pR
  let B := cubicalSignedPermutation (d + 1) pR (fun _ => true)
  have hSwap : cubicalSignedFaceIsometry d i true =
      cubicalSignedPermutation (d + 1) σ (fun _ => true) := by
    rw [cubicalSignedFaceIsometry_as_signedPermutation]
    apply congrArg (cubicalSignedPermutation (d + 1) σ)
    funext j
    simp only [ite_self]
  have hComposition : (cubicalSignedFaceIsometry d i true).trans B =
      cubicalSignedPermutation (d + 1) p (fun _ => true) := by
    rw [hSwap, cubicalSignedPermutation_compose]
    apply congrArg (cubicalSignedPermutation (d + 1) p)
    funext j
    simp only [ite_true]
  have hpTime : p i = Fin.last d := by
    change pR (σ i) = Fin.last d
    rw [Equiv.swap_apply_right, hpLast]
  have hpSpatial (a : Fin d) : p (i.succAbove a) = a.castSucc := by
    have ha : σ (r.symm a).castSucc = i.succAbove a := by
      simpa only [Equiv.apply_symm_apply] using hr (r.symm a)
    change pR (σ (i.succAbove a)) = a.castSucc
    rw [← ha, Equiv.swap_apply_self, hp, r.apply_symm_apply]
  refine ⟨p, ?_⟩
  intro e E physical lower A parent child
  have hA (z : Domain (d + 1)) : A z = B (cubicalSignedFaceIsometry d i true z) := by
    exact (congrArg (fun F : Domain (d + 1) ≃ₗᵢ[ℝ] Domain (d + 1) => F z) hComposition).symm
  refine ⟨hpTime, hpSpatial, fun z => ?_, ?_⟩
  · rw [hA]
    exact hTime _
  · intro side z
    have hInvolution := cubical_positive_face_isometry_involutive i z
    have hNative := prism_spatial_facet_coordinates i side
      (cubicalSignedFaceIsometry d i true z) (1 : ℝ)
    change cubicalSignedFaceIsometry (d + 1) i.castSucc side
        (E.symm (cubicalSignedFaceIsometry d i true (cubicalSignedFaceIsometry d i true z),
          EuclideanSpace.single (0 : Fin 1) 1)) =
      E.symm (cubicalSignedFaceIsometry d i side
        (e.symm ((e (cubicalSignedFaceIsometry d i true z)).1,
          EuclideanSpace.single (0 : Fin 1) 1)),
            (e (cubicalSignedFaceIsometry d i true z)).2) at hNative
    rw [hInvolution] at hNative
    dsimp only [parent, child]
    rw [hNative, E.apply_symm_apply, hA, hR, e.apply_symm_apply]
    apply congrArg physical.symm
    apply Prod.ext
    · exact hFacet side (e (cubicalSignedFaceIsometry d i true z)).1
    · rfl

end StratificationTheory
