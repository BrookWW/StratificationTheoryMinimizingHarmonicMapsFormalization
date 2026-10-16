module

public import StratificationTheory.Foundation.PrismFacetCoordinates
public import StratificationTheory.Foundation.CoordinateCellFacetEmbedding
public import StratificationTheory.Foundation.IndependentTimeIsometry

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- An actual signed cell facet is the canonical ordered lower cell under
one genuine finite coordinate isometry. The original shifted physical
origin and the whole normalized parameterization agree exactly. -/
theorem exists_ordered_coordinate_facet_affine_embedding {d N : ℕ}
    (coord : Fin (d + 1) ↪ Fin N) (ε : ℝ) (y : Domain N)
    (i : Fin (d + 1)) :
    ∃ r : Equiv.Perm (Fin d),
      let pair := (Fin.succAboveOrderEmb i).toEmbedding.trans coord
      let R := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ r
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
      (∀ j : Fin d, (Equiv.swap (Fin.last d) i) j.castSucc = i.succAbove (r j)) ∧
      (∀ (positive : Bool) (x : Domain d),
        let cap := cubicalSignedFaceIsometry d i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
        y + ∑ k : Fin (d + 1), (ε / 2 + (ε / 2) * cap k) •
            EuclideanSpace.single (coord k) (1 : ℝ) =
          (y + (if positive then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)) +
            ∑ a : Fin d, (ε / 2 + (ε / 2) * R x a) • EuclideanSpace.single (pair a) (1 : ℝ)) ∧
      ∃ Q : Domain (d + 1) ≃ₗᵢ[ℝ] Domain (d + 1),
        (∀ z, Q z = e.symm (R (e z).1, (e z).2)) ∧
        (∀ z, Q.symm z = e.symm (R.symm (e z).1, (e z).2)) ∧
        ∀ z, (e (Q z)).2 = (e z).2 := by
  obtain ⟨r, hr⟩ := exists_ordered_facet_swap_permutation i
  refine ⟨r, ?_⟩
  intro pair R e
  obtain ⟨Q, hQ, hQinv, hTime⟩ := exists_independent_time_isometry R
  refine ⟨hr, ?_, Q, hQ, hQinv, hTime⟩
  intro positive x cap
  have hR (j : Fin d) : R x (r j) = x j := by
    simp [R, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have hSum :
      (∑ j : Fin d, (ε / 2 + (ε / 2) * x j) •
        EuclideanSpace.single (coord ((Equiv.swap (Fin.last d) i) j.castSucc)) (1 : ℝ)) =
      ∑ a : Fin d, (ε / 2 + (ε / 2) * R x a) • EuclideanSpace.single (pair a) (1 : ℝ) := by
    conv_rhs => rw [← Equiv.sum_comp r]
    apply Finset.sum_congr rfl
    intro j _
    rw [hR, hr]
    rfl
  have h := coordinate_cell_signed_facet_affine_embedding coord ε y i positive x
  change y + ∑ k : Fin (d + 1), (ε / 2 + (ε / 2) * cap k) •
      EuclideanSpace.single (coord k) (1 : ℝ) =
    (y + (if positive then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)) +
      ∑ j : Fin d, (ε / 2 + (ε / 2) * x j) •
        EuclideanSpace.single (coord ((Equiv.swap (Fin.last d) i) j.castSucc)) (1 : ℝ) at h
  exact h.trans (congrArg (fun v : Domain N =>
    (y + (if positive then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)) + v) hSum)

end StratificationTheory
