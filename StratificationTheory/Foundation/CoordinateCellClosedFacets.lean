module

public import StratificationTheory.Foundation.CoordinateCellNativeSlices
public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate

public section

open HarmonicMaps Set
open scoped BigOperators

namespace StratificationTheory

/-- Every original closed positive coordinate facet lies in its original
closed positive cell, with the exact physical shifted origin and original
canonical tangential coordinate ordering. -/
theorem coordinate_cell_closed_facet_containment {d N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (coord : Fin (d + 1) ↪ Fin N) (y : Domain N)
    (hCell : ∀ t : Domain (d + 1), (∀ k, t k ∈ Icc (0 : ℝ) ε) →
      ∀ k : Fin N, (y + ∑ j, t j • EuclideanSpace.single (coord j) (1 : ℝ)) k ∈ Ioo (-1 : ℝ) 1)
    (i : Fin (d + 1)) (positive : Bool) :
    let pair : Fin d ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last d) i).toEmbedding).trans coord
    let origin := y + (if positive then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)
    ∀ t : Domain d, (∀ k, t k ∈ Icc (0 : ℝ) ε) →
      ∀ k : Fin N, (origin + ∑ j, t j • EuclideanSpace.single (pair j) (1 : ℝ)) k ∈ Ioo (-1 : ℝ) 1 := by
  intro pair origin t ht
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
  let δ : ℝ := if positive then ε else 0
  let T := cubicalSignedFaceIsometry d i true (e.symm (t, EuclideanSpace.single (0 : Fin 1) δ))
  have hδ : δ ∈ Icc (0 : ℝ) ε := by cases positive <;> simp [δ, hε]
  have hT (k : Fin (d + 1)) : T k ∈ Icc (0 : ℝ) ε := by
    obtain ⟨j, rfl⟩ := (Equiv.swap (Fin.last d) i).surjective k
    change cubicalSignedFaceIsometry d i true _ ((Equiv.swap (Fin.last d) i) j) ∈ Icc (0 : ℝ) ε
    rw [cubicalSignedFaceIsometry_apply]
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simp only [ite_true]
      change (e (e.symm (t, EuclideanSpace.single (0 : Fin 1) δ))).2 0 ∈ Icc (0 : ℝ) ε
      rw [e.apply_symm_apply]
      exact hδ
    · rw [if_neg (Fin.castSucc_ne_last a)]
      change (e (e.symm (t, EuclideanSpace.single (0 : Fin 1) δ))).1 a ∈ Icc (0 : ℝ) ε
      rw [e.apply_symm_apply]
      exact ht a
  have hPoint : y + ∑ k : Fin (d + 1), T k • EuclideanSpace.single (coord k) (1 : ℝ) =
      origin + ∑ k : Fin d, t k • EuclideanSpace.single (pair k) (1 : ℝ) := by
    have h := coordinate_cell_native_normal_slice coord y i t δ
    change (y + ∑ k : Fin (d + 1), T k • EuclideanSpace.single (coord k) (1 : ℝ)) =
      y + ∑ k : Fin d, t k • EuclideanSpace.single (pair k) (1 : ℝ) +
        δ • EuclideanSpace.single (coord i) (1 : ℝ) at h
    rw [h]
    dsimp only [origin]
    change (y + _) + δ • _ = (y + δ • _) + _
    abel
  intro k
  rw [← hPoint]
  exact hCell T hT k

end StratificationTheory
