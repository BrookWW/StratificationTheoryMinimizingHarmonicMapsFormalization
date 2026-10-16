module

public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- The true last signed face chart acts only on its normal time value,
with every original spatial coordinate unchanged. -/
theorem cubical_signed_last_face_split {d : ℕ} (side : Bool) (x : Domain d) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    cubicalSignedFaceIsometry d (Fin.last d) side
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
        e.symm (x, EuclideanSpace.single (0 : Fin 1) (if side then t else -t)) := by
  intro e
  have hBase (v : Domain d) (s : Domain 1) (j : Fin d) : e.symm (v, s) j.castSucc = v j := by
    change (e (e.symm (v, s))).1 j = v j
    rw [e.apply_symm_apply]
  have hLast (v : Domain d) (s : Domain 1) : e.symm (v, s) (Fin.last d) = s 0 := by
    change (e (e.symm (v, s))).2 0 = s 0
    rw [e.apply_symm_apply]
  ext j
  induction j using Fin.lastCases with
  | last =>
    rw [cubicalSignedFaceIsometry_coordinate, if_pos rfl, hLast, hLast]
    simp
  | cast j =>
    rw [cubicalSignedFaceIsometry_coordinate, if_neg (Fin.castSucc_ne_last j)]
    simp only [Equiv.swap_self, Equiv.refl_apply, hBase]

/-- The original physical prism at either actual time cap has exactly
the original normalized spatial point and the original time zero or epsilon.
This whole-carrier identity uses no trace or weak-map assumption. -/
theorem canonical_prism_time_cap_physical_embedding {d N : ℕ}
    (coord : Fin d ↪ Fin N) (ε : ℝ) (y : Domain N) (side : Bool) (x : Domain d) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1)
    let chart := fun z : Domain (d + 1) => E.symm
      (y + ∑ j : Fin d, (ε / 2 + (ε / 2) * (e z).1 j) •
        EuclideanSpace.single (coord j) (1 : ℝ),
        EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * (e z).2 0))
    chart (cubicalSignedFaceIsometry d (Fin.last d) side
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) =
      E.symm (y + ∑ j : Fin d, (ε / 2 + (ε / 2) * x j) •
        EuclideanSpace.single (coord j) (1 : ℝ),
          EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)) := by
  intro e E chart
  have hCap := cubical_signed_last_face_split side x (1 : ℝ)
  dsimp only [chart]
  rw [hCap, e.apply_symm_apply]
  apply congrArg E.symm
  apply Prod.ext
  · rfl
  · congr 1
    cases side <;> simp

end StratificationTheory
