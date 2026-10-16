module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Algebra.BigOperators.Fin

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- The actual affine normalization of a signed coordinate-cell facet is
exactly the lower-dimensional original coordinate embedding, with its
physical origin shifted only in the selected normal coordinate. -/
theorem coordinate_cell_signed_facet_affine_embedding {d N : ℕ}
    (coord : Fin (d + 1) ↪ Fin N) (ε : ℝ) (y : Domain N)
    (i : Fin (d + 1)) (positive : Bool) (x : Domain d) :
    let pair : Fin d ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last d) i).toEmbedding).trans coord
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let T : Domain (d + 1) → Domain (d + 1) := fun z =>
      WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let t : Domain d := WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • x
    let cap := cubicalSignedFaceIsometry d i positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
    y + ∑ k : Fin (d + 1), (T cap) k • EuclideanSpace.single (coord k) (1 : ℝ) =
      (y + (if positive then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)) +
        ∑ k : Fin d, t k • EuclideanSpace.single (pair k) (1 : ℝ) := by
  intro pair e T t cap
  let σ := Equiv.swap (Fin.last d) i
  let z := e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)
  have hBase (k : Fin d) : z k.castSucc = x k := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).1 k = x k
    rw [e.apply_symm_apply]
  have hLast : z (Fin.last d) = 1 := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))).2 0 = 1
    rw [e.apply_symm_apply]
    rfl
  have hTangential (k : Fin d) : (T cap) (σ k.castSucc) = t k := by
    change ε / 2 + (ε / 2) * (cubicalSignedFaceIsometry d i positive z (σ k.castSucc)) =
      ε / 2 + (ε / 2) * x k
    rw [cubicalSignedFaceIsometry_apply, if_neg (Fin.castSucc_ne_last k), hBase]
  have hNormal : (T cap) (σ (Fin.last d)) = if positive then ε else 0 := by
    change ε / 2 + (ε / 2) * (cubicalSignedFaceIsometry d i positive z (σ (Fin.last d))) = _
    rw [cubicalSignedFaceIsometry_apply, if_pos rfl, hLast]
    cases positive <;> norm_num
  have hSum : (∑ k : Fin (d + 1), (T cap) k • EuclideanSpace.single (coord k) (1 : ℝ)) =
      (∑ k : Fin d, t k • EuclideanSpace.single (pair k) (1 : ℝ)) +
        (if positive then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ) := by
    rw [← Equiv.sum_comp σ, Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _hk
      rw [hTangential]
      rfl
    · rw [hNormal]
      simp only [σ, Equiv.swap_apply_left]
  rw [hSum]
  abel

end StratificationTheory
