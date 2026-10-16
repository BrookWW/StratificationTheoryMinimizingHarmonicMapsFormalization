module

public import StratificationTheory.Foundation.GridNeighborCoordinates
public import StratificationTheory.Foundation.CoordinateCellNativeSlices

/-! # Actual lattice origins of every closed positive cubical edge -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

private theorem grid_positive_axis_mem {d : ℕ} {ε : ℝ}
    (i : Fin (d + 1)) (x : Domain d) (r : ℝ)
    (hx : ∀ k, x k ∈ Icc (0 : ℝ) ε) (hr : r ∈ Icc (0 : ℝ) ε) :
    ∀ k : Fin (d + 1),
      (cubicalSignedFaceIsometry d i true
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) r))) k ∈ Icc (0 : ℝ) ε := by
  intro k
  let σ := Equiv.swap (Fin.last d) i
  obtain ⟨j, rfl⟩ := σ.surjective k
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [cubicalSignedFaceIsometry_apply]
    simp only [ite_true]
    change ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1))
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) r))).2 0 ∈ Icc (0 : ℝ) ε
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hr
  · rw [cubicalSignedFaceIsometry_apply]
    simp only [Fin.castSucc_ne_last, ite_false]
    change ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1))
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) r))).1 j ∈ Icc (0 : ℝ) ε
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hx j

/-- Every actual cubical edge origin is an explicit finite sum of the
original lattice generators. Its entire affine edge equals the original
positive cube chart, and its closed segment stays in the parent cell. -/
theorem exists_scaled_grid_cube_edge_offsets {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let I := Fin (n + 2) × (Fin (n + 1) → Bool)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let vertex := fun i : I => (WithLp.toLp 2 (fun j : Fin (n + 1) => if i.2 j then ε else 0) : Domain (n + 1))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    ∃ shift : I → L, ∀ (i : I) (z : L) (s : ℝ),
      y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
        y z + cubicalSignedFaceIsometry (n + 1) i.1 true
          (e.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s)) ∧
      (s ∈ Icc (0 : ℝ) ε → ∀ j,
        (y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ)) j - (y z) j ∈ Icc (0 : ℝ) ε) := by
  intro grid L I y vertex e
  let step : Fin (n + 2) → L := fun j => ⟨grid j, Submodule.subset_span ⟨j, rfl⟩⟩
  let σ := fun i : I => Equiv.swap (Fin.last (n + 1)) i.1
  let shift : I → L := fun i => ∑ j : Fin (n + 1), if i.2 j then step (σ i j.castSucc) else 0
  let V := fun i : I => ∑ j : Fin (n + 1), (vertex i) j • EuclideanSpace.single (σ i j.castSucc) (1 : ℝ)
  have hGrid (j : Fin (n + 2)) : grid j = ε • (Pi.single j (1 : ℝ) : Fin (n + 2) → ℝ) := by
    simp only [grid, Basis.isUnitSMul_apply, Pi.basisFun_apply]
  have hShift (i : I) : WithLp.toLp 2 ((shift i : L) : Fin (n + 2) → ℝ) = V i := by
    ext k
    simp only [shift, V, Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    cases hside : i.2 j
    · simp [hside, vertex]
    · simp only [hside, ite_true, step, Submodule.coe_mk, hGrid, vertex]
      rfl
  have hYShift (i : I) (z : L) : y (z + shift i) = y z + V i := by
    ext k
    have h := congrArg (fun x : Domain (n + 2) => x k) (hShift i)
    change ((shift i : L) : Fin (n + 2) → ℝ) k = (V i) k at h
    change ((z : Fin (n + 2) → ℝ) k + ((shift i : L) : Fin (n + 2) → ℝ) k) + offset k =
      ((z : Fin (n + 2) → ℝ) k + offset k) + (V i) k
    rw [h]
    ring
  have hRepr (x : Domain (n + 2)) :
      (∑ k : Fin (n + 2), x k • EuclideanSpace.single k (1 : ℝ)) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).sum_repr x
  have hChart (i : I) (s : ℝ) :
      cubicalSignedFaceIsometry (n + 1) i.1 true (e.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s)) =
        V i + s • EuclideanSpace.single i.1 (1 : ℝ) := by
    have h := coordinate_cell_native_normal_slice (Function.Embedding.refl (Fin (n + 2)))
      (0 : Domain (n + 2)) i.1 (vertex i) s
    simpa only [Function.Embedding.refl_apply, zero_add, hRepr,
      Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Fin.castSuccEmb_apply, V, σ, e] using h
  refine ⟨shift, ?_⟩
  intro i z s
  have hEdge : y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
      y z + cubicalSignedFaceIsometry (n + 1) i.1 true
        (e.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s)) := by
    rw [hYShift, hChart, add_assoc]
  refine ⟨hEdge, ?_⟩
  intro hs j
  rw [hEdge]
  simp only [PiLp.add_apply, add_sub_cancel_left]
  exact grid_positive_axis_mem i.1 (vertex i) s
    (fun k => by cases hside : i.2 k <;> simp [vertex, hside, hε.le]) hs j

end StratificationTheory
