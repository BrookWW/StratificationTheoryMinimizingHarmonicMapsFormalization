module
public import StratificationTheory.Foundation.RawVertexUnitChordBounds
public import StratificationTheory.Foundation.GridCubeBallContainment

/-!
# The original vertex base on a fixed selected lattice

Original selected raw vertex membership supplies the actual affine
rank-zero graph, its native curve, and its target-distance bound.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The original selected vertex event gives the literal rank-zero base
without choosing another offset or using a higher-dimensional point trace. -/
theorem original_selected_vertex_chord_base {n q : ℕ}
    (u : Fin 2 → Domain (n + 1) → Ambient q) {N : Set (Ambient q)}
    {ε : ℝ} (hε : 0 < ε) (offset : Fin (n + 1) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _ : Fin (n + 1) => ε) (fun _ => hε.ne'.isUnit)
    (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2),
      WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset) ∈ ball (0 : Domain (n + 1)) ((n : ℝ) + 2) →
        u l (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) ∈ N) →
    ∀ z : Submodule.span ℤ (Set.range grid),
    let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
    (∀ i, y i ∈ Ioo (-1 : ℝ) 1) →
    let B : OpenDomain 1 :=
      ⟨⋂ i : Fin 1, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let C : Set (Domain 0) := ⋂ i : Fin 0, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 0) (m := 1)
    (∀ l, u l y ∈ N) ∧
    MemW12 B (rawVertexUnitChord u y) (rawVertexUnitGradient u y) ∧
    (∀ M : ℝ, (∀ v ∈ N, ‖v‖ ≤ M) → ∀ x : Domain 1, x 0 ∈ Icc (-1 : ℝ) 1 →
      ‖rawVertexUnitChord u y x‖ ≤ M) ∧
    (∀ x : Domain 1, x 0 ∈ Icc (-1 : ℝ) 1 →
      (infDist (rawVertexUnitChord u y x) N) ^ 2 ≤ ‖u 0 y - u 1 y‖ ^ 2) ∧
    ∃ K : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ t : Icc (-1 : ℝ) 1, ∃ hs : MemLp
        (fun x : Domain 0 => rawVertexUnitChord u y (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
          2 (volume.restrict C), K t = hs.toLp
        (fun x : Domain 0 => rawVertexUnitChord u y (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      ∀ side : Bool, ∃ hs : MemLp (fun _ : Domain 0 => u (if side then 1 else 0) y)
          2 (volume.restrict C),
        K ⟨if side then 1 else -1, by cases side <;> norm_num, by cases side <;> norm_num⟩ =
          hs.toLp (fun _ : Domain 0 => u (if side then 1 else 0) y) := by
  intro grid hVertexN z y hy B C e
  have hyBall : y ∈ ball (0 : Domain (n + 1)) ((n : ℝ) + 2) := by
    rw [mem_ball_zero_iff]
    have hnorm := euclidean_norm_le_dim_of_coordinate_bound y
      (fun i => abs_le.mpr ⟨(hy i).1.le, (hy i).2.le⟩)
    push_cast at hnorm
    linarith
  have hValues (l : Fin 2) : u l y ∈ N := hVertexN z l hyBall
  refine ⟨hValues, rawVertexUnitChord_memW12 u y, ?_, ?_, ?_⟩
  · intro M hM x hx
    exact rawVertexUnitChord_norm_le u y (fun l => hM _ (hValues l)) x hx
  · intro x hx
    exact rawVertexUnitChord_infDist_sq_le u y (hValues 0) x hx
  · exact exists_rawVertexUnitChord_trace u y

end StratificationTheory
