module

public import StratificationTheory.Foundation.CoordinateCellFacetEmbedding
public import StratificationTheory.Foundation.UnitCubeCoordinateTraces

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Every original coordinate-cell normal chart has the literal selected
base embedding and original physical normal coordinate. -/
theorem coordinate_cell_native_normal_slice {d N : ℕ}
    (coord : Fin (d + 1) ↪ Fin N) (y : Domain N) (i : Fin (d + 1))
    (x : Domain d) (t : ℝ) :
    let pair : Fin d ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last d) i).toEmbedding).trans coord
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let z := cubicalSignedFaceIsometry d i true
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    y + ∑ k : Fin (d + 1), z k • EuclideanSpace.single (coord k) (1 : ℝ) =
      y + ∑ k : Fin d, x k • EuclideanSpace.single (pair k) (1 : ℝ) +
        t • EuclideanSpace.single (coord i) (1 : ℝ) := by
  intro pair e z
  let σ := Equiv.swap (Fin.last d) i
  let z₀ := e.symm (x, EuclideanSpace.single (0 : Fin 1) t)
  have hBase (k : Fin d) : z (σ k.castSucc) = x k := by
    change cubicalSignedFaceIsometry d i true z₀ (σ k.castSucc) = x k
    rw [cubicalSignedFaceIsometry_apply, if_neg (Fin.castSucc_ne_last k)]
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))).1 k = x k
    rw [e.apply_symm_apply]
  have hLast : z (σ (Fin.last d)) = t := by
    change cubicalSignedFaceIsometry d i true z₀ (σ (Fin.last d)) = t
    rw [cubicalSignedFaceIsometry_apply, if_pos rfl, if_pos rfl]
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))).2 0 = t
    rw [e.apply_symm_apply]
    rfl
  rw [← Equiv.sum_comp σ, Fin.sum_univ_castSucc]
  simp only [hBase, hLast, σ, Equiv.swap_apply_left]
  rw [add_assoc]
  simp only [pair, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Fin.castSuccEmb_apply]

/-- Original selected-base physical curves are the actual coordinate
curves of the same complete raw coordinate-cell map, including both raw
endpoint classes. -/
theorem coordinate_cell_original_trace_transport {d N q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w : Domain N → Ambient q) (coord : Fin (d + 1) ↪ Fin N) (y : Domain N) :
    let pair := fun i : Fin (d + 1) =>
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last d) i).toEmbedding).trans coord
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let S := ⋂ k : Fin d, (EuclideanSpace.proj k) ⁻¹' Ioo (0 : ℝ) ε
    let u := fun z : Domain (d + 1) => w (y + ∑ k, z k • EuclideanSpace.single (coord k) (1 : ℝ))
    let F := fun i (x : Domain d) (t : ℝ) => w
      (y + ∑ k, x k • EuclideanSpace.single (pair i k) (1 : ℝ) + t • EuclideanSpace.single (coord i) (1 : ℝ))
    ∀ H : Fin (d + 1) → C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => F i x t) 2 (volume.restrict S),
        H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F i x t)) →
    (∀ i (positive : Bool),
      ∃ hs : MemLp (fun x => F i x (if positive then ε else 0)) 2 (volume.restrict S),
        H i ⟨if positive then ε else 0, by cases positive <;> simp [hε.le],
            by cases positive <;> simp [hε.le]⟩ = hs.toLp (fun x => F i x (if positive then ε else 0))) →
    (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => u (cubicalSignedFaceIsometry d i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u (cubicalSignedFaceIsometry d i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
    ∀ i (positive : Bool),
      ∃ hs : MemLp (fun x => u (cubicalSignedFaceIsometry d i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0))))) 2 (volume.restrict S),
        H i ⟨if positive then ε else 0, by cases positive <;> simp [hε.le],
            by cases positive <;> simp [hε.le]⟩ = hs.toLp (fun x => u (cubicalSignedFaceIsometry d i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0))))) := by
  intro pair e S u F H hH hEnd
  have hRaw (i : Fin (d + 1)) (x : Domain d) (t : ℝ) :
      F i x t = u (cubicalSignedFaceIsometry d i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) :=
    congrArg w (coordinate_cell_native_normal_slice coord y i x t).symm
  constructor
  · intro i
    simpa only [hRaw] using hH i
  · intro i positive
    simpa only [hRaw] using hEnd i positive

end StratificationTheory
