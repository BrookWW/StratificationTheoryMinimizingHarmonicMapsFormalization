module

public import StratificationTheory.Foundation.UnitCubeFaceL2Trace
public import StratificationTheory.Foundation.CubicalSignedFrameBlock

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- The same positive affine cube normalization commutes with every
original positive coordinate-normal chart in every dimension. -/
theorem affine_unit_cube_axis_coordinates {n : ℕ} (i : Fin (n + 1)) (ε : ℝ)
    (x : Domain n) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain (n + 1) := WithLp.toLp 2 (fun _ => ε / 2)
    A + (ε / 2) • cubicalSignedFaceIsometry n i true
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
      cubicalSignedFaceIsometry n i true
        (e.symm (a + (ε / 2) • x,
          EuclideanSpace.single (0 : Fin 1) ((ε / 2) * (t + 1)))) := by
  intro e a A
  let Q := cubicalSignedFaceIsometry n i true
  have hA : Q A = A := by
    ext l
    obtain ⟨k, rfl⟩ := (Equiv.swap (Fin.last n) i).surjective l
    rw [cubicalSignedFaceIsometry_apply]
    simp only [ite_true, ite_self]
    rfl
  calc
    _ = Q (A + (ε / 2) • e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) := by
      rw [Q.map_add, Q.map_smul, hA]
    _ = _ := congrArg Q (affine_unit_cube_split_coordinates n ε x t)

/-- Both signed endpoints use the same original positive physical chart
and its exact original endpoint height. -/
theorem affine_unit_cube_axis_endpoint {n : ℕ} (i : Fin (n + 1)) (positive : Bool) (ε : ℝ)
    (x : Domain n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain (n + 1) := WithLp.toLp 2 (fun _ => ε / 2)
    A + (ε / 2) • cubicalSignedFaceIsometry n i positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) =
      cubicalSignedFaceIsometry n i true
        (e.symm (a + (ε / 2) • x,
          EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0))) := by
  intro e a A
  rw [cubical_signed_face_native_height, affine_unit_cube_axis_coordinates]
  have hScalar : (ε / 2) * ((if positive then (1 : ℝ) else -1) + 1) =
      if positive then ε else 0 := by cases positive <;> norm_num
  exact congrArg (fun r => cubicalSignedFaceIsometry n i true
    (e.symm (a + (ε / 2) • x, EuclideanSpace.single (0 : Fin 1) r))) hScalar

/-- The original physical coordinate curves normalize by the same full
affine cube chart, with both original raw signed-face endpoint classes. -/
theorem exists_unit_cube_coordinate_traces {n q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (u : Domain (n + 1) → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let S : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let C : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let A : Domain (n + 1) := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun y : Domain (n + 1) => A + (ε / 2) • y
    let U := u ∘ T
    ∀ H : Fin (n + 1) → C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ i, ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => u (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)))) 2 (volume.restrict S),
        H i ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => u (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))))) →
    (∀ i (positive : Bool),
      ∃ hs : MemLp (fun x => u (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0)))))
          2 (volume.restrict S),
        H i ⟨if positive then ε else 0, by cases positive <;> simp [hε.le],
            by cases positive <;> simp [hε.le]⟩ = hs.toLp
          (fun x => u (cubicalSignedFaceIsometry n i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0)))))) →
    ∃ K : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U (cubicalSignedFaceIsometry n i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U (cubicalSignedFaceIsometry n i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ i (positive : Bool),
        ∃ hs : MemLp (fun x => U (cubicalSignedFaceIsometry n i positive
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C),
          K i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
              by cases positive <;> norm_num⟩ = hs.toLp
            (fun x => U (cubicalSignedFaceIsometry n i positive
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  intro e S C A T U H hH hEnd
  let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
  let G := fun x : Domain n => a + (ε / 2) • x
  let f := fun i (p : Domain n × ℝ) => u (cubicalSignedFaceIsometry n i true
    (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
  have hK (i : Fin (n + 1)) := exists_unit_cube_face_L2_trace_normalization
    (n := n) (E := Ambient q) (f := f i) hε (H i) (hH i)
    (hEnd i false).choose (hEnd i true).choose
    (hEnd i false).choose_spec (hEnd i true).choose_spec
  choose K hKraw hKleft hKright _hKunique using hK
  refine ⟨K, ?_, ?_⟩
  · intro i
    filter_upwards [hKraw i] with t ht htI
    have hfun : (fun x => f i (G x, (ε / 2) * (t + 1))) =
        (fun x => U (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
      funext x
      exact congrArg u (affine_unit_cube_axis_coordinates i ε x t).symm
    have hp := ht htI
    rw [hfun] at hp
    exact hp
  · intro i positive
    have hfun : (fun x => f i (G x, if positive then ε else 0)) =
        (fun x => U (cubicalSignedFaceIsometry n i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
      funext x
      exact congrArg u (affine_unit_cube_axis_endpoint i positive ε x).symm
    cases positive
    · obtain ⟨hs, heq⟩ := hKleft i
      have hs' : MemLp (fun x => f i (G x, 0)) 2 (volume.restrict C) := hs
      have hnew : MemLp (fun x => U (cubicalSignedFaceIsometry n i false
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C) :=
        hs'.ae_eq (Eventually.of_forall fun x => congrFun hfun x)
      exact ⟨hnew, heq.trans (hs'.toLp_congr hnew (Eventually.of_forall fun x => congrFun hfun x))⟩
    · obtain ⟨hs, heq⟩ := hKright i
      have hs' : MemLp (fun x => f i (G x, ε)) 2 (volume.restrict C) := hs
      have hnew : MemLp (fun x => U (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C) :=
        hs'.ae_eq (Eventually.of_forall fun x => congrFun hfun x)
      exact ⟨hnew, heq.trans (hs'.toLp_congr hnew (Eventually.of_forall fun x => congrFun hfun x))⟩

end StratificationTheory
