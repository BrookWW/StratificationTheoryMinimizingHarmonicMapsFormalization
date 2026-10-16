module

public import StratificationTheory.Foundation.UnitCubeFaceL2Trace
public import StratificationTheory.Foundation.CubicalSignedFaceCoordinate

/-!
# Original square coordinate traces under the same unit chart

Both original physical coordinate curves normalize by the same full affine
square chart. Their signed endpoint classes are the literal restrictions
of that same raw normalized square map.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

private theorem square_cap_coordinates (x : Domain 1) (t : ℝ) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
      (x, EuclideanSpace.single (0 : Fin 1) t) = WithLp.toLp 2 ![x 0, t] := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  apply e.injective
  rw [e.apply_symm_apply]
  apply Prod.ext <;> ext j <;> fin_cases j <;> rfl

/-- The actual positive square face axis commutes with its positive
affine cube normalization. -/
theorem affine_unit_square_axis_coordinates (i : Fin 2) (ε : ℝ)
    (x : Domain 1) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let a : Domain 1 := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    A + (ε / 2) • cubicalSignedFaceIsometry 1 i true
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
      cubicalSignedFaceIsometry 1 i true
        (e.symm (a + (ε / 2) • x,
          EuclideanSpace.single (0 : Fin 1) ((ε / 2) * (t + 1)))) := by
  intro e a A
  rw [square_cap_coordinates, square_cap_coordinates]
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [cubicalSignedFaceIsometry_coordinate, Fin.last, a, A]
  all_goals ring

/-- Every signed unit edge has the original physical edge as its exact
full-chart image, with the same positive spatial base normalization. -/
theorem affine_unit_square_axis_endpoint (i : Fin 2) (positive : Bool) (ε : ℝ)
    (x : Domain 1) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let a : Domain 1 := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    A + (ε / 2) • cubicalSignedFaceIsometry 1 i positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) =
      cubicalSignedFaceIsometry 1 i true
        (e.symm (a + (ε / 2) • x,
          EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0))) := by
  intro e a A
  rw [square_cap_coordinates, square_cap_coordinates]
  ext k
  cases positive <;> fin_cases i <;> fin_cases k <;>
    simp [cubicalSignedFaceIsometry_coordinate, Fin.last, a, A]

/-- The physical coordinate curves yield both native coordinate curves of
the actual normalized square, with all four original raw edge classes. -/
theorem exists_unit_square_coordinate_traces {q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (u : Domain 2 → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let S : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let C : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun y : Domain 2 => A + (ε / 2) • y
    let U := u ∘ T
    ∀ H : Fin 2 → C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ i, ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => u (cubicalSignedFaceIsometry 1 i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)))) 2 (volume.restrict S),
        H i ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => u (cubicalSignedFaceIsometry 1 i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))))) →
    (∀ i (positive : Bool),
      ∃ hs : MemLp (fun x => u (cubicalSignedFaceIsometry 1 i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0)))))
          2 (volume.restrict S),
        H i ⟨if positive then ε else 0, by cases positive <;> simp [hε.le],
            by cases positive <;> simp [hε.le]⟩ = hs.toLp
          (fun x => u (cubicalSignedFaceIsometry 1 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then ε else 0)))))) →
    ∃ K : Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U (cubicalSignedFaceIsometry 1 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U (cubicalSignedFaceIsometry 1 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ i (positive : Bool),
        ∃ hs : MemLp (fun x => U (cubicalSignedFaceIsometry 1 i positive
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C),
          K i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
              by cases positive <;> norm_num⟩ = hs.toLp
            (fun x => U (cubicalSignedFaceIsometry 1 i positive
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  intro e S C A T U H hH hEnd
  let a : Domain 1 := WithLp.toLp 2 (fun _ => ε / 2)
  let G := fun x : Domain 1 => a + (ε / 2) • x
  let f := fun i (p : Domain 1 × ℝ) => u (cubicalSignedFaceIsometry 1 i true
    (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
  have hK (i : Fin 2) := exists_unit_cube_face_L2_trace_normalization
    (n := 1) (E := Ambient q) (f := f i) hε (H i) (hH i)
    (hEnd i false).choose (hEnd i true).choose
    (hEnd i false).choose_spec (hEnd i true).choose_spec
  choose K hKraw hKleft hKright _hKunique using hK
  refine ⟨K, ?_, ?_⟩
  · intro i
    filter_upwards [hKraw i] with t ht htI
    have hfun : (fun x => f i (G x, (ε / 2) * (t + 1))) =
        (fun x => U (cubicalSignedFaceIsometry 1 i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
      funext x
      exact congrArg u (affine_unit_square_axis_coordinates i ε x t).symm
    have hp := ht htI
    rw [hfun] at hp
    exact hp
  · intro i positive
    have hfun : (fun x => f i (G x, if positive then ε else 0)) =
        (fun x => U (cubicalSignedFaceIsometry 1 i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
      funext x
      exact congrArg u (affine_unit_square_axis_endpoint i positive ε x).symm
    cases positive
    · obtain ⟨hs, heq⟩ := hKleft i
      have hs' : MemLp (fun x => f i (G x, 0)) 2 (volume.restrict C) := hs
      have hnew : MemLp (fun x => U (cubicalSignedFaceIsometry 1 i false
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C) :=
        hs'.ae_eq (Eventually.of_forall fun x => congrFun hfun x)
      exact ⟨hnew, heq.trans (hs'.toLp_congr hnew (Eventually.of_forall fun x => congrFun hfun x))⟩
    · obtain ⟨hs, heq⟩ := hKright i
      have hs' : MemLp (fun x => f i (G x, ε)) 2 (volume.restrict C) := hs
      have hnew : MemLp (fun x => U (cubicalSignedFaceIsometry 1 i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C) :=
        hs'.ae_eq (Eventually.of_forall fun x => congrFun hfun x)
      exact ⟨hnew, heq.trans (hs'.toLp_congr hnew (Eventually.of_forall fun x => congrFun hfun x))⟩

end StratificationTheory
