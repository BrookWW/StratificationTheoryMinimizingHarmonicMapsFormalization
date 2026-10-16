module

public import StratificationTheory.Foundation.CubicalSignedFaceCharts
public import StratificationTheory.Foundation.CubicalConeGeometry
public import StratificationTheory.Foundation.SpatialBlockIsometry
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback

public section

open HarmonicMaps MeasureTheory Set
open scoped BigOperators

namespace StratificationTheory

/-- A cube-preserving oriented ambient frame transports the original
canonical face weak pair to the same raw face in that frame. Its spatial
weak columns and exact native energy are produced internally. -/
theorem exists_cubical_face_pair_in_ambient_frame {n q : ℕ}
    (i : Fin (n + 1)) (positive : Bool)
    (G : Domain (n + 1) → Ambient q) (Df : Domain n → Gradient n q)
    (A : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1)) :
    let Q := cubicalSignedFaceIsometry n i positive
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let f : Domain n → Ambient q := fun x => G (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let fA : Domain n → Ambient q := fun x => G (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let B : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    MemW12 B f Df →
    (∀ y, ‖WithLp.ofLp (A y)‖ = ‖WithLp.ofLp y‖) →
    (∀ y, (if positive then (A y) i else -(A y) i) = (e y).2 0) →
    ∃ DA : Domain n → Gradient n q, MemW12 B fA DA ∧
      (∫ x in B.val, hsNormSq (DA x)) = ∫ x in B.val, hsNormSq (Df x) := by
  intro Q e f fA B hf hMax hNormal
  let C := A.trans Q.symm
  have hTime (y : Domain (n + 1)) : (e (C y)).2 = (e y).2 := by
    ext l
    have hl : l = 0 := Subsingleton.elim _ _
    subst l
    change Q.symm (A y) (Fin.last n) = (e y).2 0
    rw [cubicalSignedFaceIsometry_symm_apply, if_pos rfl]
    exact hNormal y
  have hQMaxInv (y : Domain (n + 1)) : ‖WithLp.ofLp (Q.symm y)‖ = ‖WithLp.ofLp y‖ := by
    have h := cubicalSignedFaceIsometry_coordinate_norm i positive (Q.symm y)
    rw [Q.apply_symm_apply] at h
    exact h.symm
  have hCMax (y : Domain (n + 1)) : ‖WithLp.ofLp (C y)‖ = ‖WithLp.ofLp y‖ :=
    (hQMaxInv (A y)).trans (hMax y)
  obtain ⟨R, ⟨hBlock, hRMax⟩, _hRunique⟩ := exists_unique_spatial_block_isometry C hTime hCMax
  have hFace (x : Domain n) : A (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) =
      Q (e.symm (R x, EuclideanSpace.single (0 : Fin 1) 1)) := by
    have h := congrArg Q (hBlock x (EuclideanSpace.single (0 : Fin 1) 1))
    simpa only [C, LinearIsometryEquiv.trans_apply, Q.apply_symm_apply] using h
  have hRaw : f ∘ R = fA := by
    funext x
    exact congrArg G (hFace x).symm
  have hCube (x : Domain n) : x ∈ B.val ↔ ‖WithLp.ofLp x‖ < 1 := by
    rw [mem_unit_coordinate_face_iff, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.norm_eq_abs]
  have hset : R ⁻¹' B.val = B.val := by
    ext x
    change R x ∈ B.val ↔ x ∈ B.val
    rw [hCube, hCube, hRMax]
  let B' : OpenDomain n := ⟨R ⁻¹' B.val, B.property.preimage R.continuous⟩
  have hB : B' = B := Subtype.ext hset
  let DA : Domain n → Gradient n q := fun x j =>
    ∑ k : Fin n, (R (EuclideanSpace.single j 1)) k • Df (R x) k
  have hPull := memW12_isometric_preimage_energy (volume_unit_coordinate_face_ne_top n) hf R
  refine ⟨DA, ?_, ?_⟩
  · have hW : MemW12 B' (f ∘ R) DA := hPull.1
    rwa [hB, hRaw] at hW
  · have hE : (∫ x in R ⁻¹' B.val, hsNormSq (DA x)) =
        ∫ x in B.val, hsNormSq (Df x) := hPull.2.2.1
    rwa [hset] at hE

end StratificationTheory
