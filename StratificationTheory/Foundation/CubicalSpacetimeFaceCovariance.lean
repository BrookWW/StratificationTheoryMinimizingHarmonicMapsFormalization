module

public import StratificationTheory.Foundation.IndependentTimeIsometry
public import StratificationTheory.Foundation.CubicalFrameFaceRestriction
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback
public import StratificationTheory.Foundation.CubicalConeGeometry

/-!
# Original spatial-face covariance with independent time

An actual finite spatial signed frame restricts to the original tangential
signed frame. Its genuine isometric lift retains time and produces the full
original face-times-time weak pair, exact native energy and value constraints.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

theorem exists_cubical_spacetime_face_pair_in_signed_frame {n q : ℕ}
    (G : Domain (n + 1) × ℝ → Ambient q)
    (Df : (Fin (n + 1) × Bool) → Domain (n + 1) → Gradient (n + 1) q)
    (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool)
    (ε : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain (n + 1) :=
      ⟨{z | (e z).1 ∈ S ∧ (e z).2 0 ∈ Ioo (0 : ℝ) ε},
        ((isOpen_iInter_of_finite fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous).preimage
            (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let f := fun (j : Fin (n + 1) × Bool) (z : Domain (n + 1)) =>
      G (cubicalSignedFaceIsometry n j.1 j.2
        (e.symm ((e z).1,EuclideanSpace.single (0 : Fin 1) 1)),(e z).2 0)
    let A := cubicalSignedPermutation (n + 1) p s
    let w := fun z : Domain (n + 1) =>
      G (A (e.symm ((e z).1,EuclideanSpace.single (0 : Fin 1) 1)),(e z).2 0)
    (∀ j, MemW12 B (f j) (Df j)) →
    ∃ D : Domain (n + 1) → Gradient (n + 1) q,
      MemW12 B w D ∧
      (∫ z in B.val,hsNormSq (D z)) =
        ∫ z in B.val,hsNormSq (Df (p (Fin.last n),s (Fin.last n)) z) ∧
      ∀ P : Ambient q → Prop,
        (∀ᵐ z ∂volume.restrict B.val, P (f (p (Fin.last n),s (Fin.last n)) z)) →
        ∀ᵐ z ∂volume.restrict B.val, P (w z) := by
  intro e S B f A w hFace
  obtain ⟨r,t,_ht,hCap⟩ := exists_cubical_signed_frame_face_restriction p s
  let C := cubicalSignedPermutation n r t
  obtain ⟨Q,hQ,_hQinv,hTime⟩ := exists_independent_time_isometry C
  have hQraw (z : Domain (n + 1)) : Q z = e.symm (C (e z).1,(e z).2) := hQ z
  have hCube (x : Domain n) : x ∈ S ↔ ‖WithLp.ofLp x‖ < 1 := by
    rw [mem_unit_coordinate_face_iff,pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.norm_eq_abs]
  have hPre : Q ⁻¹' B.val = B.val := by
    ext z
    change (e (Q z)).1 ∈ S ∧ (e (Q z)).2 0 ∈ Ioo (0 : ℝ) ε ↔
      (e z).1 ∈ S ∧ (e z).2 0 ∈ Ioo (0 : ℝ) ε
    rw [hQraw,e.apply_symm_apply,hCube,hCube,cubicalSignedPermutation_coordinate_norm]
  have hBfinite : (volume : Measure (Domain (n + 1))) B.val ≠ ⊤ := by
    rw [volume_cylinder_coordinates_rectangle n
      (MeasurableSet.iInter fun i : Fin n => measurableSet_Ioo.preimage (EuclideanSpace.proj i).continuous.measurable)
      measurableSet_Ioo]
    exact ENNReal.mul_ne_top (volume_unit_coordinate_face_ne_top n) (by simp)
  let j := (p (Fin.last n),s (Fin.last n))
  have hPull := memW12_isometric_preimage_energy hBfinite (hFace j) Q
  have hMap : f j ∘ Q = w := by
    funext z
    change G (cubicalSignedFaceIsometry n j.1 j.2
      (e.symm ((e (Q z)).1,EuclideanSpace.single (0 : Fin 1) 1)),(e (Q z)).2 0) = _
    rw [hQraw,e.apply_symm_apply]
    rw [← hCap]
  let D : Domain (n + 1) → Gradient (n + 1) q := fun z i =>
    ∑ k : Fin (n + 1), (Q (EuclideanSpace.single i 1)) k • Df j (Q z) k
  have hB : (⟨Q ⁻¹' B.val,B.property.preimage Q.continuous⟩ : OpenDomain (n + 1)) = B :=
    Subtype.ext hPre
  have hW : MemW12 B w D := by
    have h := hPull.1
    change MemW12 _ (f j ∘ Q) D at h
    rw [hB,hMap] at h
    exact h
  refine ⟨D,hW,?_,?_⟩
  · have h := hPull.2.2.1
    change (∫ z in Q ⁻¹' B.val,hsNormSq (D z)) = _ at h
    rwa [hPre] at h
  · have h := hPull.2.2.2.2
    change ∀ P : Ambient q → Prop,
      (∀ᵐ z ∂volume.restrict B.val,P (f j z)) →
      ∀ᵐ z ∂volume.restrict (Q ⁻¹' B.val),P ((f j ∘ Q) z) at h
    rwa [hPre,hMap] at h

end StratificationTheory
