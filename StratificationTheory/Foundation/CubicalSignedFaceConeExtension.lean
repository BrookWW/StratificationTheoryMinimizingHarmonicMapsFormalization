module

public import StratificationTheory.Foundation.CubicalSignedFaceConeGeometry
public import StratificationTheory.Frozen.CubicalFaceConeExtensionV2
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback
public import StratificationTheory.Foundation.CubicalConeAEValues
import HarmonicMaps.Analysis.SobolevAECongruence

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace StratificationTheory

/-- Original full signed-face Sobolev data produce the same literal
maximum-coordinate radial extension on that entire open physical face cone.
Its actual rotated columns retain the exact native HS energy and original
a.e. value constraints. -/
theorem cubical_signed_face_cone_extension {n q : ℕ} (hn : 2 ≤ n)
    (i : Fin (n + 1)) (positive : Bool)
    (G : Domain (n + 1) → Ambient q) (Df : Domain n → Gradient n q) :
    let Q := cubicalSignedFaceIsometry n i positive
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let f : Domain n → Ambient q := fun x => G (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let B : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C₀ : OpenDomain (n + 1) :=
      ⟨T ⁻¹' Ioo (0 : ℝ) 1 ∩ ⋂ k : Fin n, {y : Domain (n + 1) | |(e y).1 k| < T y},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous))).inter
          (isOpen_iInter_of_finite (fun k : Fin n =>
            isOpen_lt (((EuclideanSpace.proj k).continuous.comp
              (continuous_fst.comp e.continuous)).abs)
              ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
                (continuous_snd.comp e.continuous))))⟩
    let C : OpenDomain (n + 1) := ⟨Q.symm ⁻¹' C₀.val, C₀.property.preimage Q.symm.continuous⟩
    let D₀ : Domain (n + 1) → Gradient (n + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
        (fun k : Fin n => (T y)⁻¹ • Df (ξ y) k)
        (fun _last : Fin 1 => -((T y)⁻¹ • (∑ k : Fin n, (ξ y) k • Df (ξ y) k)))
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y j =>
      ∑ k : Fin (n + 1), (Q.symm (EuclideanSpace.single j 1)) k • D₀ (Q.symm y) k
    let W : Domain (n + 1) → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    MemW12 B f Df →
      MemW12 C W D ∧
      (∀ y, y ∈ C.val ↔
        (if positive then y i else -y i) ∈ Ioo (0 : ℝ) 1 ∧
          ∀ j : Fin (n + 1), j ≠ i → |y j| < (if positive then y i else -y i)) ∧
      (∫ y in C.val, hsNormSq (D y)) =
        ((n : ℝ) - 1)⁻¹ * ∫ x in B.val,
          hsNormSq (Df x) + ‖∑ k : Fin n, x k • Df x k‖ ^ 2 ∧
      (∫ y in C.val, hsNormSq (D y)) ≤
        (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Df x) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (f x)) →
        ∀ᵐ y ∂volume.restrict C.val, P (W y) := by
  intro Q e f B T ξ C₀ C D₀ D W hf
  obtain ⟨hW₀, _hξ, _hJac, _hL2, _hval, _hDI, hE₀, hbound₀, _hrays, _htrace⟩ :=
    cubical_face_cone_extension_joint hn hf
  have hC₀ : C₀.val = {y : Domain (n + 1) | T y ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k : Fin n, |(e y).1 k| < T y} := by
    ext y
    simp only [C₀, mem_inter_iff, mem_preimage, mem_iInter, mem_setOf_eq]
  have hCfinite : (volume : Measure (Domain (n + 1))) C₀.val ≠ ⊤ := by
    rw [hC₀]
    exact volume_native_unit_face_cone_ne_top n
  have hPull := memW12_isometric_preimage_energy hCfinite hW₀ Q.symm
  have hmem (y : Domain (n + 1)) : y ∈ C.val ↔
      (if positive then y i else -y i) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ j : Fin (n + 1), j ≠ i → |y j| < (if positive then y i else -y i) := by
    change Q.symm y ∈ C₀.val ↔ _
    rw [hC₀]
    exact cubicalSignedFaceIsometry_strict_cone_iff i positive y
  have hmap : ((fun y => f (ξ y)) ∘ Q.symm) =ᵐ[volume.restrict C.val] W := by
    filter_upwards [ae_restrict_mem C.property.measurableSet] with y hy
    obtain ⟨hyPos, hyOther⟩ := (hmem y).mp hy
    obtain ⟨_hNorm, hRad⟩ := cubical_radial_retraction_signed_face i positive y hyPos.1 hyOther
    have hN : T (Q.symm y) = (if positive then y i else -y i) := by
      change Q.symm y (Fin.last n) = _
      simpa only [ite_true] using cubicalSignedFaceIsometry_symm_apply i positive y (Fin.last n)
    change G (Q (e.symm ((T (Q.symm y))⁻¹ • (e (Q.symm y)).1,
      EuclideanSpace.single (0 : Fin 1) 1))) = G (‖WithLp.ofLp y‖⁻¹ • y)
    rw [hN, hRad]
  have hW : MemW12 C W D := hPull.1.congr_ae hmap (EventuallyEq.refl _ _)
  refine ⟨hW, hmem, hPull.2.2.1.trans hE₀, hPull.2.2.1.trans_le hbound₀, ?_⟩
  intro P hP
  have hP₀ : ∀ᵐ y ∂volume.restrict C₀.val, P (f (ξ y)) := by
    rw [hC₀]
    exact ae_native_unit_face_cone_pullback hP
  have hPPull := hPull.2.2.2.2 P hP₀
  filter_upwards [hPPull, hmap] with y hPy hEq
  rwa [hEq] at hPy

end StratificationTheory
