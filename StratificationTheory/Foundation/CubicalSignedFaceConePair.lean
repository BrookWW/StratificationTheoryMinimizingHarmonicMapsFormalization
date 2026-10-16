module

public import StratificationTheory.Foundation.CubicalSignedFaceConeExtension
public import StratificationTheory.Foundation.CubicalSignedConeCover

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators

namespace StratificationTheory

/-- The original signed-face data produce an actual weak pair on the literal
physical cone, for the same maximum-coordinate radial map. -/
theorem exists_cubical_signed_face_cone_pair {n q : ℕ} (hn : 2 ≤ n)
    (i : Fin (n + 1)) (positive : Bool) (G : Domain (n + 1) → Ambient q)
    (Df : Domain n → Gradient n q) :
    let Q := cubicalSignedFaceIsometry n i positive
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let f : Domain n → Ambient q := fun x => G (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let B : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let C : OpenDomain (n + 1) :=
      ⟨{y | (if positive then y i else -y i) ∈ Ioo (0 : ℝ) 1 ∧
        ∀ j : Fin (n + 1), j ≠ i → |y j| < (if positive then y i else -y i)},
        isOpen_cubical_signed_cone i positive⟩
    let W : Domain (n + 1) → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    MemW12 B f Df → ∃ D : Domain (n + 1) → Gradient (n + 1) q,
      MemW12 C W D ∧
      (∫ y in C.val, hsNormSq (D y)) =
        ((n : ℝ) - 1)⁻¹ * ∫ x in B.val,
          hsNormSq (Df x) + ‖∑ k : Fin n, x k • Df x k‖ ^ 2 ∧
      (∫ y in C.val, hsNormSq (D y)) ≤
        (((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Df x) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (f x)) →
        ∀ᵐ y ∂volume.restrict C.val, P (W y) := by
  intro Q e f B C W hf
  let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
  let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
  let D₀ : Domain (n + 1) → Gradient (n + 1) q := fun y =>
    Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
      (fun k : Fin n => (T y)⁻¹ • Df (ξ y) k)
      (fun _last : Fin 1 => -((T y)⁻¹ • (∑ k : Fin n, (ξ y) k • Df (ξ y) k)))
  let A : Domain (n + 1) → Gradient (n + 1) q := fun y j =>
    ∑ k : Fin (n + 1), (Q.symm (EuclideanSpace.single j 1)) k • D₀ (Q.symm y) k
  obtain ⟨hW, hMem, hE, hBound, hP⟩ := cubical_signed_face_cone_extension hn i positive G Df hf
  have hset : _ = C.val := Set.ext hMem
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · have hsub := fun y hy => (hMem y).mpr hy
    refine ⟨hW.1.mono hsub, hW.2.1.mono_measure (Measure.restrict_mono_set volume hsub), ?_⟩
    exact fun j => (hW.2.2 j).mono_measure (Measure.restrict_mono_set volume hsub)
  · rw [← hset]
    exact hE
  · rw [← hset]
    exact hBound
  · intro P hPf
    rw [← hset]
    exact hP P hPf

end StratificationTheory
