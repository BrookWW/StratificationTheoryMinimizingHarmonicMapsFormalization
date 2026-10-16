module

public import StratificationTheory.Foundation.CubicalSignedFrameBlock
public import StratificationTheory.Foundation.SignedCubeL2TraceTransport

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Original normal curves in the finitely many coordinate directions
produce original normal curves in every finite signed permutation frame.
Every endpoint remains the same literal ambient boundary representative. -/
theorem exists_cubical_coordinate_finite_frame_traces {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f g : Domain (n + 1) → E) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let B := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    ∀ K : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
    (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => f (cubicalSignedFaceIsometry n i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B),
        K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ (i : Fin (n + 1)) (positive : Bool),
      (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → E)
        =ᵐ[volume.restrict B] (fun x => g (cubicalSignedFaceIsometry n i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) →
    ∀ (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool),
      let A := cubicalSignedPermutation (n + 1) p s
      ∃ H : C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain n => f (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B),
            H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        (H ⟨1, by norm_num, le_rfl⟩ : Domain n → E) =ᵐ[volume.restrict B]
          (fun x => g (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  intro e B K hK hEnd p s A
  obtain ⟨r, t, _ht, hBlock⟩ := exists_cubical_signed_frame_block p s
  let j := p (Fin.last n)
  let positive := s (Fin.last n)
  let C := cubicalSignedPermutation n r t
  let F : Domain n × ℝ → E := fun z => f (cubicalSignedFaceIsometry n j true
    (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2)))
  let g₀ : Domain n → E := fun x => g (cubicalSignedFaceIsometry n j false
    (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
  let g₁ : Domain n → E := fun x => g (cubicalSignedFaceIsometry n j true
    (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
  obtain ⟨H, hH, hHEnd⟩ := exists_signed_cube_L2_trace_transport F g₀ g₁ r t positive
    (K j) (hK j) (hEnd j false) (hEnd j true)
  have hFrame (x : Domain n) (η : ℝ) : A (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)) =
      cubicalSignedFaceIsometry n j true
        (e.symm (C x, EuclideanSpace.single (0 : Fin 1) (if positive then η else -η))) :=
    (hBlock x η).trans (cubical_signed_face_native_height j positive (C x) η)
  refine ⟨H, ?_, ?_⟩
  · filter_upwards [hH] with η hη hηI
    simpa only [F, hFrame] using hη hηI
  · filter_upwards [hHEnd] with x hx
    rw [hFrame]
    cases hpos : positive
    · simp only [hpos, Bool.false_eq_true, ite_false] at hx ⊢
      exact hx.trans (congrArg g (cubical_signed_face_native_height j false (C x) 1))
    · simpa only [hpos, ite_true] using hx

end StratificationTheory
