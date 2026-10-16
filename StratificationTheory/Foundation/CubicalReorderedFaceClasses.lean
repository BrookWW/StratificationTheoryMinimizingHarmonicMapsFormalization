module

public import StratificationTheory.Foundation.CubicalFiniteFrameFaceClasses
public import StratificationTheory.Foundation.CubicalSignedReordering

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- A finite signed reordering retains the exact weak graph, energy, and
all original separate lower-face endpoint classes in their actual native
signed coordinate charts. -/
theorem exists_cubical_reordered_pair_of_face_classes {n q : ℕ}
    (V : Domain (n + 1) → Ambient q) (DV : Domain (n + 1) → Gradient (n + 1) q)
    (g : (Fin (n + 1) × Bool) → Domain n → Ambient q)
    (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let B := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let A := cubicalSignedPermutation (n + 1) p s
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y i =>
      ∑ j : Fin (n + 1), (A (EuclideanSpace.single i 1)) j • DV (A y) j
    MemW12 Ω V DV →
    ∀ K : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B)),
    (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => V (cubicalSignedFaceIsometry n i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B),
        K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ i positive,
      (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict B] g (i, positive)) →
    MemW12 Ω (V ∘ A) D ∧
      (∫ y in Ω.val, hsNormSq (D y)) = ∫ y in Ω.val, hsNormSq (DV y) ∧
      (∃ (r : Fin (n + 1) → Equiv.Perm (Fin n))
        (t : Fin (n + 1) → Fin n → Bool)
        (H : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B))),
        ∀ i,
          let R := cubicalSignedPermutation n (r i) (t i)
          (∀ (x : Domain n) (η : ℝ),
            A (cubicalSignedFaceIsometry n i true (e.symm
              (x, EuclideanSpace.single (0 : Fin 1) η))) =
              cubicalSignedFaceIsometry n (p i) (s i)
                (e.symm (R x, EuclideanSpace.single (0 : Fin 1) η))) ∧
          (∀ᵐ η : ℝ ∂volume, ∀ hη : η ∈ Ioo (-1 : ℝ) 1,
            ∃ hs : MemLp (fun x => (V ∘ A) (cubicalSignedFaceIsometry n i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)))) 2 (volume.restrict B),
              H i ⟨η, hη.1.le, hη.2.le⟩ = hs.toLp
                (fun x => (V ∘ A) (cubicalSignedFaceIsometry n i true
                  (e.symm (x, EuclideanSpace.single (0 : Fin 1) η))))) ∧
          ∀ positive : Bool,
            (H i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
              =ᵐ[volume.restrict B] (fun x => g (p i, if positive then s i else !(s i)) (R x))) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict Ω.val, P (V y)) →
        ∀ᵐ y ∂volume.restrict Ω.val, P ((V ∘ A) y) := by
  classical
  intro e B Ω A D hV K hK hEnd
  obtain ⟨G, _hCarrier, hCap⟩ := exists_cubical_boundary_from_face_maps g
  have hEndG (i : Fin (n + 1)) (positive : Bool) :
      (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict B] (fun x => G (cubicalSignedFaceIsometry n i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
    filter_upwards [hEnd i positive, ae_restrict_mem (MeasurableSet.iInter fun k : Fin n =>
      measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable)] with x hx hxB
    exact hx.trans (hCap i positive x hxB).symm
  obtain ⟨hW, hEnergy, _hOldCurves, hProperties⟩ :=
    exists_cubical_signed_reordered_pair_and_traces V G DV p s hV K hK hEndG
  refine ⟨hW, hEnergy, ?_, hProperties⟩
  have hCurve (i : Fin (n + 1)) : ∃ (r : Equiv.Perm (Fin n)) (t : Fin n → Bool)
      (H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B))),
      let R := cubicalSignedPermutation n r t
      (∀ (x : Domain n) (η : ℝ), A (cubicalSignedFaceIsometry n i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) η))) =
          cubicalSignedFaceIsometry n (p i) (s i)
            (e.symm (R x, EuclideanSpace.single (0 : Fin 1) η))) ∧
      (∀ᵐ η : ℝ ∂volume, ∀ hη : η ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => (V ∘ A) (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)))) 2 (volume.restrict B),
          H ⟨η, hη.1.le, hη.2.le⟩ = hs.toLp
            (fun x => (V ∘ A) (cubicalSignedFaceIsometry n i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) η))))) ∧
      ∀ positive : Bool,
        (H ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
          =ᵐ[volume.restrict B] (fun x => g (p i, if positive then s i else !(s i)) (R x)) := by
    let σ := Equiv.swap (Fin.last n) i
    let π := σ.trans p
    let τ := fun j => s (σ j)
    have hComposition : (cubicalSignedFaceIsometry n i true).trans A =
        cubicalSignedPermutation (n + 1) π τ := by
      rw [cubicalSignedFaceIsometry_as_signedPermutation, cubicalSignedPermutation_compose]
      apply congrArg (cubicalSignedPermutation (n + 1) π)
      funext j
      simp only [ite_self, ite_true, τ, σ]
    have hFrame (x : Domain n) (η : ℝ) :
        cubicalSignedPermutation (n + 1) π τ (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)) =
          A (cubicalSignedFaceIsometry n i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) η))) := by
      rw [← hComposition]
      rfl
    dsimp only [e] at hFrame
    have hNormal : π (Fin.last n) = p i := by simp [π, σ]
    have hSide : τ (Fin.last n) = s i := by simp [τ, σ]
    obtain ⟨r, t, H, hBlock, hH, hHEnd⟩ :=
      exists_cubical_finite_frame_trace_of_face_classes V g K hK hEnd π τ
    refine ⟨r, t, H, ?_, ?_, ?_⟩
    · simpa only [e, hFrame, hNormal, hSide] using hBlock
    · simpa only [e, B, hFrame, Function.comp_apply] using hH
    · simpa only [hNormal, hSide] using hHEnd
  choose r t H hFrame hH hEnd using hCurve
  exact ⟨r, t, H, fun i => ⟨hFrame i, hH i, hEnd i⟩⟩

end StratificationTheory
