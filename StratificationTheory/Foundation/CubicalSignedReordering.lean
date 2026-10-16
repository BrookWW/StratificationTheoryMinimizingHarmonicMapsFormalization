module

public import StratificationTheory.Foundation.CubicalFiniteFrameEndpointTraces
public import StratificationTheory.Foundation.CubicalSignedPermutationComposition
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- An actual finite signed coordinate reordering of one original cube
weak pair preserves its exact energy and transports every original normal
curve with both original boundary endpoint classes. -/
theorem exists_cubical_signed_reordered_pair_and_traces {n q : ℕ}
    (V g : Domain (n + 1) → Ambient q) (DV : Domain (n + 1) → Gradient (n + 1) q)
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
      ∃ hs : MemLp (fun x : Domain n => V (cubicalSignedFaceIsometry n i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B),
        K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ (i : Fin (n + 1)) (positive : Bool),
      (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict B] (fun x => g (cubicalSignedFaceIsometry n i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) →
    MemW12 Ω (V ∘ A) D ∧
      (∫ y in Ω.val, hsNormSq (D y)) = ∫ y in Ω.val, hsNormSq (DV y) ∧
      (∃ H : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain n => (V ∘ A) (cubicalSignedFaceIsometry n i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B),
            H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => (V ∘ A) (cubicalSignedFaceIsometry n i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ (i : Fin (n + 1)) (positive : Bool),
          (H i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
            =ᵐ[volume.restrict B] (fun x => (g ∘ A) (cubicalSignedFaceIsometry n i positive
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict Ω.val, P (V y)) →
        ∀ᵐ y ∂volume.restrict Ω.val, P ((V ∘ A) y) := by
  classical
  intro e B Ω A D hV K hK hEnd
  have hCube (x : Domain (n + 1)) : x ∈ Ω.val ↔ ‖WithLp.ofLp x‖ < 1 := by
    rw [mem_unit_coordinate_face_iff, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.norm_eq_abs]
  have hPre : A ⁻¹' Ω.val = Ω.val := by
    ext x
    change A x ∈ Ω.val ↔ x ∈ Ω.val
    rw [hCube, hCube, cubicalSignedPermutation_coordinate_norm]
  have hPull := memW12_isometric_preimage_energy (volume_unit_coordinate_face_ne_top (n + 1)) hV A
  let Ω' : OpenDomain (n + 1) := ⟨A ⁻¹' Ω.val, Ω.property.preimage A.continuous⟩
  have hΩ : Ω' = Ω := Subtype.ext hPre
  have hW : MemW12 Ω' (V ∘ A) D := hPull.1
  rw [hΩ] at hW
  have hEnergy : (∫ y in Ω.val, hsNormSq (D y)) = ∫ y in Ω.val, hsNormSq (DV y) := by
    have h := hPull.2.2.1
    change (∫ y in A ⁻¹' Ω.val, hsNormSq (D y)) = _ at h
    rwa [hPre] at h
  have hCurve (j : Fin (n + 1)) :
      ∃ H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain n => (V ∘ A) (cubicalSignedFaceIsometry n j true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B),
            H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => (V ∘ A) (cubicalSignedFaceIsometry n j true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ positive : Bool,
          (H ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
            =ᵐ[volume.restrict B] (fun x => (g ∘ A) (cubicalSignedFaceIsometry n j positive
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
    let σ := Equiv.swap (Fin.last n) j
    let r := σ.trans p
    let t := fun k => s (σ k)
    have hComposition : (cubicalSignedFaceIsometry n j true).trans A =
        cubicalSignedPermutation (n + 1) r t := by
      rw [cubicalSignedFaceIsometry_as_signedPermutation, cubicalSignedPermutation_compose]
      apply congrArg (cubicalSignedPermutation (n + 1) r)
      funext k
      simp only [ite_self, ite_true, t, σ]
    have hFrame (x : Domain n) (η : ℝ) :
        cubicalSignedPermutation (n + 1) r t (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)) =
          A (cubicalSignedFaceIsometry n j true (e.symm (x, EuclideanSpace.single (0 : Fin 1) η))) := by
      rw [← hComposition]
      rfl
    obtain ⟨H, hH, hHend⟩ := exists_cubical_coordinate_finite_frame_endpoint_traces V g K hK hEnd r t
    refine ⟨H, ?_, ?_⟩
    · change ∀ᵐ η : ℝ ∂volume, ∀ ht : η ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x : Domain n => V (cubicalSignedPermutation (n + 1) r t
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)))) 2 (volume.restrict B),
          H ⟨η, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (cubicalSignedPermutation (n + 1) r t
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)))) at hH
      simpa only [hFrame, Function.comp_apply] using hH
    · intro positive
      cases positive
      · change (H ⟨-1, le_rfl, by norm_num⟩ : Domain n → Ambient q) =ᵐ[volume.restrict B]
          (fun x => g (A (cubicalSignedFaceIsometry n j false
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))))
        have h := hHend false
        change (H ⟨-1, le_rfl, by norm_num⟩ : Domain n → Ambient q) =ᵐ[volume.restrict B]
          (fun x => g (cubicalSignedPermutation (n + 1) r t
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) (-1))))) at h
        filter_upwards [h] with x hx
        rw [hx, hFrame]
        exact congrArg (fun z => g (A z)) (cubical_signed_face_native_height j false x 1).symm
      · change (H ⟨1, by norm_num, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict B]
          (fun x => g (A (cubicalSignedFaceIsometry n j true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))))
        have h := hHend true
        change (H ⟨1, by norm_num, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict B]
          (fun x => g (cubicalSignedPermutation (n + 1) r t
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) at h
        filter_upwards [h] with x hx
        rw [hx, hFrame]
  choose H hH hHend using hCurve
  refine ⟨hW, hEnergy, ⟨H, hH, hHend⟩, ?_⟩
  have hProp := hPull.2.2.2.2
  change ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict Ω.val, P (V y)) →
    ∀ᵐ y ∂volume.restrict (A ⁻¹' Ω.val), P ((V ∘ A) y) at hProp
  rwa [hPre] at hProp

end StratificationTheory
