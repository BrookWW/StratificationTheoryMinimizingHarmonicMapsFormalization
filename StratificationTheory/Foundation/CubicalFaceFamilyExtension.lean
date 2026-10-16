module

public import StratificationTheory.Foundation.CubicalCompatibleBoundaryExtension
public import StratificationTheory.Foundation.CubicalCompatibleFrameCurves
public import StratificationTheory.Foundation.CubicalRadialCoordinateTraces

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Original independent signed-face maps and their original coordinate
curves with common physical edge endpoint classes produce one actual cube
extension. The same extension has the original full signed-face traces,
exact native energy, and every common a.e. face property. -/
theorem exists_cubical_face_family_extension {n q : ℕ}
    (f : (Fin ((n + 2) + 1) × Bool) → Domain (n + 2) → Ambient q)
    (Df : (Fin ((n + 2) + 1) × Bool) → Domain (n + 2) → Gradient (n + 2) q)
    (E : Domain ((n + 2) + 1) → Ambient q) :
    let d := (n + 2) + 1
    let J := Fin d × Bool
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 2) (m := 1)
    let B : OpenDomain (n + 2) :=
      ⟨⋂ k : Fin (n + 2), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 2) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let S := ⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω : OpenDomain d :=
      ⟨⋂ k : Fin d, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin d =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Q := fun j : J => cubicalSignedFaceIsometry (n + 2) j.1 j.2
    (∀ j : J, MemW12 B (f j) (Df j)) →
    ∀ Bnd : ℝ, (∀ j : J, ∀ᵐ x ∂volume.restrict B.val, ‖f j x‖ ≤ Bnd) →
    ∀ K : J → Fin (n + 2) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ j i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain (n + 1) => f j (cubicalSignedFaceIsometry (n + 1) i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K j i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f j (cubicalSignedFaceIsometry (n + 1) i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ j (i : Fin (n + 2)) (positive : Bool),
      (K j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 1) → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (Q j (e.symm
          (cubicalSignedFaceIsometry (n + 1) i positive (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1))))) →
    ∃ (G : Domain d → Ambient q) (D : Domain d → Gradient d q),
      let W : Domain d → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
      (∀ j x, x ∈ B.val → G (Q j (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = f j x) ∧
      MemW12 Ω W D ∧
      (∫ y in Ω.val, hsNormSq (D y)) =
        ((n + 2 : ℕ) - (1 : ℝ))⁻¹ * ∑ j : J, ∫ x in B.val,
          hsNormSq (Df j x) + ‖∑ k : Fin (n + 2), x k • Df j x k‖ ^ 2 ∧
      (∫ y in Ω.val, hsNormSq (D y)) ≤
        (((n + 2 : ℕ) + (1 : ℝ)) / ((n + 2 : ℕ) - (1 : ℝ))) *
          ∑ j : J, ∫ x in B.val, hsNormSq (Df j x) ∧
      (∃ H : Fin d → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain (n + 2) => W (Q (i, true)
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
            H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (Q (i, true)
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i positive,
          (H i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 2) → Ambient q)
            =ᵐ[volume.restrict B.val] f (i, positive)) ∧
      ∀ P : Ambient q → Prop, (∀ j : J, ∀ᵐ x ∂volume.restrict B.val, P (f j x)) →
        ∀ᵐ y ∂volume.restrict Ω.val, P (W y) := by
  classical
  intro d J b e B S Ω Q hface Bnd hBound K hK hEnd
  obtain ⟨G, _hCarrier, hCap⟩ := exists_cubical_boundary_from_face_maps f
  let fG : J → Domain (n + 2) → Ambient q := fun j x =>
    G (Q j (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
  have hAE (j : J) : fG j =ᵐ[volume.restrict B.val] f j := by
    filter_upwards [ae_restrict_mem B.property.measurableSet] with x hx
    exact hCap j.1 j.2 x hx
  have hCap' : ∀ j x, x ∈ B.val → fG j x = f j x := fun j => hCap j.1 j.2
  have hFaceG (j : J) : MemW12 B (fG j) (Df j) :=
    (hface j).congr_ae (hAE j).symm (EventuallyEq.refl _ _)
  have hBoundG (j : J) : ∀ᵐ x ∂volume.restrict B.val, ‖fG j x‖ ≤ Bnd := by
    filter_upwards [hBound j, hAE j] with x hx heq
    rwa [heq]
  obtain ⟨H, hH, hMatch⟩ := exists_cubical_compatible_frame_curves_of_coordinate_traces
    f G E hCap' K hK hEnd
  obtain ⟨D, hW, hEnergy, hEnergyBound, hProp⟩ :=
    exists_cubical_compatible_boundary_extension G Df hFaceG Bnd hBoundG H hH hMatch
  obtain ⟨T, hT, hTEnd⟩ := exists_cubical_radial_coordinate_traces G D hW
    (fun i positive => (hFaceG (i, positive)).2.1)
  refine ⟨G, D, hCap', hW, hEnergy, hEnergyBound, ⟨T, hT, ?_⟩, ?_⟩
  · intro i positive
    exact (hTEnd i positive).trans (hAE (i, positive))
  · intro P hP
    apply hProp P
    intro j
    filter_upwards [hP j, hAE j] with x hx heq
    change P (fG j x)
    rwa [heq]

end StratificationTheory
