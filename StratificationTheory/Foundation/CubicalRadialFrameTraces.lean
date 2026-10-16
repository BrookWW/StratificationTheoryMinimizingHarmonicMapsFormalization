module

public import StratificationTheory.Foundation.CubicalRadialFullFaceTrace
public import StratificationTheory.Foundation.CubicalFaceFrameCovariance
public import StratificationTheory.Foundation.CubicalSignedPermutations

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Canonical original full-face graphs and the actual radial cube graph
produce the complete finite family of original normalized flat L2 curves
and original full-face endpoint classes. -/
theorem exists_cubical_radial_finite_frame_traces {n q : ℕ}
    (G : Domain (n + 1) → Ambient q)
    (Df : (Fin (n + 1) × Bool) → Domain n → Gradient n q)
    (D : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let B : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let f : (Fin (n + 1) × Bool) → Domain n → Ambient q := fun j x =>
      G (cubicalSignedFaceIsometry n j.1 j.2 (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let W : Domain (n + 1) → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    (∀ j, MemW12 B (f j) (Df j)) → MemW12 Ω W D →
    ∀ (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool),
      let A := cubicalSignedPermutation (n + 1) p s
      let g : Domain n → Ambient q := fun x => G (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
      ∃ H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain n => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
            H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
              (fun x => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        (H ⟨1, by norm_num, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict B.val] g ∧
        ∀ K : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
          (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
            ∃ hs : MemLp (fun x : Domain n => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
              K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
                (fun x => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) → K = H := by
  intro e B Ω f W hface hW p s A g
  have hMax : ∀ y, ‖WithLp.ofLp (A y)‖ = ‖WithLp.ofLp y‖ :=
    cubicalSignedPermutation_coordinate_norm p s
  have hNormal (y : Domain (n + 1)) :
      (if s (Fin.last n) then (A y) (p (Fin.last n)) else -(A y) (p (Fin.last n))) = (e y).2 0 := by
    change (if s (Fin.last n) then (A y) (p (Fin.last n)) else -(A y) (p (Fin.last n))) = y (Fin.last n)
    rw [cubicalSignedPermutation_apply]
    split_ifs <;> simp only [neg_neg]
  have hg : MemLp g 2 (volume.restrict B.val) := by
    obtain ⟨DA, hA, _hEnergy⟩ := exists_cubical_face_pair_in_ambient_frame
      (p (Fin.last n)) (s (Fin.last n)) G (Df (p (Fin.last n), s (Fin.last n))) A
        (hface (p (Fin.last n), s (Fin.last n))) hMax hNormal
    exact hA.2.1
  obtain ⟨H, hH, hEnd, hUnique⟩ := exists_cubical_radial_full_face_trace G D A hMax hW hg
  refine ⟨H, hH, ?_, hUnique⟩
  rw [hEnd]
  exact hg.coeFn_toLp

end StratificationTheory
