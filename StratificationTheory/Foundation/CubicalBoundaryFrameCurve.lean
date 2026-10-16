module

public import StratificationTheory.Foundation.CubicalCoordinateFrameTraces

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Coordinate curves of the original face maps, with literal common edge
endpoint data, produce the original boundary curve in every finite ambient
frame. The endpoint is the same actual physical edge parametrization. -/
theorem exists_cubical_boundary_frame_curve {n q : ℕ}
    (f : (Fin ((n + 1) + 1) × Bool) → Domain (n + 1) → Ambient q)
    (G E : Domain ((n + 1) + 1) → Ambient q) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let B := ⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let S := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let Q := fun j : Fin ((n + 1) + 1) × Bool => cubicalSignedFaceIsometry (n + 1) j.1 j.2
    (∀ j x, x ∈ B → G (Q j (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = f j x) →
    ∀ K : (Fin ((n + 1) + 1) × Bool) → Fin (n + 1) →
      C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ j i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => f j (cubicalSignedFaceIsometry n i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K j i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f j (cubicalSignedFaceIsometry n i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ j (i : Fin (n + 1)) (positive : Bool),
      (K j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (Q j (e.symm
          (cubicalSignedFaceIsometry n i positive (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1))))) →
    ∀ (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool),
      let A := cubicalSignedPermutation ((n + 1) + 1) p s
      ∃ H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain n => G (A (e.symm
            (b.symm (x, EuclideanSpace.single (0 : Fin 1) t), EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict S),
            H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => G (A (e.symm
              (b.symm (x, EuclideanSpace.single (0 : Fin 1) t), EuclideanSpace.single (0 : Fin 1) 1))))) ∧
        (H ⟨1, by norm_num, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict S]
          (fun x => E (A (e.symm (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1),
            EuclideanSpace.single (0 : Fin 1) 1)))) := by
  intro b e B S Q hG K hK hEnd p s A
  obtain ⟨r, t, _ht, hBlock⟩ := exists_cubical_signed_frame_block p s
  let j := (p (Fin.last (n + 1)), s (Fin.last (n + 1)))
  let C := cubicalSignedPermutation (n + 1) r t
  let g : Domain (n + 1) → Ambient q := fun x => E (Q j (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
  obtain ⟨H, hH, hEndpoint⟩ := exists_cubical_coordinate_finite_frame_traces (f j) g
    (K j) (hK j) (hEnd j) r t
  have hCB (z : Domain (n + 1)) (hz : z ∈ B) : C z ∈ B := by
    apply (mem_unit_coordinate_face_iff _).mpr
    have hzNorm : ‖WithLp.ofLp z‖ < 1 := by
      rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
      simpa only [Real.norm_eq_abs] using (mem_unit_coordinate_face_iff z).mp hz
    intro k
    have hk := norm_le_pi_norm (WithLp.ofLp (C z)) k
    change |C z k| ≤ ‖WithLp.ofLp (C z)‖ at hk
    rw [cubicalSignedPermutation_coordinate_norm] at hk
    exact hk.trans_lt hzNorm
  have hNative (x : Domain n) (hx : x ∈ S) (η : ℝ) (hη : η ∈ Ioo (-1 : ℝ) 1) :
      b.symm (x, EuclideanSpace.single (0 : Fin 1) η) ∈ B := by
    apply (mem_unit_coordinate_face_iff _).mpr
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · change |(b (b.symm (x, EuclideanSpace.single (0 : Fin 1) η))).2 0| < 1
      rw [b.apply_symm_apply]
      exact abs_lt.mpr hη
    · change |(b (b.symm (x, EuclideanSpace.single (0 : Fin 1) η))).1 k| < 1
      rw [b.apply_symm_apply]
      exact (mem_unit_coordinate_face_iff x).mp hx k
  have hGFrame (z : Domain (n + 1)) (hz : z ∈ B) :
      G (A (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1))) = f j (C z) := by
    rw [hBlock]
    exact hG j (C z) (hCB z hz)
  refine ⟨H, ?_, ?_⟩
  · filter_upwards [hH] with η hη hηI
    obtain ⟨hs, hClass⟩ := hη hηI
    have hRaw : (fun x : Domain n => f j (C (b.symm (x, EuclideanSpace.single (0 : Fin 1) η))))
        =ᵐ[volume.restrict S] (fun x => G (A (e.symm
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) η), EuclideanSpace.single (0 : Fin 1) 1)))) := by
      filter_upwards [ae_restrict_mem (MeasurableSet.iInter fun k : Fin n =>
        measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable)] with x hx
      exact (hGFrame _ (hNative x hx η hηI)).symm
    have hs' := hs.ae_eq hRaw
    exact ⟨hs', hClass.trans (MemLp.toLp_congr hs hs' hRaw)⟩
  · filter_upwards [hEndpoint] with x hx
    exact hx.trans (congrArg E (hBlock (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) 1).symm)

end StratificationTheory
