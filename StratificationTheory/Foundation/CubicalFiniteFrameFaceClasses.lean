module

public import StratificationTheory.Foundation.CubicalFiniteFrameEndpointTraces
public import StratificationTheory.Foundation.CubicalBoundaryFromFaces
public import StratificationTheory.Foundation.CubicalSignedFrameBlock

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

private theorem signed_cap_endpoint_reflection {n : ℕ} (i : Fin (n + 1))
    (side positive : Bool) (x : Domain n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    cubicalSignedFaceIsometry n i side (e.symm
      (x, EuclideanSpace.single (0 : Fin 1) (if positive then 1 else -1))) =
      cubicalSignedFaceIsometry n i (if positive then side else !side)
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)) := by
  intro e
  have h₀ := cubical_signed_face_native_height i side x (if positive then 1 else -1)
  have h₁ := cubical_signed_face_native_height i (if positive then side else !side) x 1
  have hScalar : (if side then (if positive then (1 : ℝ) else -1)
      else -(if positive then (1 : ℝ) else -1)) =
      (if (if positive then side else !side) then (1 : ℝ) else -1) := by
    cases positive <;> cases side <;> norm_num
  exact h₀.trans ((congrArg (fun r => cubicalSignedFaceIsometry n i true
    (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))) hScalar).trans h₁.symm)

/-- Original coordinate curves whose endpoints are the original separate
face classes produce all finite signed-frame curves. Both new endpoints
retain the exact original lower-face class and the same real tangential
signed permutation; no ambient boundary representative is an input. -/
theorem exists_cubical_finite_frame_trace_of_face_classes {n q : ℕ}
    (f : Domain (n + 1) → Ambient q)
    (g : (Fin (n + 1) × Bool) → Domain n → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let B := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    ∀ K : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B)),
    (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => f (cubicalSignedFaceIsometry n i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B),
        K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ i positive,
      (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict B] g (i, positive)) →
    ∀ (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool),
      let A := cubicalSignedPermutation (n + 1) p s
      let j := p (Fin.last n)
      let side := s (Fin.last n)
      ∃ (r : Equiv.Perm (Fin n)) (t : Fin n → Bool)
        (H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B))),
        let R := cubicalSignedPermutation n r t
        (∀ (x : Domain n) (η : ℝ), A (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)) =
          cubicalSignedFaceIsometry n j side (e.symm (R x, EuclideanSpace.single (0 : Fin 1) η))) ∧
        (∀ᵐ η : ℝ ∂volume, ∀ hη : η ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => f (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)))) 2 (volume.restrict B),
            H ⟨η, hη.1.le, hη.2.le⟩ = hs.toLp
              (fun x => f (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) η))))) ∧
        ∀ positive : Bool,
          (H ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
            =ᵐ[volume.restrict B] (fun x => g (j, if positive then side else !side) (R x)) := by
  intro e B K hK hEnd p s A j side
  obtain ⟨G, _hCarrier, hCap⟩ := exists_cubical_boundary_from_face_maps g
  have hEndG (i : Fin (n + 1)) (positive : Bool) :
      (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict B] (fun x => G (cubicalSignedFaceIsometry n i positive
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
    filter_upwards [hEnd i positive, ae_restrict_mem (MeasurableSet.iInter fun k : Fin n =>
      measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable)] with x hx hxB
    exact hx.trans (hCap i positive x hxB).symm
  obtain ⟨r, t, _ht, hBlock⟩ := exists_cubical_signed_frame_block p s
  let R := cubicalSignedPermutation n r t
  have hRB (x : Domain n) (hx : x ∈ B) : R x ∈ B := by
    have hNorm : ‖WithLp.ofLp x‖ < 1 := by
      rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
      simpa only [Real.norm_eq_abs] using (mem_unit_coordinate_face_iff x).mp hx
    apply (mem_unit_coordinate_face_iff _).mpr
    intro k
    have h := norm_le_pi_norm (WithLp.ofLp (R x)) k
    change |R x k| ≤ ‖WithLp.ofLp (R x)‖ at h
    rw [cubicalSignedPermutation_coordinate_norm] at h
    exact h.trans_lt hNorm
  obtain ⟨H, hH, hHEnd⟩ := exists_cubical_coordinate_finite_frame_endpoint_traces f G K hK hEndG p s
  have hEndpointPoint (x : Domain n) (positive : Bool) :
      A (e.symm (x, EuclideanSpace.single (0 : Fin 1) (if positive then 1 else -1))) =
      cubicalSignedFaceIsometry n j (if positive then side else !side)
        (e.symm (R x, EuclideanSpace.single (0 : Fin 1) 1)) :=
    (hBlock x _).trans (signed_cap_endpoint_reflection j side positive (R x))
  refine ⟨r, t, H, hBlock, hH, ?_⟩
  intro positive
  filter_upwards [hHEnd positive, ae_restrict_mem (MeasurableSet.iInter fun k : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable)] with x hx hxB
  exact hx.trans ((congrArg G (hEndpointPoint x positive)).trans
    (hCap j (if positive then side else !side) (R x) (hRB x hxB)))

end StratificationTheory
