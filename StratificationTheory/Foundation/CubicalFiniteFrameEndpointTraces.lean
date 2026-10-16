module

public import StratificationTheory.Foundation.CubicalCoordinateFrameTraces
public import StratificationTheory.Foundation.ReflectedRawTraceEndpoint

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Reflecting the original last coordinate of a finite signed frame has
its exact formula at every original native height. -/
theorem cubical_signed_frame_normal_reflection {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (s : Fin (n + 1) → Bool)
    (x : Domain n) (η : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let s' := fun k => if k = Fin.last n then !(s k) else s k
    cubicalSignedPermutation (n + 1) p s' (e.symm (x, EuclideanSpace.single (0 : Fin 1) η)) =
      cubicalSignedPermutation (n + 1) p s (e.symm (x, EuclideanSpace.single (0 : Fin 1) (-η))) := by
  intro e s'
  have hBase (k : Fin n) (t : ℝ) :
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) k.castSucc = x k := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))).1 k = x k
    rw [e.apply_symm_apply]
  have hLast (t : ℝ) : (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) (Fin.last n) = t := by
    change (e (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))).2 0 = t
    rw [e.apply_symm_apply]
    rfl
  ext l
  obtain ⟨k, rfl⟩ := p.surjective l
  rw [cubicalSignedPermutation_apply, cubicalSignedPermutation_apply]
  by_cases hk : k = Fin.last n
  · subst k
    rw [hLast, hLast]
    cases hs : s (Fin.last n) <;> simp [s', hs]
  · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hk
    rw [← hj, hBase, hBase]
    simp only [s', if_neg (Fin.castSucc_ne_last j)]

/-- Complete original coordinate curves determine both endpoint classes
in every actual finite signed frame. The second endpoint follows from
normal reflection and uniqueness of the original raw-slice curve. -/
theorem exists_cubical_coordinate_finite_frame_endpoint_traces {n : ℕ} {E : Type*}
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
        ∀ positive : Bool,
          (H ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → E)
            =ᵐ[volume.restrict B] (fun x => g (A (e.symm
              (x, EuclideanSpace.single (0 : Fin 1) (if positive then 1 else -1))))) := by
  intro e B K hK hEnd p s A
  obtain ⟨H, hH, hRight⟩ := exists_cubical_coordinate_finite_frame_traces f g K hK hEnd p s
  let s' := fun k => if k = Fin.last n then !(s k) else s k
  let A' := cubicalSignedPermutation (n + 1) p s'
  obtain ⟨J, hJ, hJRight⟩ := exists_cubical_coordinate_finite_frame_traces f g K hK hEnd p s'
  have hJ' : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => f (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) (-t))))) 2 (volume.restrict B),
        J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
          (fun x => f (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) (-t))))) := by
    simpa only [A', s', cubical_signed_frame_normal_reflection] using hJ
  have hLeft : H ⟨-1, le_rfl, by norm_num⟩ = J ⟨1, by norm_num, le_rfl⟩ :=
    left_trace_eq_right_trace_of_reflected_raw_slices (volume.restrict B)
      (fun z : Domain n × ℝ => f (A (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2)))) H J hH hJ'
  refine ⟨H, hH, ?_⟩
  intro positive
  cases positive
  · change (H ⟨-1, le_rfl, by norm_num⟩ : Domain n → E) =ᵐ[volume.restrict B] _
    rw [hLeft]
    simpa only [A', s', cubical_signed_frame_normal_reflection, Bool.false_eq_true, ite_false] using hJRight
  · exact hRight

end StratificationTheory
