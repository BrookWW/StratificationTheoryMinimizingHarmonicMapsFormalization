module

public import StratificationTheory.Foundation.CubicalRadialFullFaceTrace
public import StratificationTheory.Foundation.CubicalSignedFrameBlock
public import StratificationTheory.Foundation.ReflectedRawTraceEndpoint

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- The same whole-cube radial Sobolev map has its original continuous
coordinate traces with both original signed boundary face classes. -/
theorem exists_cubical_radial_coordinate_traces {n q : ℕ}
    (G : Domain (n + 1) → Ambient q) (D : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let B : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Q := fun (i : Fin (n + 1)) (positive : Bool) => cubicalSignedFaceIsometry n i positive
    let f := fun i positive (x : Domain n) => G (Q i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let W := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    MemW12 Ω W D → (∀ i positive, MemLp (f i positive) 2 (volume.restrict B.val)) →
    ∃ K : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
      (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x : Domain n => W (Q i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
          K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => W (Q i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ i positive,
        (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
          =ᵐ[volume.restrict B.val] f i positive := by
  classical
  intro e B Ω Q f W hW hf
  have hEach (i : Fin (n + 1)) (positive : Bool) :=
    exists_cubical_radial_full_face_trace G D (Q i positive)
      (cubicalSignedFaceIsometry_coordinate_norm i positive) hW (hf i positive)
  choose H hH hEnd _hUnique using hEach
  refine ⟨fun i => H i true, fun i => hH i true, ?_⟩
  intro i positive
  cases positive
  · change (H i true ⟨-1, le_rfl, by norm_num⟩ : Domain n → Ambient q) =ᵐ[volume.restrict B.val] f i false
    have hFrame (x : Domain n) (t : ℝ) : Q i false (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
        Q i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) (-t))) :=
      cubical_signed_face_native_height i false x t
    have hMinus : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x : Domain n => W (Q i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) (-t))))) 2 (volume.restrict B.val),
          H i false ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => W (Q i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) (-t))))) := by
      have hSource := hH i false
      change ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x : Domain n => W (Q i false (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
          H i false ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => W (Q i false (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) at hSource
      simpa only [hFrame] using hSource
    have hLeft := left_trace_eq_right_trace_of_reflected_raw_slices (volume.restrict B.val)
      (fun z : Domain n × ℝ => W (Q i true (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2))))
      (H i true) (H i false) (hH i true) hMinus
    rw [hLeft, hEnd i false]
    exact (hf i false).coeFn_toLp
  · change (H i true ⟨1, by norm_num, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict B.val] f i true
    rw [hEnd i true]
    exact (hf i true).coeFn_toLp

end StratificationTheory
