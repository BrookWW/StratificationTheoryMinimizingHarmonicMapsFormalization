module

public import StratificationTheory.Foundation.FlatRadialEndpoint
public import StratificationTheory.Foundation.CoordinateRectangleTrace
public import StratificationTheory.Foundation.CubicalConeRadialFormula
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal

namespace StratificationTheory

/-- The actual whole-cube radial Sobolev graph produces its unique full-face
native L2 curve in every genuine cube frame. Its positive endpoint is the
original boundary face class on the entire open face. -/
theorem exists_cubical_radial_full_face_trace {n q : ℕ}
    (G : Domain (n + 1) → Ambient q) (D : Domain (n + 1) → Gradient (n + 1) q)
    (A : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1))
    (hMax : ∀ y, ‖WithLp.ofLp (A y)‖ = ‖WithLp.ofLp y‖) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let B : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let W : Domain (n + 1) → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    let f : Domain n → Ambient q := fun x => G (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    MemW12 Ω W D → ∀ hf : MemLp f 2 (volume.restrict B.val),
    ∃ H : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x : Domain n => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      H ⟨1, by norm_num, le_rfl⟩ = hf.toLp f ∧
      ∀ K : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x : Domain n => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
            K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
              (fun x => W (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) → K = H := by
  intro e B Ω W f hW hf
  have hCube (y : Domain (n + 1)) : y ∈ Ω.val ↔ ‖WithLp.ofLp y‖ < 1 := by
    rw [mem_unit_coordinate_face_iff, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.norm_eq_abs]
  have hPre : A ⁻¹' Ω.val = Ω.val := by
    ext y
    change A y ∈ Ω.val ↔ y ∈ Ω.val
    rw [hCube, hCube, hMax]
  have hPull := memW12_isometric_preimage (volume_unit_coordinate_face_ne_top (n + 1)) hW A
  let ΩA : OpenDomain (n + 1) := ⟨A ⁻¹' Ω.val, Ω.property.preimage A.continuous⟩
  have hΩA : ΩA = Ω := Subtype.ext hPre
  let DA : Domain (n + 1) → Gradient (n + 1) q := fun x i =>
    ∑ j : Fin (n + 1), (A (EuclideanSpace.single i 1)) j • D (A x) j
  have hWA : MemW12 Ω (W ∘ A) DA := by
    have h : MemW12 ΩA (W ∘ A) DA := hPull
    rwa [hΩA] at h
  let R : OpenDomain (n + 1) :=
    ⟨{y | (e y).1 ∈ B.val ∧ (e y).2 0 ∈ Ioo (-1 : ℝ) 1},
      (B.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hR : R = Ω := by
    apply Subtype.ext
    ext y
    constructor
    · intro hy
      apply (mem_unit_coordinate_face_iff y).mpr
      intro k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · change |(e y).2 0| < 1
        exact abs_lt.mpr hy.2
      · change |(e y).1 k| < 1
        exact (mem_unit_coordinate_face_iff _).mp hy.1 k
    · intro hy
      have h := (mem_unit_coordinate_face_iff y).mp hy
      refine ⟨(mem_unit_coordinate_face_iff _).mpr (fun k => h k.castSucc), ?_⟩
      exact abs_lt.mp (h (Fin.last n))
  have hWR : MemW12 R (W ∘ A) DA := by rwa [hR]
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict B.val) :=
    isFiniteMeasure_restrict.mpr (volume_unit_coordinate_face_ne_top n)
  obtain ⟨H, hH, hUnique⟩ := exists_unique_L2_trace_of_memW12_rectangle B
    (by norm_num : (-1 : ℝ) < 1) hWR
  refine ⟨H, hH, ?_, fun K hK => hUnique K hK⟩
  apply continuous_flat_trace_endpoint_of_radial_slices f
    (fun z => W (A (e.symm (z.1, EuclideanSpace.single (0 : Fin 1) z.2)))) hf H hH
  intro t ht x hxt
  let y := e.symm (x, EuclideanSpace.single (0 : Fin 1) t)
  have hy : ∀ k : Fin n, |(e y).1 k| < (e y).2 0 := by
    intro k
    simp only [y, e.apply_symm_apply, PiLp.single_apply, ite_true]
    have hk := norm_le_pi_norm (WithLp.ofLp x) k
    exact (show |x k| ≤ ‖WithLp.ofLp x‖ from hk).trans_lt hxt
  have ht' : 0 < (e y).2 0 := by simpa only [y, e.apply_symm_apply, PiLp.single_apply, ite_true] using ht.1
  change G (‖WithLp.ofLp (A y)‖⁻¹ • A y) = G (A (e.symm (t⁻¹ • x, EuclideanSpace.single (0 : Fin 1) 1)))
  rw [cubical_radial_retraction_isometry A hMax,
    (positive_cube_cone_radial_retraction y ht' hy).2]
  change G (A (e.symm (((e y).2 0)⁻¹ • (e y).1, EuclideanSpace.single (0 : Fin 1) 1))) = _
  simp only [y, e.apply_symm_apply, PiLp.single_apply, ite_true]

end StratificationTheory
