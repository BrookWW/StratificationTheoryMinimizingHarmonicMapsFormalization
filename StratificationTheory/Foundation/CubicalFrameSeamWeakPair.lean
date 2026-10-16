module

public import StratificationTheory.Foundation.CubicalAdjacentConeGluing
public import StratificationTheory.Foundation.CubicalFaceFrameCovariance
public import StratificationTheory.Foundation.CubicalSignedPermutations
public import StratificationTheory.Foundation.CubicalConeRadialFormula
import HarmonicMaps.Analysis.SobolevAECongruence

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace StratificationTheory

/-- Compatible original flat face traces give an actual weak pair for the
same global radial map on a neighborhood of the physical signed seam.
All face graphs in the supplied finite frame are derived from canonical
signed-face data. -/
theorem exists_cubical_frame_seam_weak_pair {n q : ℕ} (hn : 2 ≤ n + 1)
    (G : Domain ((n + 1) + 1) → Ambient q)
    (Df : (Fin ((n + 1) + 1) × Bool) → Domain (n + 1) → Gradient (n + 1) q)
    (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let A := cubicalSignedPermutation ((n + 1) + 1) p s
    let A₀ := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
    let B : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let S : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let f : (Fin ((n + 1) + 1) × Bool) → Domain (n + 1) → Ambient q := fun j x =>
      G (cubicalSignedFaceIsometry (n + 1) j.1 j.2 (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let w₀ : Domain (n + 1) → Ambient q := fun x => G (A (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    let w₁ : Domain (n + 1) → Ambient q := fun x => G (A (A₀ (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))))
    (∀ j, MemW12 B (f j) (Df j)) →
    ∀ (H₀ H₁ : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S.val))),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => w₀ (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S.val),
        H₀ ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => w₀ (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => w₁ (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S.val),
        H₁ ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => w₁ (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) →
    H₀ ⟨1, by norm_num, le_rfl⟩ = H₁ ⟨1, by norm_num, le_rfl⟩ →
    ∀ (b₀ b₁ : ℝ), 0 < b₀ → b₀ < b₁ → b₁ < 1 →
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S.val}
    let Ψ : Domain (n + 1) → Domain (n + 1) := fun y =>
      b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2))
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun z =>
      e.symm (b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2)),
        EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2))
    let ν := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    let W : Domain ((n + 1) + 1) → Ambient q := fun y => G (‖WithLp.ofLp y‖⁻¹ • y)
    ∃ Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1),
      (∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = A (Γ z) + η • A ν) ∧
      ∀ U : OpenDomain (n + 1), IsCompact (closure U.val) → Ψ '' closure U.val ⊆ interior C →
      let R : ℝ → OpenDomain ((n + 1) + 1) := fun ε =>
        ⟨Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (-ε) ε},
          ((U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))).preimage Q.symm.continuous⟩
      ∃ ε : ℝ, 0 < ε ∧ ∃ D : Domain ((n + 1) + 1) → Gradient ((n + 1) + 1) q,
        MemW12 (R ε) W D := by
  intro b e A A₀ B S f w₀ w₁ hface H₀ H₁ hSlices₀ hSlices₁ hMatch b₀ b₁ hb₀ hbb hb₁ T ξ C Ψ Γ ν W
  let l := Fin.last (n + 1)
  let m := (Fin.last n).castSucc
  have hMax (y : Domain ((n + 1) + 1)) : ‖WithLp.ofLp (A y)‖ = ‖WithLp.ofLp y‖ :=
    cubicalSignedPermutation_coordinate_norm p s y
  have hMax₀ (y : Domain ((n + 1) + 1)) : ‖WithLp.ofLp (A₀ y)‖ = ‖WithLp.ofLp y‖ :=
    cubicalSignedFaceIsometry_coordinate_norm (Fin.last n).castSucc true y
  have hNormal₀ (y : Domain ((n + 1) + 1)) :
      (if s l then (A y) (p l) else -(A y) (p l)) = (e y).2 0 := by
    change (if s l then (A y) (p l) else -(A y) (p l)) = y l
    rw [cubicalSignedPermutation_apply]
    split_ifs <;> simp only [neg_neg]
  let A₁ := A₀.trans A
  have hNormal₁ (y : Domain ((n + 1) + 1)) :
      (if s m then (A₁ y) (p m) else -(A₁ y) (p m)) = (e y).2 0 := by
    change (if s m then (A (A₀ y)) (p m) else -(A (A₀ y)) (p m)) = y l
    rw [cubicalSignedPermutation_apply]
    have hSwap : A₀ y m = y l := by
      have h := cubicalSignedFaceIsometry_apply (Fin.last n).castSucc true y (Fin.last (n + 1))
      simpa only [Equiv.swap_apply_left, ite_true, ite_self] using h
    rw [hSwap]
    split_ifs <;> simp only [neg_neg]
  obtain ⟨Dw₀, hw₀, _hE₀⟩ := exists_cubical_face_pair_in_ambient_frame
    (p l) (s l) G (Df (p l, s l)) A (hface (p l, s l)) hMax hNormal₀
  obtain ⟨Dw₁, hw₁, _hE₁⟩ := exists_cubical_face_pair_in_ambient_frame
    (p m) (s m) G (Df (p m, s m)) A₁ (hface (p m, s m))
      (fun y => (hMax (A₀ y)).trans (hMax₀ y)) hNormal₁
  let g : Domain n → Ambient q := H₀ ⟨1, by norm_num, le_rfl⟩
  have hg : MemLp g 2 (volume.restrict S.val) := Lp.memLp (H₀ ⟨1, by norm_num, le_rfl⟩)
  have hEnd₀ : H₀ ⟨1, by norm_num, le_rfl⟩ = hg.toLp g := (Lp.toLp_coeFn _ hg).symm
  have hEnd₁ : H₁ ⟨1, by norm_num, le_rfl⟩ = hg.toLp g := hMatch.symm.trans hEnd₀
  have hSbound : ∀ x ∈ S.val, ∀ k : Fin n, |x k| < 1 :=
    fun x hx => (mem_unit_coordinate_face_iff x).mp hx
  obtain ⟨Q₀, hQ₀, hGlue⟩ := exists_adjacent_face_cones_weak_gluing hn S hSbound hb₀ hbb hb₁
    w₀ w₁ Dw₀ Dw₁ hw₀ hw₁ H₀ H₁ hSlices₀ hSlices₁ g hg hEnd₀ hEnd₁
  let Q := Q₀.trans A
  have hQ : ∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = A (Γ z) + η • A ν := by
    intro z η
    change A (Q₀ _) = _
    rw [hQ₀, A.map_add, A.map_smul]
  refine ⟨Q, hQ, ?_⟩
  intro U hU hUC R
  obtain ⟨ε, hε, D₀, hF, hPlus, hMinus⟩ := hGlue U hU hUC
  have hUfinite : (volume : Measure (Domain (n + 1))) U.val ≠ ⊤ :=
    ne_top_of_le_ne_top hU.measure_lt_top.ne (measure_mono subset_closure)
  have hRfinite : (volume : Measure (Domain ((n + 1) + 1)))
      (Q₀.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (-ε) ε}) ≠ ⊤ := by
    have hMeas : MeasurableSet {y : Domain ((n + 1) + 1) |
        (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (-ε) ε} :=
      ((U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))).measurableSet
    rw [Q₀.symm.measurePreserving.measure_preimage hMeas.nullMeasurableSet]
    rw [volume_cylinder_coordinates_rectangle (n + 1) U.property.measurableSet measurableSet_Ioo]
    exact ENNReal.mul_ne_top hUfinite (by simp)
  have hPull := memW12_isometric_preimage hRfinite hF A.symm
  have hA₀A₀ (y : Domain ((n + 1) + 1)) : A₀ (A₀ y) = y :=
    (cubical_adjacent_cone_swap_coordinates n).2.1 y
  have hMap₀ (y : Domain ((n + 1) + 1))
      (hy : (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧ ∀ k : Fin (n + 1), |(e y).1 k| < (e y).2 0) :
      w₀ (((e y).2 0)⁻¹ • (e y).1) = G (‖WithLp.ofLp (A y)‖⁻¹ • A y) := by
    change G (A (e.symm (_, EuclideanSpace.single (0 : Fin 1) 1))) = _
    rw [← (positive_cube_cone_radial_retraction y hy.1.1 hy.2).2,
      ← cubical_radial_retraction_isometry A hMax]
  have hMap₁ (y : Domain ((n + 1) + 1))
      (hy : (e (A₀ y)).2 0 ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin (n + 1), |(e (A₀ y)).1 k| < (e (A₀ y)).2 0) :
      w₁ (((e (A₀ y)).2 0)⁻¹ • (e (A₀ y)).1) = G (‖WithLp.ofLp (A y)‖⁻¹ • A y) := by
    change G (A (A₀ (e.symm (_, EuclideanSpace.single (0 : Fin 1) 1)))) = _
    rw [← (positive_cube_cone_radial_retraction (A₀ y) hy.1.1 hy.2).2,
      ← cubical_radial_retraction_isometry A₀ hMax₀, hA₀A₀,
      ← cubical_radial_retraction_isometry A hMax]
  have hNativeZero : ∀ᵐ y : Domain ((n + 1) + 1) ∂volume, (e (Q.symm y)).2 0 ≠ 0 :=
    Q.symm.measurePreserving.quasiMeasurePreserving.ae (ae_native_time_ne (n + 1) 0)
  have hMap : ∀ᵐ y ∂volume.restrict (R ε).val, (e (Q.symm y)).2 0 ≠ 0 :=
    ae_restrict_of_ae hNativeZero
  have hRaw : ((fun y => if (e (Q₀.symm y)).2 0 < 0 then
      w₁ (((e (A₀ y)).2 0)⁻¹ • (e (A₀ y)).1) else w₀ (((e y).2 0)⁻¹ • (e y).1)) ∘ A.symm)
        =ᵐ[volume.restrict (R ε).val] W := by
    filter_upwards [hMap, ae_restrict_mem (R ε).property.measurableSet] with y hne hy
    have hyU : (e (Q₀.symm (A.symm y))).1 ∈ U.val := hy.1
    have hyt : (e (Q₀.symm (A.symm y))).2 0 ∈ Ioo (-ε) ε := hy.2
    change (if (e (Q₀.symm (A.symm y))).2 0 < 0 then _ else _) = _
    by_cases ht : (e (Q₀.symm (A.symm y))).2 0 < 0
    · rw [if_pos ht]
      exact (hMap₁ _ (hMinus _ hyU ⟨hyt.1, ht⟩)).trans (by
        rw [A.apply_symm_apply])
    · have htpos : 0 < (e (Q₀.symm (A.symm y))).2 0 := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm hne)
      rw [if_neg ht]
      exact (hMap₀ _ (hPlus _ hyU ⟨htpos, hyt.2⟩)).trans (by
        rw [A.apply_symm_apply])
  have hW : MemW12 (R ε) W _ := hPull.congr_ae hRaw (EventuallyEq.refl _ _)
  exact ⟨ε, hε, _, hW⟩

end StratificationTheory
