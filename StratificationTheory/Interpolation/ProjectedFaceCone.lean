module

public import StratificationTheory.Frozen.CubicalFaceConeExtensionV2
public import StratificationTheory.Foundation.CubicalConeAEValues
public import StratificationTheory.Foundation.FlatFaceConeCapTrace
public import StratificationTheory.Foundation.CylinderPostcomposition
public import StratificationTheory.Interpolation.ProjectedCollar

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ContDiff ENNReal BigOperators
namespace StratificationTheory.Interpolation

/-- One target projection sends the actual native cone into the target,
with its displayed weak columns and the quantitative native energy bound.
The tubular input is an original a.e. face-value bound. -/
theorem exists_projected_unit_face_cone_operator {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ (ρ : ℝ) (Q : Ambient q → Ambient q),
      0 < ρ ∧ ContDiff ℝ ∞ Q ∧ (∀ z ∈ N.carrierSet, Q z = z) ∧
      ∀ (n : ℕ) (_hn : 2 ≤ n)
        (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q)
        (_hw : MemW12
          ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
            isOpen_iInter_of_finite (fun i : Fin n =>
              isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w Dw),
    let B : OpenDomain n :=
      ⟨⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : Domain (n + 1) → Domain n := fun y => (e y).1
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let C : OpenDomain (n + 1) :=
      ⟨T ⁻¹' Ioo (0 : ℝ) 1 ∩ ⋂ i : Fin n, {y : Domain (n + 1) | |X y i| < T y},
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous))).inter
        (isOpen_iInter_of_finite (fun i : Fin n =>
          isOpen_lt (((EuclideanSpace.proj i).continuous.comp
            (continuous_fst.comp e.continuous)).abs)
            ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous))))⟩
    let W : Domain (n + 1) → Ambient q := fun y => w (ξ y)
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin (n + 1) => Ambient q)
        (fun i : Fin n => (T y)⁻¹ • Dw (ξ y) i)
        (fun _last : Fin 1 => -((T y)⁻¹ • (∑ i : Fin n, (ξ y) i • Dw (ξ y) i)))
    let DQ : Domain (n + 1) → Gradient (n + 1) q :=
      fun y i => fderiv ℝ Q (W y) (D y i)
    (∀ᵐ x ∂volume.restrict B.val, infDist (w x) N.carrierSet < ρ) →
      MemW12 C W D ∧ MemW12 C (Q ∘ W) DQ ∧
      (∀ᵐ y ∂volume.restrict C.val, Q (W y) ∈ N.carrierSet) ∧
      (∫ y in C.val, hsNormSq (DQ y)) ≤
        (4 * (((n : ℝ) + 1) / ((n : ℝ) - 1))) * ∫ x in B.val, hsNormSq (Dw x) ∧
      dirichletEnergy DQ C.val ≤ 4 * dirichletEnergy D C.val ∧
      ∀ (σ : ℝ) (hσ : σ ∈ Ioo (0 : ℝ) 1),
        let U : Set (Domain n) := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-σ) σ
        ∃ H : C(Icc σ 1, Lp (Ambient q) 2 (volume.restrict U)),
          (∀ r : Icc σ 1,
            ∃ hr : MemLp (fun x : Domain n => (Q ∘ W)
                (e.symm (x, EuclideanSpace.single (0 : Fin 1) r.val))) 2 (volume.restrict U),
              H r = hr.toLp (fun x : Domain n => (Q ∘ W)
                (e.symm (x, EuclideanSpace.single (0 : Fin 1) r.val)))) ∧
          (∃ hcap : MemLp (Q ∘ w) 2 (volume.restrict U),
            H ⟨1, hσ.2.le, le_rfl⟩ = hcap.toLp (Q ∘ w)) ∧
          (∀ r : Icc σ 1, ∀ᵐ x ∂volume.restrict U, H r x ∈ N.carrierSet) ∧
          ((∀ᵐ x ∂volume.restrict B.val, w x ∈ N.carrierSet) →
            ∃ hcap : MemLp w 2 (volume.restrict U),
              H ⟨1, hσ.2.le, le_rfl⟩ = hcap.toLp w) ∧
          ∀ K : C(Icc σ 1, Lp (Ambient q) 2 (volume.restrict U)),
            (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo σ 1,
              ∃ hslice : MemLp (fun x : Domain n => (Q ∘ W)
                  (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))) 2 (volume.restrict U),
                K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x : Domain n => (Q ∘ W)
                  (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)))) → K = H := by
  obtain ⟨ρ, Q, hρ, _hρbase, hQ, ⟨L, _hL, hQL⟩, hfix, hnear⟩ :=
    exists_smooth_target_projection N
  refine ⟨ρ, Q, hρ, hQ, hfix, ?_⟩
  intro n hn w Dw hw B e X T ξ C W D DQ htube
  obtain ⟨hW, _hξ, _hjac, _hWI, _hWexact, hDI, _hDexact, hDbound, _hray, _htrace⟩ :=
    cubical_face_cone_extension_joint hn hw
  have hW' : MemW12 C W D := hW
  have hC : C.val = {y : Domain (n + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin n, |(e y).1 i| < (e y).2 0} := by
    ext y
    simp only [C, X, T, mem_inter_iff, mem_preimage, mem_iInter, mem_setOf_eq]
  have hCtube : ∀ᵐ y ∂volume.restrict C.val, infDist (W y) N.carrierSet < ρ := by
    rw [hC]
    exact ae_native_unit_face_cone_pullback (n := n) (w := w)
      (P := fun z => infDist z N.carrierSet < ρ) htube
  letI : IsFiniteMeasure (volume.restrict C.val) := isFiniteMeasure_restrict.mpr (by
    rw [hC]
    exact volume_native_unit_face_cone_ne_top n)
  have hQW : MemW12 C (Q ∘ W) DQ := MemW12.postcompose_finite (Ω := C) hW' Q hQ L hQL
  have htarget : ∀ᵐ y ∂volume.restrict C.val, Q (W y) ∈ N.carrierSet := by
    filter_upwards [hCtube] with y hy
    exact (hnear (W y) hy).choose_spec.2.1
  have hDlocal : ∀ᵐ y ∂volume.restrict C.val, ‖fderiv ℝ Q (W y)‖ ≤ 2 := by
    filter_upwards [hCtube] with y hy
    exact (hnear (W y) hy).choose_spec.2.2
  have hpoint : ∀ᵐ y ∂volume.restrict C.val,
      hsNormSq (DQ y) ≤ 4 * hsNormSq (D y) := by
    filter_upwards [hDlocal] with y hy
    unfold hsNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hnorm : ‖fderiv ℝ Q (W y) (D y i)‖ ≤ 2 * ‖D y i‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
    change ‖fderiv ℝ Q (W y) (D y i)‖ ^ 2 ≤ 4 * ‖D y i‖ ^ 2
    nlinarith only [hnorm, norm_nonneg (fderiv ℝ Q (W y) (D y i)), norm_nonneg (D y i)]
  refine ⟨hW, hQW, htarget, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∫ y in C.val, 4 * hsNormSq (D y) :=
        integral_mono_ae hQW.integrable_hsNormSq (hDI.const_mul 4) hpoint
      _ = 4 * ∫ y in C.val, hsNormSq (D y) := integral_const_mul _ _
      _ ≤ 4 * ((((n : ℝ) + 1) / ((n : ℝ) - 1)) * ∫ x in B.val, hsNormSq (Dw x)) :=
        mul_le_mul_of_nonneg_left hDbound (by norm_num)
      _ = _ := by ring
  · exact dirichletEnergy_postcomposition_le_four Q W D C.val hDlocal

  · intro σ hσ U
    letI : IsFiniteMeasure (volume.restrict B.val) :=
      isFiniteMeasure_restrict.mpr (volume_unit_coordinate_face_ne_top n)
    have hQw : MemLp (Q ∘ w) 2 (volume.restrict B.val) :=
      memLp_postcomposition hw.2.1 hQ hQL
    have hQwN : ∀ᵐ x ∂volume.restrict B.val, Q (w x) ∈ N.carrierSet := by
      filter_upwards [htube] with x hx
      exact (hnear (w x) hx).choose_spec.2.1
    obtain ⟨_hgeometry, H, hraw, hcap, hvalues, huniq⟩ :=
      exists_fixed_subface_cone_cap_L2_trace hσ.1 hσ.2 (Q ∘ w) hQw
    refine ⟨H, hraw, hcap, hvalues (fun z => z ∈ N.carrierSet) hQwN, ?_, huniq⟩
    intro hwN
    have hUB : U ⊆ B.val := by
      intro x hx
      apply mem_iInter.mpr
      intro i
      have hxi : -σ < x i ∧ x i < σ := mem_iInter.mp hx i
      change -1 < x i ∧ x i < 1
      constructor <;> linarith only [hσ.2, hxi.1, hxi.2]
    have hwU := hw.2.1.mono_measure (Measure.restrict_mono_set volume hUB)
    obtain ⟨hQU, hcapEq⟩ := hcap
    refine ⟨hwU, hcapEq.trans (hQU.toLp_congr hwU ?_)⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUB hwN] with x hx
    exact hfix (w x) hx

end StratificationTheory.Interpolation
