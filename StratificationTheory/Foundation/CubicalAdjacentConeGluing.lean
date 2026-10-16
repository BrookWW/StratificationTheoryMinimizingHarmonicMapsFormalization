module

public import StratificationTheory.Foundation.CubicalAdjacentConeSwap
public import StratificationTheory.Foundation.CubicalFaceRectangleL2
public import StratificationTheory.Foundation.ConicalNormalChart
public import StratificationTheory.Foundation.IsometricTraceGluing

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace StratificationTheory

/-- Two original full-face weak pairs with the same genuine flat endpoint
trace produce a genuine Sobolev radial extension across their common conical
side. The one-sided cone traces and weak graphs are constructed internally. -/
theorem exists_adjacent_face_cones_weak_gluing {n q : ℕ} (hn : 2 ≤ n + 1)
    (S : OpenDomain n) (hSbound : ∀ x ∈ S.val, ∀ i : Fin n, |x i| < 1)
    {b₀ b₁ : ℝ} (hb₀ : 0 < b₀) (hbb : b₀ < b₁) (hb₁ : b₁ < 1)
    (w₀ w₁ : Domain (n + 1) → Ambient q)
    (Dw₀ Dw₁ : Domain (n + 1) → Gradient (n + 1) q)
    (hw₀ : MemW12
      ⟨⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w₀ Dw₀)
    (hw₁ : MemW12
      ⟨⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w₁ Dw₁)
    (H₀ H₁ : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S.val)))
    (hSlices₀ : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => w₀
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) z))) 2 (volume.restrict S.val),
        H₀ ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x : Domain n => w₀
          ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
            (x, EuclideanSpace.single (0 : Fin 1) z))))
    (hSlices₁ : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => w₁
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) z))) 2 (volume.restrict S.val),
        H₁ ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x : Domain n => w₁
          ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
            (x, EuclideanSpace.single (0 : Fin 1) z))))
    (g : Domain n → Ambient q) (hg : MemLp g 2 (volume.restrict S.val))
    (hEnd₀ : H₀ ⟨1, by norm_num, le_rfl⟩ = hg.toLp g)
    (hEnd₁ : H₁ ⟨1, by norm_num, le_rfl⟩ = hg.toLp g) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let A := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
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
    let W₀ : Domain ((n + 1) + 1) → Ambient q := fun y => w₀ (((e y).2 0)⁻¹ • (e y).1)
    let W₁ : Domain ((n + 1) + 1) → Ambient q := fun y => w₁ (((e (A y)).2 0)⁻¹ • (e (A y)).1)
    let C₀ := {y : Domain ((n + 1) + 1) | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k : Fin (n + 1), |(e y).1 k| < (e y).2 0}
    ∃ Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1),
      (∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = Γ z + η • ν) ∧
      ∀ U : OpenDomain (n + 1), IsCompact (closure U.val) → Ψ '' closure U.val ⊆ interior C →
      let R : ℝ → OpenDomain ((n + 1) + 1) := fun ε =>
        ⟨Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (-ε) ε},
          ((U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))).preimage Q.symm.continuous⟩
      let F : Domain ((n + 1) + 1) → Ambient q := fun y =>
        if (e (Q.symm y)).2 0 < 0 then W₁ y else W₀ y
      ∃ ε : ℝ, 0 < ε ∧ ∃ D : Domain ((n + 1) + 1) → Gradient ((n + 1) + 1) q,
        MemW12 (R ε) F D ∧
        (∀ y, (e (Q.symm y)).1 ∈ U.val → (e (Q.symm y)).2 0 ∈ Ioo (0 : ℝ) ε → y ∈ C₀) ∧
        (∀ y, (e (Q.symm y)).1 ∈ U.val → (e (Q.symm y)).2 0 ∈ Ioo (-ε) (0 : ℝ) → A y ∈ C₀) := by
  intro b e A T ξ C Ψ Γ ν W₀ W₁ C₀
  have hf₀ := (memLp_unit_face_native_rectangle hw₀.2.1 S.property.measurableSet hSbound).aestronglyMeasurable
  have hf₁ := (memLp_unit_face_native_rectangle hw₁.2.1 S.property.measurableSet hSbound).aestronglyMeasurable
  obtain ⟨Q, hQ, hK₀⟩ := native_face_cone_normal_isometric_slices_L2
    S.property.measurableSet hSbound (by norm_num : (-1 : ℝ) < 1) hb₀ hbb hb₁
    w₀ H₀ hf₀ hSlices₀ hg hEnd₀
  obtain ⟨Q₁, hQ₁, hK₁⟩ := native_face_cone_normal_isometric_slices_L2
    S.property.measurableSet hSbound (by norm_num : (-1 : ℝ) < 1) hb₀ hbb hb₁
    w₁ H₁ hf₁ hSlices₁ hg hEnd₁
  have hQeq : Q₁ = Q := by
    apply LinearIsometryEquiv.ext
    intro y
    have hOne : EuclideanSpace.single (0 : Fin 1) ((e y).2 0) = (e y).2 := by
      ext l
      have hl : l = 0 := Subsingleton.elim _ _
      subst l
      simp only [PiLp.single_apply, ite_true]
    have hrep : e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) = y := by
      rw [hOne, e.symm_apply_apply]
    have h₀ := hQ (e y).1 ((e y).2 0)
    have h₁ := hQ₁ (e y).1 ((e y).2 0)
    rw [hrep] at h₀ h₁
    exact h₁.trans h₀.symm
  subst Q₁
  have hQcanonical : ∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = Γ z + η • ν := by
    intro z η
    simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
      PiLp.single_apply, ite_true, sub_zero] using hQ z η
  obtain ⟨_hSwap, _hAA, _hAΓ, _hAν, hSwapQ⟩ := cubical_adjacent_cone_swap_coordinates n
  have hSwapNormal : ∀ z η, A (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))) =
      Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) (-η))) := by
    exact hSwapQ Q hQcanonical
  refine ⟨Q, hQcanonical, ?_⟩
  intro U hU hUC R F
  have hL₀ := hK₀ (closure U.val) hU hUC
  have hL₁ := hK₁ (closure U.val) hU hUC
  let G : Domain (n + 1) → Ambient q := fun y => g (ξ (Ψ y))
  have hgU : MemLp G 2 (volume.restrict U.val) :=
    hL₀.1.mono_measure (Measure.restrict_mono_set volume subset_closure)
  have hgeom := hL₀.2.1.mono fun _ h => h.2
  obtain ⟨ε, hε, hεgeom⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgeom
  have hεpos : 0 < ε := hε
  let V : OpenDomain ((n + 1) + 1) :=
    ⟨{y | (e y).2 0 ∈ Ioo (0 : ℝ) 1} ∩
      ⋂ k : Fin (n + 1), {y | |(e y).1 k| < (e y).2 0},
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous))).inter
        (isOpen_iInter_of_finite (fun k => isOpen_lt
          (((EuclideanSpace.proj k).continuous.comp (continuous_fst.comp e.continuous)).abs)
          ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_snd.comp e.continuous))))⟩
  have hVfinite : (volume : Measure (Domain ((n + 1) + 1))) V.val ≠ ⊤ := by
    have hset : V.val = {y | (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin (n + 1), |(e y).1 k| < (e y).2 0} := by
      ext y
      simp only [V, mem_inter_iff, mem_iInter, mem_setOf_eq]
    rw [hset]
    exact volume_native_unit_face_cone_ne_top (n + 1)
  have hwV₀ := (cubical_face_cone_extension_joint hn hw₀).1
  have hwV₁ := (cubical_face_cone_extension_joint hn hw₁).1
  have hwA₁ := memW12_isometric_preimage hVfinite hwV₁ A
  let Rplus : OpenDomain ((n + 1) + 1) :=
    ⟨Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε},
      ((U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))).preimage Q.symm.continuous⟩
  let Rminus : OpenDomain ((n + 1) + 1) :=
    ⟨Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (-ε) (0 : ℝ)},
      ((U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))).preimage Q.symm.continuous⟩
  have hrep (y : Domain ((n + 1) + 1)) :
      Q (e.symm ((e (Q.symm y)).1, EuclideanSpace.single (0 : Fin 1) ((e (Q.symm y)).2 0))) = y := by
    have hOne : EuclideanSpace.single (0 : Fin 1) ((e (Q.symm y)).2 0) = (e (Q.symm y)).2 := by
      ext l
      have hl : l = 0 := Subsingleton.elim _ _
      subst l
      simp only [PiLp.single_apply, ite_true]
    rw [hOne, e.symm_apply_apply, Q.apply_symm_apply]
  have hsubPlus : Rplus.val ⊆ V.val := by
    intro y hy
    have h := hεgeom hy.2 (e (Q.symm y)).1 (subset_closure hy.1)
    rw [hrep] at h
    exact ⟨h.1, mem_iInter.mpr h.2⟩
  have hsubMinus : Rminus.val ⊆ A ⁻¹' V.val := by
    intro y hy
    have htime : -(e (Q.symm y)).2 0 ∈ Ioo (0 : ℝ) ε :=
      ⟨neg_pos.mpr hy.2.2, by linarith only [hy.2.1]⟩
    have h := hεgeom htime (e (Q.symm y)).1 (subset_closure hy.1)
    rw [← hSwapNormal, hrep] at h
    exact ⟨h.1, mem_iInter.mpr h.2⟩
  have hwR₀ : MemW12 Rplus W₀ _ :=
    ⟨hwV₀.1.mono hsubPlus, hwV₀.2.1.mono_measure (Measure.restrict_mono_set volume hsubPlus),
      fun k => (hwV₀.2.2 k).mono_measure (Measure.restrict_mono_set volume hsubPlus)⟩
  have hwR₁ : MemW12 Rminus W₁ _ :=
    ⟨hwA₁.1.mono hsubMinus, hwA₁.2.1.mono_measure (Measure.restrict_mono_set volume hsubMinus),
      fun k => (hwA₁.2.2 k).mono_measure (Measure.restrict_mono_set volume hsubMinus)⟩
  have hright : Tendsto (fun t : ℝ => eLpNorm
      (fun z => W₀ (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t))) - G z)
        2 (volume.restrict U.val)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL₀.2.2
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume subset_closure))
  let Vone : Domain ((n + 1) + 1) → Ambient q := fun y =>
    w₁ (((e y).2 0)⁻¹ • (e y).1)
  have hbaseLeft : Tendsto (fun t : ℝ => eLpNorm
      (fun z => Vone (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t))) - G z)
        2 (volume.restrict U.val)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL₁.2.2
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume subset_closure))
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hId : Tendsto (fun t : ℝ => t) (𝓝[<] 0) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [neg_zero] using hId.neg
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact neg_pos.mpr (show t < 0 from ht)
  have hleft : Tendsto (fun t : ℝ => eLpNorm
      (fun z => W₁ (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t))) - G z)
        2 (volume.restrict U.val)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [W₁, Vone, hSwapNormal, Function.comp_def] using hbaseLeft.comp hneg
  letI : IsFiniteMeasure ((volume : Measure (Domain (n + 1))).restrict U.val) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top hU.measure_lt_top.ne (measure_mono subset_closure))
  have hglue := memW12_isometric_piecewise_of_common_raw_L2_limit U
    (by linarith only [hεpos] : -ε < (0 : ℝ)) hεpos Q W₁ W₀ _ _ hwR₁ hwR₀ G hgU hleft hright
  refine ⟨ε, hεpos, _, hglue.1, ?_, ?_⟩
  · intro y hyU hyt
    have h := hsubPlus ⟨hyU, hyt⟩
    exact ⟨h.1, fun k => mem_iInter.mp h.2 k⟩
  · intro y hyU hyt
    have h := hsubMinus ⟨hyU, hyt⟩
    exact ⟨h.1, fun k => mem_iInter.mp h.2 k⟩

end StratificationTheory
