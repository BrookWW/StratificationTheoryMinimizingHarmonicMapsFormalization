module

public import StratificationTheory.Foundation.ConicalSideTrace
public import StratificationTheory.Foundation.LocalMovingL2
import HarmonicMaps.Analysis.VariableMollificationL2

/-!
# Original cone traces along the actual unit normal

On compact subsets of a lateral parameter patch, genuine inward unit-normal
slices of the same degree-zero extension converge to the original flat trace.
The necessary tangential shift is controlled by local L2 translation continuity.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

private theorem inner_finAdd_symm {n m : ℕ} (p q : Domain n × Domain m) :
    inner ℝ ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm p)
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm q) =
      inner ℝ p.1 q.1 + inner ℝ p.2 q.2 := by
  let a := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv (m := n) (n := m)).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin n ⊕ Fin m => ℝ))
  change inner ℝ (a.symm (WithLp.toLp 2 p)) (a.symm (WithLp.toLp 2 q)) = _
  rw [a.symm.inner_map_map, WithLp.prod_inner_apply]

/-- The displayed inward vector is orthogonal to every tangent vector of
this actual lateral plane. -/
theorem native_cone_normal_orthogonal (n : ℕ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let ν := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    ∀ y, inner ℝ ν (e.symm (b.symm ((b y).1,
      EuclideanSpace.single (0 : Fin 1) ((b y).2 0)),
      EuclideanSpace.single (0 : Fin 1) ((b y).2 0))) = 0 := by
  intro b e ν y
  dsimp only [ν]
  rw [inner_finAdd_symm, inner_finAdd_symm]
  simp only [inner_zero_left, zero_add, EuclideanSpace.inner_single_left,
    PiLp.single_apply, ite_true, conj_trivial]
  ring

/-- The literal inward unit normal relates genuine normal translations to the
original parallel slices, including their small tangential parameter shift. -/
theorem native_cone_normal_translation (n : ℕ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let γ : ℝ → Domain (n + 1) → Domain ((n + 1) + 1) := fun δ y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 - δ)),
        EuclideanSpace.single (0 : Fin 1) ((b y).2 0))
    let ν := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    let τ : ℝ → Domain (n + 1) := fun η =>
      b.symm (0, EuclideanSpace.single (0 : Fin 1) (η / Real.sqrt 2))
    ‖ν‖ = 1 ∧ ∀ y η, γ 0 y + η • ν = γ (Real.sqrt 2 * η) (y + τ η) := by
  intro b e γ ν τ
  have hd : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have htwo : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 :=
    (div_eq_iff hp.ne').mpr (by nlinarith only [hd])
  refine ⟨?_, ?_⟩
  · have hnorm : ‖ν‖ ^ 2 = 1 := by
      dsimp only [ν]
      rw [norm_sq_finAddEquivProd_symm, norm_sq_finAddEquivProd_symm]
      simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
        PiLp.norm_single, Real.norm_eq_abs, sq_abs, neg_sq, inv_pow, hd]
      norm_num
    nlinarith only [hnorm, norm_nonneg ν]
  · intro y η
    apply e.injective
    simp only [γ, ν, τ, map_add, map_smul, e.apply_symm_apply, b.apply_symm_apply,
      Prod.fst_add, Prod.snd_add, PiLp.add_apply,
      PiLp.single_apply, ite_true, sub_zero, add_zero]
    apply Prod.ext
    · change b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0)) +
        η • b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)) = _
      rw [← b.symm.map_smul, ← b.symm.map_add]
      apply congrArg b.symm
      apply Prod.ext
      · simp
      · ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp only [Prod.snd_add, Prod.smul_snd, PiLp.add_apply, PiLp.smul_apply,
          PiLp.single_apply, ite_true, smul_eq_mul]
        have h := congrArg (fun r : ℝ => r * η) htwo
        simp only [div_eq_mul_inv] at h ⊢
        nlinarith only [h]
    · change EuclideanSpace.single (0 : Fin 1) ((b y).2 0) +
        η • EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹ = _
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul]
      ring

/-- Original flat trace data determine actual inward unit-normal slices of the
same cone map on every compact subset of the lateral parameter patch. -/
theorem native_face_cone_normal_side_L2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSbound : ∀ x ∈ S, ∀ i : Fin n, |x i| < 1)
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀) (hbb : b₀ < b₁) (hb₁ : b₁ < 1)
    (w : Domain (n + 1) → E)
    (H : C(Icc a 1, Lp E 2 (volume.restrict S)))
    (hf : AEStronglyMeasurable (fun p : Domain n × ℝ =>
      w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      ((volume.restrict S).prod (volume.restrict (Ioo a 1))))
    (hSlices : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x : Domain n =>
        w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) z))) 2 (volume.restrict S),
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x : Domain n =>
          w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
            (x, EuclideanSpace.single (0 : Fin 1) z))))
    {g : Domain n → E} (hg : MemLp g 2 (volume.restrict S))
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let W : Domain ((n + 1) + 1) → E := fun z => w (((e z).2 0)⁻¹ • (e z).1)
    let γ : ℝ → Domain (n + 1) → Domain ((n + 1) + 1) := fun δ y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) (T y - δ)),
        EuclideanSpace.single (0 : Fin 1) (T y))
    let ν := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    ‖ν‖ = 1 ∧ ∀ K : Set (Domain (n + 1)), IsCompact K → K ⊆ interior C →
      (∀ᶠ η in 𝓝[>] (0 : ℝ),
        MemLp (fun y => W (γ 0 y + η • ν) - g (ξ y)) 2 (volume.restrict K) ∧
        ∀ y ∈ K,
          (e (γ 0 y + η • ν)).2 0 ∈ Ioo (0 : ℝ) 1 ∧
          ∀ i : Fin (n + 1), |(e (γ 0 y + η • ν)).1 i| < (e (γ 0 y + η • ν)).2 0) ∧
      Tendsto (fun η : ℝ => eLpNorm (fun y => W (γ 0 y + η • ν) - g (ξ y))
        2 (volume.restrict K)) (𝓝[>] 0) (𝓝 0) := by
  intro b e T ξ C W γ ν
  let τ : ℝ → Domain (n + 1) := fun η =>
    b.symm (0, EuclideanSpace.single (0 : Fin 1) (η / Real.sqrt 2))
  have hgeom := native_cone_normal_translation n
  have hnormal : ∀ y η, γ 0 y + η • ν = γ (Real.sqrt 2 * η) (y + τ η) := hgeom.2
  refine ⟨hgeom.1, ?_⟩
  intro K hK hKC
  have hd : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hδ : Tendsto (fun η : ℝ => Real.sqrt 2 * η) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [mul_zero, id_eq] using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hd hη
  have hτ : Tendsto τ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hs : Isometry (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
      intro r s
      exact PiLp.edist_single_same 2 (fun _ : Fin 1 => ℝ) 0 r s
    have hc : Continuous τ := b.symm.continuous.comp
      (continuous_const.prodMk (hs.continuous.comp (continuous_id.div_const _)))
    have hz : τ 0 = 0 := by simp [τ]
    rw [← hz]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpar := native_face_cone_parallel_side_L2
    hS hSbound ha hb₀ hbb hb₁ w H hf hSlices hg hEnd
  let Ω : Set (Domain (n + 1)) := interior C
  let f : ℝ → Domain (n + 1) → E := fun η y => W (γ (Real.sqrt 2 * η) y)
  let G : Domain (n + 1) → E := fun y => g (ξ y)
  have hGC : MemLp G 2 (volume.restrict C) := by
    have hp := memLp_two_native_cone_of_product hS measurableSet_Icc
      (fun _ ht => hb₀.trans_le ht.1) (hb₀.trans hbb).le (fun _ ht => ht.2)
      (hg.comp_fst (volume.restrict (Icc b₀ b₁)))
    exact hp.1
  have hGΩ : MemLp G 2 (volume.restrict Ω) :=
    hGC.mono_measure (Measure.restrict_mono interior_subset le_rfl)
  have hLpΩ : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      MemLp (fun y => f η y - G y) 2 (volume.restrict Ω) := by
    filter_upwards [hδ.eventually hpar.1] with η hη
    exact hη.1.mono_measure (Measure.restrict_mono interior_subset le_rfl)
  have hlimΩ : Tendsto (fun η : ℝ => eLpNorm (fun y => f η y - G y)
      2 (volume.restrict Ω)) (𝓝[>] 0) (𝓝 0) := by
    have hup := hpar.2.2.comp hδ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => zero_le) (fun η => eLpNorm_mono_measure _
        (Measure.restrict_mono interior_subset le_rfl))
  have hmove := tendsto_local_L2_after_small_translation isOpen_interior hK hKC
    hGΩ hLpΩ hlimΩ hτ
  refine ⟨?_, ?_⟩
  · filter_upwards [hmove.1, hδ.eventually hpar.1] with η hη hp
    refine ⟨?_, ?_⟩
    · have hEq : (fun y => f η (y + τ η) - G y) =
          (fun y => W (γ 0 y + η • ν) - g (ξ y)) := by
        funext y
        dsimp only [f, G]
        rw [hnormal]
      rw [← hEq]
      exact hη.2
    · intro y hy
      rw [hnormal]
      have hyC : y + τ η ∈ C := interior_subset (hη.1 y hy)
      exact (hp.2 (y + τ η) hyC).1
  · have hEq : (fun η : ℝ => eLpNorm (fun y => f η (y + τ η) - G y)
        2 (volume.restrict K)) =
        (fun η : ℝ => eLpNorm (fun y => W (γ 0 y + η • ν) - g (ξ y))
        2 (volume.restrict K)) := by
      funext η
      congr 1
      funext y
      dsimp only [f, G]
      rw [hnormal]
    rw [← hEq]
    exact hmove.2

/-- Genuine inward unit-normal slices of the same extension converge on the
fixed actual lateral surface with its native Hausdorff measure. -/
theorem native_face_cone_normal_side_surface_L2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSbound : ∀ x ∈ S, ∀ i : Fin n, |x i| < 1)
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀) (hbb : b₀ < b₁) (hb₁ : b₁ < 1)
    (w : Domain (n + 1) → E)
    (H : C(Icc a 1, Lp E 2 (volume.restrict S)))
    (hf : AEStronglyMeasurable (fun p : Domain n × ℝ =>
      w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
        (p.1, EuclideanSpace.single (0 : Fin 1) p.2)))
      ((volume.restrict S).prod (volume.restrict (Ioo a 1))))
    (hSlices : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x : Domain n =>
        w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) z))) 2 (volume.restrict S),
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x : Domain n =>
          w ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
            (x, EuclideanSpace.single (0 : Fin 1) z))))
    {g : Domain n → E} (hg : MemLp g 2 (volume.restrict S))
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let W : Domain ((n + 1) + 1) → E := fun z => w (((e z).2 0)⁻¹ • (e z).1)
    let γ : ℝ → Domain (n + 1) → Domain ((n + 1) + 1) := fun δ y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) (T y - δ)),
        EuclideanSpace.single (0 : Fin 1) (T y))
    let ν := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    ∀ K : Set (Domain (n + 1)), IsCompact K → K ⊆ interior C →
    let σ := (Measure.euclideanHausdorffMeasure (n + 1) :
      Measure (Domain ((n + 1) + 1))).restrict (γ 0 '' K)
    let F : ℝ → Domain ((n + 1) + 1) → E := fun η z =>
      W (z + η • ν) - g (((e z).2 0)⁻¹ • (b (e z).1).1)
    (∀ᶠ η in 𝓝[>] (0 : ℝ), MemLp (F η) 2 σ ∧
      Integrable (fun z => ‖F η z‖ ^ 2) σ) ∧
      Tendsto (fun η : ℝ => ∫ z, ‖F η z‖ ^ 2 ∂σ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun η : ℝ => eLpNorm (F η) 2 σ) (𝓝[>] 0) (𝓝 0) := by
  intro b e T ξ C W γ ν K hK hKC σ F
  let R : ℝ → Domain (n + 1) → E := fun η y => W (γ 0 y + η • ν) - g (ξ y)
  have hn := native_face_cone_normal_side_L2 hS hSbound ha hb₀ hbb hb₁ w H hf hSlices hg hEnd
  have hKdata := hn.2 K hK hKC
  have hRLp : ∀ᶠ η in 𝓝[>] (0 : ℝ), MemLp (R η) 2 (volume.restrict K) :=
    hKdata.1.mono fun _ hi => hi.1
  have hRlim : Tendsto (fun η : ℝ => eLpNorm (R η) 2 (volume.restrict K))
      (𝓝[>] 0) (𝓝 0) := hKdata.2
  have htrans := native_lateral_height_L2_transport (E := E) (n := n) 0 hK.measurableSet
  have htransport : ∀ G : Domain ((n + 1) + 1) → E,
      MemLp (G ∘ γ 0) 2 (volume.restrict K) →
        MemLp G 2 σ ∧ Integrable (fun z => ‖G z‖ ^ 2) σ ∧
        (∫ z, ‖G z‖ ^ 2 ∂σ) = Real.sqrt 2 * ∫ y in K, ‖G (γ 0 y)‖ ^ 2 := htrans.2.2
  have hpull (η : ℝ) : F η ∘ γ 0 = R η := by
    funext y
    simp only [F, R, Function.comp_apply, γ, ξ, T, e.apply_symm_apply,
      b.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero]
  have hLp : ∀ᶠ η in 𝓝[>] (0 : ℝ), MemLp (F η) 2 σ ∧
      Integrable (fun z => ‖F η z‖ ^ 2) σ := by
    filter_upwards [hRLp] with η hη
    have hR : MemLp (F η ∘ γ 0) 2 (volume.restrict K) := by
      rw [hpull]
      exact hη
    exact ⟨(htransport (F η) hR).1, (htransport (F η) hR).2.1⟩
  have hRsq : Tendsto (fun η : ℝ => ∫ y in K, ‖R η y‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun η : ℝ => (eLpNorm (R η) 2 (volume.restrict K)).toReal ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [Function.comp_apply, ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hRlim).pow 2
    apply ht.congr'
    filter_upwards [hRLp] with η hη
    exact (HarmonicMaps.integral_norm_sq_eq_eLpNorm_two_toReal_sq hη).symm
  have hsq : Tendsto (fun η : ℝ => ∫ z, ‖F η z‖ ^ 2 ∂σ) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun η : ℝ => Real.sqrt 2 * ∫ y in K, ‖R η y‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hRsq
    apply hlim.congr'
    filter_upwards [hRLp] with η hη
    have hR : MemLp (F η ∘ γ 0) 2 (volume.restrict K) := by
      rw [hpull]
      exact hη
    have heq := (htransport (F η) hR).2.2
    have heqPull : (fun y => ‖F η (γ 0 y)‖ ^ 2) = (fun y => ‖R η y‖ ^ 2) := by
      funext y
      exact congrArg (fun z => ‖z‖ ^ 2) (congrFun (hpull η) y)
    rw [heqPull] at heq
    exact heq.symm
  refine ⟨hLp, hsq, ?_⟩
  have heq : (fun η => eLpNorm (F η) 2 σ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun η => ENNReal.ofReal (Real.sqrt (∫ z, ‖F η z‖ ^ 2 ∂σ))) := by
    filter_upwards [hLp] with η hη
    rw [Real.sqrt_eq_rpow]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] using
      hη.1.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  apply (tendsto_congr' heq).mpr
  have ht := ENNReal.tendsto_ofReal (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  simpa only [Function.comp_apply, Real.sqrt_zero, ENNReal.ofReal_zero] using ht

end StratificationTheory
