module

public import StratificationTheory.Foundation.ConicalNormalTrace
public import StratificationTheory.Foundation.ConicalNormalCoordinates
public import StratificationTheory.Foundation.CoordinateRectangleTrace
public import StratificationTheory.Foundation.ContinuousTraceEndpoint
public import StratificationTheory.Foundation.IsometricDomainSobolevPullback
public import StratificationTheory.Frozen.CubicalFaceConeExtensionV2
public import HarmonicMaps.SobolevRestriction

/-!
# Canonical normal-coordinate traces of the original cone

The normalized lateral isometry converts actual surface L2 limits to original
normal-coordinate slices. Full Sobolev data of the original face supply the
physical cone weak pair and the canonical trace on sufficiently small inward
normal rectangles.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

private theorem normal_chart_measure_preserving {n : ℕ} {K : Set (Domain (n + 1))}
    (hK : MeasurableSet K) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2)),
        EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2))
    MeasurableEmbedding Γ ∧ MeasurePreserving Γ (volume.restrict K)
      ((Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict (Γ '' K)) := by
  intro b e Γ
  have hΓ : Isometry Γ := by
    simpa only [sub_zero] using isometry_native_cone_lateral_chart n 0
  have hEmb : MeasurableEmbedding Γ := hΓ.continuous.measurableEmbedding hΓ.injective
  have hMP0 : MeasurePreserving Γ volume
      ((Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict
        {z | (e z).2 0 - (b (e z).1).2 0 = 0}) := by
    simpa only [sub_zero] using (measurePreserving_native_cone_lateral_chart n 0).2
  have hMP := hMP0.restrict_image_emb hEmb K
  have hsub : Γ '' K ⊆ {z : Domain ((n + 1) + 1) |
      (e z).2 0 - (b (e z).1).2 0 = 0} := by
    rintro z ⟨y, _hy, rfl⟩
    simp only [Γ, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true, sub_self, mem_setOf_eq]
  have hM : MeasurableSet (Γ '' K) := hEmb.measurableSet_image' hK
  have hμ : ((Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict
      {z | (e z).2 0 - (b (e z).1).2 0 = 0}).restrict (Γ '' K) =
      (Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict (Γ '' K) := by
    rw [Measure.restrict_restrict hM, inter_eq_left.mpr hsub]
  refine ⟨hEmb, ?_⟩
  have hMP' : MeasurePreserving Γ (volume.restrict K)
      (((Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict
        {z | (e z).2 0 - (b (e z).1).2 0 = 0}).restrict (Γ '' K)) := by
    simpa only [sub_zero] using hMP
  rwa [hμ] at hMP'

/-- One actual Euclidean normal isometry realizes the same raw cone slices.
Original flat trace data produce their native L2 limits and canonical limit
classes on every compact interior lateral patch. -/
theorem native_face_cone_normal_isometric_slices_L2 {n : ℕ} {E : Type*}
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
    let Ψ : Domain (n + 1) → Domain (n + 1) := fun y =>
      b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2))
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := γ 0 ∘ Ψ
    let G : Domain (n + 1) → E := fun y => g (ξ (Ψ y))
    ∃ Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1),
      (∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = Γ z + η • ν) ∧
      ∀ K : Set (Domain (n + 1)), IsCompact K → Ψ '' K ⊆ interior C →
        MemLp G 2 (volume.restrict K) ∧
        (∀ᶠ η in 𝓝[>] (0 : ℝ),
          MemLp (fun z => W (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))) - G z)
            2 (volume.restrict K) ∧
          ∀ z ∈ K,
            (e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)))).2 0 ∈ Ioo (0 : ℝ) 1 ∧
            ∀ i : Fin (n + 1),
              |(e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)))).1 i| <
                (e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)))).2 0) ∧
        Tendsto (fun η : ℝ => eLpNorm
          (fun z => W (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))) - G z)
          2 (volume.restrict K)) (𝓝[>] 0) (𝓝 0) := by
  intro b e T ξ C W γ ν Ψ Γ G
  obtain ⟨Q, hQ, _hunique⟩ := exists_unique_native_cone_normal_coordinates n
  have hslice (z : Domain (n + 1)) (η : ℝ) :
      Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = Γ z + η • ν := by
    have hforward : ∀ y, e (Q y) =
        (b.symm ((b (e y).1).1, EuclideanSpace.single (0 : Fin 1)
          (((b (e y).1).2 0 - (e y).2 0) / Real.sqrt 2)),
         EuclideanSpace.single (0 : Fin 1) (((b (e y).1).2 0 + (e y).2 0) / Real.sqrt 2)) := hQ.1
    have hF := hforward (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))
    simp only [e.apply_symm_apply, PiLp.single_apply, ite_true] at hF
    apply e.injective
    rw [hF]
    simp only [Γ, Function.comp_apply, γ, T, Ψ, ν, map_add, map_smul,
      e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero]
    apply Prod.ext
    · change b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1)
          (((b z).2 0 - η) / Real.sqrt 2)) =
        b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2)) +
          η • b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹))
      rw [← b.symm.map_smul, ← b.symm.map_add]
      apply congrArg b.symm
      apply Prod.ext
      · simp
      · ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp only [Prod.snd_add, Prod.smul_snd, PiLp.add_apply, PiLp.smul_apply,
          PiLp.single_apply, ite_true, smul_eq_mul]
        ring
    · change EuclideanSpace.single (0 : Fin 1) (((b z).2 0 + η) / Real.sqrt 2) =
        EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2) +
          η • EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul]
      ring
  refine ⟨Q, hslice, ?_⟩
  intro K hK hKC
  have hs : Isometry (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    intro r s
    exact PiLp.edist_single_same 2 (fun _ : Fin 1 => ℝ) 0 r s
  have ht : Continuous (fun z : Domain (n + 1) => (b z).2 0) :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_snd.comp b.continuous)
  have hΨ : Continuous Ψ := b.symm.continuous.comp
    ((continuous_fst.comp b.continuous).prodMk (hs.continuous.comp (ht.div_const _)))
  let L : Set (Domain (n + 1)) := Ψ '' K
  have hL : IsCompact L := hK.image hΨ
  have hΓ (z : Domain (n + 1)) : Γ z =
      e.symm (b.symm ((b z).1, EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2)),
        EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2)) := by
    simp only [Γ, Function.comp_apply, γ, T, Ψ, b.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero]
  have hImage : Γ '' K = γ 0 '' L := by
    exact (image_image (γ 0) Ψ K).symm
  let σ := (Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict (Γ '' K)
  have hMP : MeasurePreserving Γ (volume.restrict K) σ := by
    have hnorm := normal_chart_measure_preserving hK.measurableSet
    have hfunc : Γ = (fun z => e.symm (b.symm ((b z).1,
        EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2)),
        EuclideanSpace.single (0 : Fin 1) ((b z).2 0 / Real.sqrt 2))) := funext hΓ
    change MeasurePreserving Γ (volume.restrict K)
      ((Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict (Γ '' K))
    rw [hfunc]
    exact hnorm.2
  let F : ℝ → Domain ((n + 1) + 1) → E := fun η z =>
    W (z + η • ν) - g (((e z).2 0)⁻¹ • (b (e z).1).1)
  have hpull (η : ℝ) : F η ∘ Γ =
      (fun z => W (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η))) - G z) := by
    funext z
    rw [hslice]
    simp only [F, G, Γ, Function.comp_apply, γ, ξ, T, e.apply_symm_apply,
      b.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero]
  have hsurface := native_face_cone_normal_side_surface_L2
    hS hSbound ha hb₀ hbb hb₁ w H hf hSlices hg hEnd L hL hKC
  have hSurfLp : ∀ᶠ η in 𝓝[>] (0 : ℝ), MemLp (F η) 2 σ := by
    filter_upwards [hsurface.1] with η hη
    simpa only [σ, hImage] using hη.1
  have hSurfLim : Tendsto (fun η : ℝ => eLpNorm (F η) 2 σ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [σ, hImage] using hsurface.2.2
  have hGC : MemLp (fun y => g (ξ y)) 2 (volume.restrict C) := by
    have hp := memLp_two_native_cone_of_product hS measurableSet_Icc
      (fun _ ht => hb₀.trans_le ht.1) (hb₀.trans hbb).le (fun _ ht => ht.2)
      (hg.comp_fst (volume.restrict (Icc b₀ b₁)))
    exact hp.1
  have hGL : MemLp (fun y => g (ξ y)) 2 (volume.restrict L) :=
    hGC.mono_measure (Measure.restrict_mono_set volume (fun y hy => interior_subset (hKC hy)))
  let B : Domain ((n + 1) + 1) → E := fun z => g (((e z).2 0)⁻¹ • (b (e z).1).1)
  have hBpull : B ∘ γ 0 = (fun y => g (ξ y)) := by
    funext y
    simp only [B, Function.comp_apply, γ, ξ, T, e.apply_symm_apply,
      b.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero]
  have hB : MemLp B 2 σ := by
    have htr := native_lateral_height_L2_transport (E := E) (n := n) 0 hL.measurableSet
    have hB' : MemLp (B ∘ γ 0) 2 (volume.restrict L) := by rwa [hBpull]
    have hB'' := (htr.2.2 B hB').1
    simpa only [σ, hImage] using hB''
  have hG : MemLp G 2 (volume.restrict K) := by
    have hbg : B ∘ Γ = G := by
      funext z
      simp only [B, G, Γ, Function.comp_apply, γ, ξ, T, e.apply_symm_apply,
        b.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero]
    rw [← hbg]
    exact hB.comp_measurePreserving hMP
  have hgeometry := (native_face_cone_normal_side_L2
    hS hSbound ha hb₀ hbb hb₁ w H hf hSlices hg hEnd).2 L hL hKC
  refine ⟨hG, ?_, ?_⟩
  · filter_upwards [hSurfLp, hgeometry.1] with η hη hgeo
    refine ⟨?_, ?_⟩
    · rw [← hpull]
      exact hη.comp_measurePreserving hMP
    · intro z hz
      rw [hslice]
      exact hgeo.2 (Ψ z) ⟨z, hz, rfl⟩
  · have hEq : (fun η : ℝ => eLpNorm (F η ∘ Γ) 2 (volume.restrict K)) =ᶠ[𝓝[>] 0]
        (fun η : ℝ => eLpNorm (F η) 2 σ) := by
      filter_upwards [hSurfLp] with η hη
      exact eLpNorm_comp_measurePreserving (g := F η) (f := Γ)
        (μ := volume.restrict K) (ν := σ) (p := (2 : ℝ≥0∞)) hη.aestronglyMeasurable hMP
    have ht := hSurfLim.congr' hEq.symm
    simpa only [hpull] using ht

/-- Full original face Sobolev data produce the actual cone weak pair on
small inward normal rectangles and their unique normalized continuous trace.
The endpoint is derived from the original flat trace, not supplied separately. -/
theorem exists_canonical_native_cone_normal_trace {n q : ℕ} (hn : 2 ≤ n + 1)
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSbound : ∀ x ∈ S, ∀ i : Fin n, |x i| < 1)
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀) (hbb : b₀ < b₁) (hb₁ : b₁ < 1)
    (w : Domain (n + 1) → Ambient q) {Dw : Domain (n + 1) → Gradient (n + 1) q}
    (hw : MemW12
      ⟨⋂ i : Fin (n + 1), (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩ w Dw)
    (H : C(Icc a 1, Lp (Ambient q) 2 (volume.restrict S)))
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
    {g : Domain n → Ambient q} (hg : MemLp g 2 (volume.restrict S))
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let W : Domain ((n + 1) + 1) → Ambient q := fun z => w (((e z).2 0)⁻¹ • (e z).1)
    let D : Domain ((n + 1) + 1) → Gradient ((n + 1) + 1) q := fun y =>
      Fin.addCases (motive := fun _j : Fin ((n + 1) + 1) => Ambient q)
        (fun i : Fin (n + 1) => ((e y).2 0)⁻¹ • Dw (((e y).2 0)⁻¹ • (e y).1) i)
        (fun _last : Fin 1 => -(((e y).2 0)⁻¹ •
          (∑ i : Fin (n + 1), ((((e y).2 0)⁻¹ • (e y).1) i) •
            Dw (((e y).2 0)⁻¹ • (e y).1) i)))
    let γ : ℝ → Domain (n + 1) → Domain ((n + 1) + 1) := fun δ y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) (T y - δ)),
        EuclideanSpace.single (0 : Fin 1) (T y))
    let ν := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    let Ψ : Domain (n + 1) → Domain (n + 1) := fun y =>
      b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 / Real.sqrt 2))
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := γ 0 ∘ Ψ
    let G : Domain (n + 1) → Ambient q := fun y => g (ξ (Ψ y))
    ∃ Q : Domain ((n + 1) + 1) ≃ₗᵢ[ℝ] Domain ((n + 1) + 1),
      (∀ z η, Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) η)) = Γ z + η • ν) ∧
      ∀ U : OpenDomain (n + 1), IsCompact (closure U.val) → Ψ '' closure U.val ⊆ interior C →
      let σ := (volume : Measure (Domain (n + 1))).restrict U.val
      let R : ℝ → OpenDomain ((n + 1) + 1) := fun ε =>
        ⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε},
          (U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      ∃ (ε : ℝ) (hε : 0 < ε),
        MemW12 (R ε) (W ∘ Q) (fun y i =>
          ∑ j : Fin ((n + 1) + 1), (Q (EuclideanSpace.single i 1)) j • D (Q y) j) ∧
        ∃! J : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 σ),
          (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
            ∃ htLp : MemLp (fun z => W (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))) 2 σ,
              J ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp
                (fun z => W (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t))))) ∧
          ∃ hG : MemLp G 2 σ, J ⟨0, le_rfl, hε.le⟩ = hG.toLp G := by
  intro b e T ξ C W D γ ν Ψ Γ G
  classical
  obtain ⟨Q, hQ, hQN⟩ := native_face_cone_normal_isometric_slices_L2
    (n := n) (E := Ambient q) (S := S) (a := a) (b₀ := b₀) (b₁ := b₁)
    hS hSbound ha hb₀ hbb hb₁ w H hf hSlices (g := g) hg hEnd
  refine ⟨Q, hQ, ?_⟩
  intro U hU hUC σ R
  have hK := hQN (closure U.val) hU hUC
  have hG : MemLp G 2 σ := hK.1.mono_measure (Measure.restrict_mono_set volume subset_closure)
  have hlim : Tendsto (fun t : ℝ => eLpNorm
      (fun z => W (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t))) - G z) 2 σ)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK.2.2
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _
        (Measure.restrict_mono_set volume subset_closure))
  have hgeometry : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ closure U.val,
      (e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).2 0 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin (n + 1), |(e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).1 i| <
        (e (Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).2 0 := hK.2.1.mono fun _ hi => hi.2
  obtain ⟨ε, hε, hεgeo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgeometry
  let V : OpenDomain ((n + 1) + 1) :=
    ⟨(fun y : Domain ((n + 1) + 1) => (e y).2 0) ⁻¹' Ioo (0 : ℝ) 1 ∩
      ⋂ i : Fin (n + 1), {y : Domain ((n + 1) + 1) | |(e y).1 i| < (e y).2 0},
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous))).inter
        (isOpen_iInter_of_finite (fun i : Fin (n + 1) =>
          isOpen_lt (((EuclideanSpace.proj i).continuous.comp
            (continuous_fst.comp e.continuous)).abs)
            ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous))))⟩
  have hWV : MemW12 V W D := (cubical_face_cone_extension_joint hn hw).1
  have hVset : V.val = {y : Domain ((n + 1) + 1) |
      (e y).2 0 ∈ Ioo (0 : ℝ) 1 ∧ ∀ i : Fin (n + 1), |(e y).1 i| < (e y).2 0} := by
    ext y
    simp only [V, mem_inter_iff, mem_preimage, mem_iInter, mem_setOf_eq]
  have hVfinite : (volume : Measure (Domain ((n + 1) + 1))) V.val ≠ ⊤ := by
    rw [hVset]
    exact volume_native_unit_face_cone_ne_top (n + 1)
  have hpull := memW12_isometric_preimage hVfinite hWV Q
  have hsub : (R ε).val ⊆ Q ⁻¹' V.val := by
    intro y hy
    have hOne : EuclideanSpace.single (0 : Fin 1) ((e y).2 0) = (e y).2 := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.single_apply, ite_true]
    have hrep : e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) = y := by
      rw [hOne, e.symm_apply_apply]
    have h := hεgeo hy.2 (e y).1 (subset_closure hy.1)
    rw [hrep] at h
    exact ⟨h.1, mem_iInter.mpr h.2⟩
  have hrect : MemW12 (R ε) (W ∘ Q) (fun y i =>
      ∑ j : Fin ((n + 1) + 1), (Q (EuclideanSpace.single i 1)) j • D (Q y) j) :=
    ⟨hpull.1.mono hsub, hpull.2.1.mono_measure (Measure.restrict_mono_set volume hsub),
      fun i => (hpull.2.2 i).mono_measure (Measure.restrict_mono_set volume hsub)⟩
  have hUfinite : (volume : Measure (Domain (n + 1))) U.val ≠ ⊤ :=
    ne_top_of_le_ne_top hU.measure_lt_top.ne (measure_mono subset_closure)
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr hUfinite
  obtain ⟨J, hJ, hJun⟩ := exists_unique_L2_trace_of_memW12_rectangle
    (n := n + 1) (q := q) U (a := 0) (b := ε) hε
      (u := W ∘ Q)
      (Du := fun y i => ∑ j : Fin ((n + 1) + 1), (Q (EuclideanSpace.single i 1)) j • D (Q y) j) hrect
  have hEndJ : J ⟨0, le_rfl, hε.le⟩ = hG.toLp G :=
    continuous_L2_trace_left_endpoint_of_raw_limit σ hε J
      (f := fun p : Domain (n + 1) × ℝ => W (Q (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))))
      hJ (g := G) hG hlim
  refine ⟨ε, hε, hrect, J, ⟨hJ, hG, hEndJ⟩, ?_⟩
  intro K hK
  exact hJun K hK.1

end StratificationTheory
