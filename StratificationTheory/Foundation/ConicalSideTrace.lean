module
public import StratificationTheory.Foundation.ConicalTraceParameter
public import StratificationTheory.Foundation.CubicalConeProductL2
public import StratificationTheory.Foundation.ConicalSideGeometry
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Original cone slices at a lateral face

Continuous flat face traces determine the literal inward parallel slices
of the same degree-zero cone map. Their L2 limits hold first in native
height coordinates and then on a fixed native Hausdorff surface patch.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Original flat L2 trace data produce the same raw reciprocal slices in
actual native inverse-cone coordinates, with their full L2 limit. -/
theorem native_cone_raw_parameter_L2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) (hSfinite : (volume : Measure (Domain n)) S ≠ ⊤)
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀) (hbb : b₀ < b₁)
    (H : C(Icc a 1, Lp E 2 (volume.restrict S))) {f : Domain n × ℝ → E}
    (hf : AEStronglyMeasurable f ((volume.restrict S).prod (volume.restrict (Ioo a 1))))
    (hSlices : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 (volume.restrict S),
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x => f (x,z)))
    {g : Domain n → E} (hg : MemLp g 2 (volume.restrict S))
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let R : ℝ → Domain (n + 1) → E := fun δ y => f (ξ y, 1 - δ / T y) - g (ξ y)
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (R δ) 2 (volume.restrict C)) ∧
      Tendsto (fun δ : ℝ => ∫ y in C, ‖R δ y‖ ^ 2) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun δ : ℝ => eLpNorm (R δ) 2 (volume.restrict C)) (𝓝[>] 0) (𝓝 0) := by
  intro e T ξ C R
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  have hRaw := StratificationTheory.tendsto_raw_conical_parameter_L2
    (b₁ := b₁) (volume.restrict S) ha hb₀ H hf hSlices hg hEnd
  have hSq : Tendsto (fun δ : ℝ => ∫ p : Domain n × ℝ,
      ‖f (p.1, 1 - δ / p.2) - g p.1‖ ^ 2
        ∂((volume.restrict S).prod (volume.restrict (Icc b₀ b₁)))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [pow_zero, one_mul] using (hRaw.2.1 0).2
  exact StratificationTheory.tendsto_native_cone_L2_of_product
    hS measurableSet_Icc (fun _ ht => hb₀.trans_le ht.1)
    (hb₀.trans hbb).le (fun _ ht => ht.2) hRaw.1 hSq


/-- On positive compact height bands, the same literal degree-zero extension
has its original parallel-side slices converging in the native parameter L2
space. The slices lie in the actual open cone and the exact parallel planes. -/
theorem native_face_cone_parallel_side_L2 {n : ℕ} {E : Type*}
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
    let R : ℝ → Domain (n + 1) → E := fun δ y => W (γ δ y) - g (ξ y)
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (R δ) 2 (volume.restrict C) ∧
      ∀ y ∈ C,
        ((e (γ δ y)).2 0 ∈ Ioo (0 : ℝ) 1 ∧
          ∀ i : Fin (n + 1), |(e (γ δ y)).1 i| < (e (γ δ y)).2 0) ∧
        (e (γ δ y)).2 0 - (b (e (γ δ y)).1).2 0 = δ) ∧
      Tendsto (fun δ : ℝ => ∫ y in C, ‖R δ y‖ ^ 2) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun δ : ℝ => eLpNorm (R δ) 2 (volume.restrict C)) (𝓝[>] 0) (𝓝 0) := by
  intro b e T ξ C W γ R
  let f : Domain n × ℝ → E := fun p => w (b.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  have hSfinite : (volume : Measure (Domain n)) S ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_unit_coordinate_face_ne_top n) (measure_mono (fun x hx =>
      (mem_unit_coordinate_face_iff x).mpr (hSbound x hx)))
  have hNative := native_cone_raw_parameter_L2 hS hSfinite ha hb₀ hbb H hf hSlices hg hEnd
  have hC : MeasurableSet C :=
    (measurableSet_Icc.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp b.continuous)).measurable).inter
      (hS.preimage (((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp b.continuous)).measurable.inv.smul
        (measurable_fst.comp b.continuous.measurable)))
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 2 * b₀ :=
    Ioo_mem_nhdsGT (by positivity)
  have hdata : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ y ∈ C, R δ y = f (ξ y, 1 - δ / T y) - g (ξ y)) ∧
      ∀ y ∈ C,
        ((e (γ δ y)).2 0 ∈ Ioo (0 : ℝ) 1 ∧
          ∀ i : Fin (n + 1), |(e (γ δ y)).1 i| < (e (γ δ y)).2 0) ∧
        (e (γ δ y)).2 0 - (b (e (γ δ y)).1).2 0 = δ := by
    filter_upwards [hsmall] with δ hδ
    have hgeometry (y : Domain (n + 1)) (hy : y ∈ C) := by
      have htpos : 0 < T y := hb₀.trans_le hy.1.1
      have hδt : δ < 2 * T y := hδ.2.trans_le (by linarith only [hy.1.1])
      have hx : ∀ i : Fin n, |(b y).1 i| < T y := by
        intro i
        have hi := hSbound (ξ y) hy.2 i
        change |(T y)⁻¹ * (b y).1 i| < 1 at hi
        rw [abs_mul, abs_of_pos (inv_pos.mpr htpos)] at hi
        have hi' : |(b y).1 i| / T y < 1 := by
          simpa only [div_eq_mul_inv, mul_comm] using hi
        exact (div_lt_one htpos).mp hi'
      exact native_face_cone_parallel_side_slice w htpos hδ.1 hδt (b y).1 hx
    refine ⟨?_, ?_⟩
    · intro y hy
      exact congrArg (fun z => z - g (ξ y)) (hgeometry y hy).1
    · intro y hy
      refine ⟨⟨?_, (hgeometry y hy).2.2⟩, (hgeometry y hy).2.1⟩
      simpa only [γ, e.apply_symm_apply, PiLp.single_apply, ite_true] using
        (show T y ∈ Ioo (0 : ℝ) 1 from ⟨hb₀.trans_le hy.1.1, hy.1.2.trans_lt hb₁⟩)
  have hAE : ∀ᶠ δ in 𝓝[>] (0 : ℝ), R δ =ᵐ[volume.restrict C]
      (fun y => f (ξ y, 1 - δ / T y) - g (ξ y)) := by
    filter_upwards [hdata] with δ hδ
    filter_upwards [ae_restrict_mem hC] with y hy
    exact hδ.1 y hy
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hNative.1, hAE, hdata] with δ hL hEq hδ
    exact ⟨hL.ae_eq hEq.symm, hδ.2⟩
  · apply hNative.2.1.congr'
    filter_upwards [hAE] with δ hEq
    exact integral_congr_ae (hEq.symm.mono fun y hy => congrArg (fun z => ‖z‖ ^ 2) hy)
  · apply hNative.2.2.congr'
    filter_upwards [hAE] with δ hEq
    exact eLpNorm_congr_ae hEq.symm

/-- The actual height chart transfers raw L2 fields to the native surface
measure on every measurable lateral patch, with the exact area factor. -/
theorem native_lateral_height_L2_transport {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (δ : ℝ) {C : Set (Domain (n + 1))} (hC : MeasurableSet C) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let Γ : Domain (n + 1) → Domain ((n + 1) + 1) := fun y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 - δ)),
        EuclideanSpace.single (0 : Fin 1) ((b y).2 0))
    let σ := (Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict (Γ '' C)
    MeasurableEmbedding Γ ∧
      MeasurePreserving Γ (ENNReal.ofReal (Real.sqrt 2) • volume.restrict C) σ ∧
      ∀ F : Domain ((n + 1) + 1) → E,
        MemLp (F ∘ Γ) 2 (volume.restrict C) →
          MemLp F 2 σ ∧ Integrable (fun z => ‖F z‖ ^ 2) σ ∧
          (∫ z, ‖F z‖ ^ 2 ∂σ) = Real.sqrt 2 * ∫ y in C, ‖F (Γ y)‖ ^ 2 := by
  intro b e Γ σ
  let P : Set (Domain ((n + 1) + 1)) := {z | (e z).2 0 - (b (e z).1).2 0 = δ}
  have hsingle : Isometry (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    intro r s
    exact PiLp.edist_single_same 2 (fun _ : Fin 1 => ℝ) 0 r s
  have ht : Continuous (fun y : Domain (n + 1) => (b y).2 0) :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_snd.comp b.continuous)
  have hΓcont : Continuous Γ :=
    e.symm.continuous.comp ((b.symm.continuous.comp
      ((continuous_fst.comp b.continuous).prodMk
        (hsingle.continuous.comp (ht.sub continuous_const)))).prodMk (hsingle.continuous.comp ht))
  have hΓinj : Function.Injective Γ := by
    intro x y hxy
    apply b.injective
    apply Prod.ext
    · have h := congrArg (fun z => (b (e z).1).1) hxy
      simpa only [Γ, e.apply_symm_apply, b.apply_symm_apply] using h
    · ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have h := congrArg (fun z => (e z).2 0) hxy
      simpa only [Γ, e.apply_symm_apply, PiLp.single_apply, ite_true] using h
  have hEmb : MeasurableEmbedding Γ := hΓcont.measurableEmbedding hΓinj
  have hsub : Γ '' C ⊆ P := by
    rintro z ⟨y, _hy, rfl⟩
    change (e (Γ y)).2 0 - (b (e (Γ y)).1).2 0 = δ
    simp only [Γ, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
    ring
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmap : Measure.map Γ (ENNReal.ofReal (Real.sqrt 2) • volume) =
      (Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict P := by
    rw [Measure.map_smul, map_native_cone_lateral_height_chart n δ, smul_smul,
      ← ENNReal.ofReal_mul hsqrtpos.le, mul_inv_cancel₀ hsqrtpos.ne', ENNReal.ofReal_one, one_smul]
  have hrestrict := hEmb.restrict_map (ENNReal.ofReal (Real.sqrt 2) • volume) (Γ '' C)
  rw [hmap, Measure.restrict_restrict (hEmb.measurableSet_image' hC),
    inter_eq_left.mpr hsub, hΓinj.preimage_image, Measure.restrict_smul] at hrestrict
  have hMP : MeasurePreserving Γ (ENNReal.ofReal (Real.sqrt 2) • volume.restrict C) σ :=
    ⟨hEmb.measurable, hrestrict.symm⟩
  refine ⟨hEmb, hMP, ?_⟩
  intro F hF
  have hL : MemLp F 2 σ := by
    rw [← hMP.map_eq]
    exact hEmb.memLp_map_measure_iff.mpr (hF.smul_measure ENNReal.ofReal_ne_top)
  refine ⟨hL, hL.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0), ?_⟩
  rw [← hMP.map_eq, hEmb.integral_map, integral_smul_measure,
    ENNReal.toReal_ofReal hsqrtpos.le, smul_eq_mul]

/-- The original inward parallel slices converge on one fixed lateral patch
in its actual native codimension-one Hausdorff L2 measure. -/
theorem native_face_cone_parallel_side_surface_L2 {n : ℕ} {E : Type*}
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
    let σ := (Measure.euclideanHausdorffMeasure (n + 1) : Measure (Domain ((n + 1) + 1))).restrict (γ 0 '' C)
    let F : ℝ → Domain ((n + 1) + 1) → E := fun δ z =>
      W (e.symm (b.symm ((b (e z).1).1,
        EuclideanSpace.single (0 : Fin 1) ((b (e z).1).2 0 - δ)), (e z).2)) -
        g (((e z).2 0)⁻¹ • (b (e z).1).1)
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (F δ) 2 σ) ∧
      Tendsto (fun δ : ℝ => ∫ z, ‖F δ z‖ ^ 2 ∂σ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun δ : ℝ => eLpNorm (F δ) 2 σ) (𝓝[>] 0) (𝓝 0) := by
  intro b e T ξ C W γ σ F
  let R : ℝ → Domain (n + 1) → E := fun δ y => W (γ δ y) - g (ξ y)
  have hpar := native_face_cone_parallel_side_L2 hS hSbound ha hb₀ hbb hb₁ w H hf hSlices hg hEnd
  have hC : MeasurableSet C :=
    (measurableSet_Icc.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp b.continuous)).measurable).inter
      (hS.preimage (((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp b.continuous)).measurable.inv.smul
        (measurable_fst.comp b.continuous.measurable)))
  have htrans := native_lateral_height_L2_transport (E := E) (n := n) 0 hC
  have htransport : ∀ G : Domain ((n + 1) + 1) → E,
      MemLp (G ∘ γ 0) 2 (volume.restrict C) →
        MemLp G 2 σ ∧ Integrable (fun z => ‖G z‖ ^ 2) σ ∧
        (∫ z, ‖G z‖ ^ 2 ∂σ) = Real.sqrt 2 * ∫ y in C, ‖G (γ 0 y)‖ ^ 2 := htrans.2.2
  have hpull (δ : ℝ) : F δ ∘ γ 0 = R δ := by
    funext y
    simp only [F, R, Function.comp_apply, γ, ξ, T, e.apply_symm_apply,
      b.apply_symm_apply, PiLp.single_apply, ite_true, sub_zero]
  have hLp : ∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (F δ) 2 σ := by
    filter_upwards [hpar.1] with δ hδ
    have hR : MemLp (F δ ∘ γ 0) 2 (volume.restrict C) := by
      rw [hpull]
      exact hδ.1
    exact (htransport (F δ) hR).1
  have hsq : Tendsto (fun δ : ℝ => ∫ z, ‖F δ z‖ ^ 2 ∂σ) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun δ : ℝ => Real.sqrt 2 * ∫ y in C, ‖R δ y‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hpar.2.1
    apply hlim.congr'
    filter_upwards [hpar.1] with δ hδ
    have hR : MemLp (F δ ∘ γ 0) 2 (volume.restrict C) := by
      rw [hpull]
      exact hδ.1
    have heq := (htransport (F δ) hR).2.2
    have heqPull : (fun y => ‖F δ (γ 0 y)‖ ^ 2) = (fun y => ‖R δ y‖ ^ 2) := by
      funext y
      exact congrArg (fun z => ‖z‖ ^ 2) (congrFun (hpull δ) y)
    rw [heqPull] at heq
    exact heq.symm
  refine ⟨hLp, hsq, ?_⟩
  have heq : (fun δ => eLpNorm (F δ) 2 σ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ => ENNReal.ofReal (Real.sqrt (∫ z, ‖F δ z‖ ^ 2 ∂σ))) := by
    filter_upwards [hLp] with δ hδ
    rw [Real.sqrt_eq_rpow]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] using
      hδ.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  apply (tendsto_congr' heq).mpr
  have ht := ENNReal.tendsto_ofReal (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  simpa only [Function.comp_apply, Real.sqrt_zero, ENNReal.ofReal_zero] using ht

end StratificationTheory
