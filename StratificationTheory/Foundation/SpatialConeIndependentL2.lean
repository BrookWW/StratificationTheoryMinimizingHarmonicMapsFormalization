module

public import StratificationTheory.Foundation.SpatialConeTimeProductDomination
public import StratificationTheory.Foundation.ConicalTraceParameter

/-!
# Spatial cone L2 limits with an unchanged independent parameter

Genuine product L2 errors pull back to the actual spatial cone and converge
in its native product measure. The independent parameter is never dilated.
Original continuous flat L2 traces consequently give the actual reciprocal
parallel-side limits in these coordinates.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- A bounded-height spatial inverse cone preserves a genuine original
product L2 limit while carrying the independent parameter unchanged. -/
theorem tendsto_native_cone_independent_parameter_L2
    {ι A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {l : Filter ι} {n : ℕ} (τ : Measure A) [SFinite τ]
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) {M : ℝ} (hJM : ∀ t ∈ J, t ≤ M)
    (f : ι → (Domain n × A) × ℝ → E)
    (hf : ∀ᶠ i in l, MemLp (f i) 2 (((volume.restrict S).prod τ).prod (volume.restrict J)))
    (hlim : Tendsto (fun i => eLpNorm (f i) 2
      (((volume.restrict S).prod τ).prod (volume.restrict J))) l (𝓝 0)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ J ∧ ξ y ∈ S}
    let F : ι → Domain (n + 1) × A → E := fun i p => f i ((ξ p.1, p.2), T p.1)
    (∀ᶠ i in l, MemLp (F i) 2 ((volume.restrict C).prod τ)) ∧
      Tendsto (fun i => eLpNorm (F i) 2 ((volume.restrict C).prod τ)) l (𝓝 0) := by
  intro e T ξ C F
  let μ := ((volume : Measure (Domain n)).restrict S).prod τ
  let ν := (volume : Measure ℝ).restrict J
  let σ := ((volume : Measure (Domain (n + 1))).restrict C).prod τ
  let Q : Domain (n + 1) × A → (Domain n × A) × ℝ := fun p => ((ξ p.1, p.2), T p.1)
  have hT : Measurable T :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.comp
      (measurable_snd.comp e.continuous.measurable)
  have hξ : Measurable ξ := hT.inv.smul (measurable_fst.comp e.continuous.measurable)
  have hQ : Measurable Q :=
    ((hξ.comp measurable_fst).prodMk measurable_snd).prodMk (hT.comp measurable_fst)
  have hdom : Measure.map Q σ ≤ ENNReal.ofReal (M ^ n) • (μ.prod ν) :=
    map_native_inverse_cone_independent_parameter_le_smul τ hS hJ hJpos hJM
  have hmem : ∀ᶠ i in l, MemLp (F i) 2 σ := by
    filter_upwards [hf] with i hi
    exact memLp_comp_of_map_le_smul hQ.aemeasurable ENNReal.ofReal_ne_top hdom hi
  refine ⟨hmem, ?_⟩
  have hfinite : (ENNReal.ofReal (M ^ n)) ^ ((1 : ℝ≥0∞) / 2).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hbound := ENNReal.Tendsto.const_mul hlim (Or.inr hfinite)
  rw [mul_zero] at hbound
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hf] with i hi
  exact eLpNorm_comp_le_of_map_le_smul hQ.aemeasurable hdom hi.aestronglyMeasurable

/-- Original flat L2 slice curves determine true parallel-side errors for a
spatial cone, with every independent-time value retained unchanged. -/
theorem native_spatial_cone_raw_parameter_L2 {A E : Type*}
    [MeasurableSpace A] [NormedAddCommGroup E]
    {n : ℕ} (τ : Measure A) [IsFiniteMeasure τ]
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSfinite : (volume : Measure (Domain n)) S ≠ ⊤)
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (H : C(Icc a 1, Lp E 2 ((volume.restrict S).prod τ)))
    (f : (Domain n × A) × ℝ → E)
    (hf : AEStronglyMeasurable f (((volume.restrict S).prod τ).prod (volume.restrict (Ioo a 1))))
    (hSlices : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 ((volume.restrict S).prod τ),
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x => f (x,z)))
    (g : Domain n × A → E) (hg : MemLp g 2 ((volume.restrict S).prod τ))
    (hEnd : H ⟨1, ha.le, le_rfl⟩ = hg.toLp g) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (e y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (e y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let R : ℝ → Domain (n + 1) × A → E := fun δ p =>
      f ((ξ p.1,p.2),1 - δ / T p.1) - g (ξ p.1,p.2)
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (R δ) 2 ((volume.restrict C).prod τ)) ∧
      Tendsto (fun δ => eLpNorm (R δ) 2 ((volume.restrict C).prod τ))
        (𝓝[>] 0) (𝓝 0) := by
  intro e T ξ C R
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  have hraw := tendsto_raw_conical_parameter_L2 (b₁ := b₁) ((volume.restrict S).prod τ) ha hb₀
    H hf hSlices hg hEnd
  exact tendsto_native_cone_independent_parameter_L2 τ hS measurableSet_Icc
    (fun _ ht => hb₀.trans_le ht.1) (M := b₁) (fun _ ht => ht.2)
    (fun δ p => f (p.1,1 - δ / p.2) - g p.1) hraw.1 hraw.2.2

end StratificationTheory
