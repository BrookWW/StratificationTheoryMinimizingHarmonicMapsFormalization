module

public import StratificationTheory.Foundation.IntervalClosedConstraints
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- A left-hand limit of the original a.e. distance determines the right
endpoint of the whole continuous interval curve. -/
theorem continuous_interval_right_endpoint_of_ae_distance_limit {E : Type*}
    [NormedAddCommGroup E] {a b : ℝ} (hab : a < b)
    (H : C(Icc a b, E)) (g : E) {f : ℝ → ℝ}
    (hdist : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ‖H ⟨t, ht.1.le, ht.2.le⟩ - g‖ = f t)
    (hlim : Tendsto f (𝓝[<] b) (𝓝 0)) : H ⟨b, hab.le, le_rfl⟩ = g := by
  have hbound (ε : ℝ) (hε : 0 < ε) : ‖H ⟨b, hab.le, le_rfl⟩ - g‖ ≤ ε := by
    obtain ⟨c, hc, hsmall⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hab).mp
      (hlim.eventually (eventually_lt_nhds hε))
    let ι : C(Icc c b, Icc a b) :=
      ⟨fun t => ⟨t.val, hc.1.trans t.property.1, t.property.2⟩,
        continuous_subtype_val.subtype_mk _⟩
    let G : C(Icc c b, ℝ) := ⟨fun t => ‖H (ι t) - g‖,
      ((H.continuous.comp ι.continuous).sub continuous_const).norm⟩
    have hG : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo c b,
        G ⟨t, ht.1.le, ht.2.le⟩ ∈ Iic ε := by
      filter_upwards [hdist] with t ht htI
      change ‖H ⟨t, hc.1.trans htI.1.le, htI.2.le⟩ - g‖ ≤ ε
      rw [ht ⟨hc.1.trans_lt htI.1, htI.2⟩]
      exact (hsmall htI).le
    exact continuous_interval_mem_closed_of_ae hc.2 G isClosed_Iic hG ⟨b, hc.2.le, le_rfl⟩
  have hz : ‖H ⟨b, hab.le, le_rfl⟩ - g‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hnot
    have hp : 0 < ‖H ⟨b, hab.le, le_rfl⟩ - g‖ := lt_of_not_ge hnot
    have hhalf := hbound _ (half_pos hp)
    linarith only [hhalf, hp]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- A right-hand limit of the original a.e. distance determines the left
endpoint of the whole continuous interval curve. -/
theorem continuous_interval_left_endpoint_of_ae_distance_limit {E : Type*}
    [NormedAddCommGroup E] {a b : ℝ} (hab : a < b)
    (H : C(Icc a b, E)) (g : E) {f : ℝ → ℝ}
    (hdist : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ‖H ⟨t, ht.1.le, ht.2.le⟩ - g‖ = f t)
    (hlim : Tendsto f (𝓝[>] a) (𝓝 0)) : H ⟨a, le_rfl, hab.le⟩ = g := by
  have hbound (ε : ℝ) (hε : 0 < ε) : ‖H ⟨a, le_rfl, hab.le⟩ - g‖ ≤ ε := by
    obtain ⟨c, hc, hsmall⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab).mp
      (hlim.eventually (eventually_lt_nhds hε))
    let ι : C(Icc a c, Icc a b) :=
      ⟨fun t => ⟨t.val, t.property.1, t.property.2.trans hc.2⟩,
        continuous_subtype_val.subtype_mk _⟩
    let G : C(Icc a c, ℝ) := ⟨fun t => ‖H (ι t) - g‖,
      ((H.continuous.comp ι.continuous).sub continuous_const).norm⟩
    have hG : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a c,
        G ⟨t, ht.1.le, ht.2.le⟩ ∈ Iic ε := by
      filter_upwards [hdist] with t ht htI
      change ‖H ⟨t, htI.1.le, htI.2.le.trans hc.2⟩ - g‖ ≤ ε
      rw [ht ⟨htI.1, htI.2.trans_le hc.2⟩]
      exact (hsmall htI).le
    exact continuous_interval_mem_closed_of_ae hc.1 G isClosed_Iic hG ⟨a, le_rfl, hc.1.le⟩
  have hz : ‖H ⟨a, le_rfl, hab.le⟩ - g‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hnot
    have hp : 0 < ‖H ⟨a, le_rfl, hab.le⟩ - g‖ := lt_of_not_ge hnot
    have hhalf := hbound _ (half_pos hp)
    linarith only [hhalf, hp]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- A genuine original-slice L2 limit identifies the right endpoint trace
class, regardless of raw values on the endpoint face. -/
theorem continuous_L2_trace_right_endpoint_of_raw_limit {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X)
    {a b : ℝ} (hab : a < b) (H : C(Icc a b, Lp E 2 μ)) {f : X × ℝ → E}
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x => f (x,t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (x,t)))
    {g : X → E} (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun t => eLpNorm (fun x => f (x,t) - g x) 2 μ) (𝓝[<] b) (𝓝 0)) :
    H ⟨b, hab.le, le_rfl⟩ = hg.toLp g := by
  have hdist : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ‖H ⟨t, ht.1.le, ht.2.le⟩ - hg.toLp g‖ =
        (eLpNorm (fun x => f (x,t) - g x) 2 μ).toReal := by
    filter_upwards [hH] with t ht htI
    obtain ⟨hs, hEq⟩ := ht htI
    rw [hEq, ← hs.toLp_sub hg, Lp.norm_toLp]
    rfl
  apply continuous_interval_right_endpoint_of_ae_distance_limit hab H (hg.toLp g) hdist
  have h := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hlim
  simpa only [Function.comp_def, ENNReal.toReal_zero] using h

/-- A genuine original-slice L2 limit identifies the left endpoint trace
class, regardless of raw values on the endpoint face. -/
theorem continuous_L2_trace_left_endpoint_of_raw_limit {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X)
    {a b : ℝ} (hab : a < b) (H : C(Icc a b, Lp E 2 μ)) {f : X × ℝ → E}
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x => f (x,t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (x,t)))
    {g : X → E} (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun t => eLpNorm (fun x => f (x,t) - g x) 2 μ) (𝓝[>] a) (𝓝 0)) :
    H ⟨a, le_rfl, hab.le⟩ = hg.toLp g := by
  have hdist : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ‖H ⟨t, ht.1.le, ht.2.le⟩ - hg.toLp g‖ =
        (eLpNorm (fun x => f (x,t) - g x) 2 μ).toReal := by
    filter_upwards [hH] with t ht htI
    obtain ⟨hs, hEq⟩ := ht htI
    rw [hEq, ← hs.toLp_sub hg, Lp.norm_toLp]
    rfl
  apply continuous_interval_left_endpoint_of_ae_distance_limit hab H (hg.toLp g) hdist
  have h := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hlim
  simpa only [Function.comp_def, ENNReal.toReal_zero] using h

end StratificationTheory
