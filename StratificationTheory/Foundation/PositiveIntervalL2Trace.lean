module

public import StratificationTheory.Foundation.UnitIntervalL2Trace

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- The literal inverse time normalization carries a complete original unit
trace to the physical positive segment and retains both endpoint classes. -/
theorem exists_positive_segment_L2_trace_of_unit_interval {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X} {ε : ℝ} (hε : 0 < ε)
    (F : X × ℝ → E) (H : C(Icc (-1 : ℝ) 1, Lp E 2 μ))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, t))) :
    ∃ K : C(Icc (0 : ℝ) ε, Lp E 2 μ),
      (∀ r : Icc (0 : ℝ) ε, K r = H ⟨r.val / (ε / 2) - 1,
        by rw [le_sub_iff_add_le, neg_add_cancel, le_div_iff₀ (half_pos hε)]; simpa using r.property.1,
        by rw [sub_le_iff_le_add, div_le_iff₀ (half_pos hε)]; nlinarith [r.property.2]⟩) ∧
      (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
        ∃ hs : MemLp (fun x => F (x, r / (ε / 2) - 1)) 2 μ,
          K ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => F (x, r / (ε / 2) - 1))) ∧
      K ⟨0, le_rfl, hε.le⟩ = H ⟨-1, le_rfl, by norm_num⟩ ∧
      K ⟨ε, hε.le, le_rfl⟩ = H ⟨1, by norm_num, le_rfl⟩ ∧
      ∀ J : C(Icc (0 : ℝ) ε, Lp E 2 μ),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
          ∃ hs : MemLp (fun x => F (x, r / (ε / 2) - 1)) 2 μ,
            J ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => F (x, r / (ε / 2) - 1))) → J = K := by
  let τ : ℝ → ℝ := fun r => r / (ε / 2) - 1
  have hclosed (r : Icc (0 : ℝ) ε) : τ r.val ∈ Icc (-1 : ℝ) 1 := by
    dsimp only [τ]
    constructor
    · rw [le_sub_iff_add_le, neg_add_cancel, le_div_iff₀ (half_pos hε)]
      simpa using r.property.1
    · rw [sub_le_iff_le_add, div_le_iff₀ (half_pos hε)]
      nlinarith [r.property.2]
  let γ : C(Icc (0 : ℝ) ε, Icc (-1 : ℝ) 1) :=
    ⟨fun r => ⟨τ r.val, hclosed r⟩,
      ((continuous_subtype_val.div_const (ε / 2)).sub continuous_const).subtype_mk hclosed⟩
  let K := H.comp γ
  have hτ : Measure.QuasiMeasurePreserving τ (volume : Measure ℝ) volume := by
    have h := (measurePreserving_add_left (volume : Measure ℝ) (-1)).quasiMeasurePreserving.comp
      ((volume : Measure ℝ).quasiMeasurePreserving_smul (inv_ne_zero (half_pos hε).ne'))
    convert h using 1
    funext r
    change r / (ε / 2) - 1 = -1 + (ε / 2)⁻¹ * r
    rw [div_eq_mul_inv]
    ring
  have hK : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => F (x, τ r)) 2 μ,
        K ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun x => F (x, τ r)) := by
    filter_upwards [hτ.ae hH] with r hr hrI
    have hτI : τ r ∈ Ioo (-1 : ℝ) 1 := by
      dsimp only [τ]
      constructor
      · rw [lt_sub_iff_add_lt, neg_add_cancel, lt_div_iff₀ (half_pos hε)]
        simpa using hrI.1
      · rw [sub_lt_iff_lt_add, div_lt_iff₀ (half_pos hε)]
        nlinarith [hrI.2]
    exact hr hτI
  refine ⟨K, fun _ => rfl, hK, ?_, ?_, ?_⟩
  · change H ⟨τ 0, hclosed ⟨0, le_rfl, hε.le⟩⟩ = _
    simp only [τ, zero_div, zero_sub]
  · change H ⟨τ ε, hclosed ⟨ε, hε.le, le_rfl⟩⟩ = _
    have hτε : τ ε = 1 := by dsimp only [τ]; field_simp; ring
    simp only [hτε]
  · intro J hJ
    exact continuous_Lp_representatives_eq_of_ae_slices
      (f := fun z : X × ℝ => F (z.1, τ z.2)) (g := fun z : X × ℝ => F (z.1, τ z.2))
      hε J K hJ hK (Eventually.of_forall fun _ _ => EventuallyEq.rfl)

end StratificationTheory
