module

public import StratificationTheory.Foundation.RadialTraceCompatibility

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Continuous curves normalized by opposite actual raw time directions
have the same corresponding endpoint class. -/
theorem left_trace_eq_right_trace_of_reflected_raw_slices {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X)
    (F : X × ℝ → E) (H J : C(Icc (-1 : ℝ) 1, Lp E 2 μ))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, t)))
    (hJ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, -t)) 2 μ,
        J ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, -t))) :
    H ⟨-1, le_rfl, by norm_num⟩ = J ⟨1, by norm_num, le_rfl⟩ := by
  have hτ (t : Icc (-1 : ℝ) 1) : -t.val ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [t.property.2], by linarith [t.property.1]⟩
  let τ : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1) :=
    ⟨fun t => ⟨-t.val, hτ t⟩, continuous_subtype_val.neg.subtype_mk hτ⟩
  let K := H.comp τ
  have hK : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => F (x, -t)) 2 μ,
        K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => F (x, -t)) := by
    have hPull := ((volume : Measure ℝ).quasiMeasurePreserving_smul (by norm_num : (-1 : ℝ) ≠ 0)).ae hH
    filter_upwards [hPull] with t ht htI
    have hneg : -t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [htI.2], by linarith [htI.1]⟩
    change ∃ hs : MemLp (fun x => F (x, -t)) 2 μ,
      H ⟨-t, hneg.1.le, hneg.2.le⟩ = hs.toLp (fun x => F (x, -t))
    simpa only [smul_eq_mul, neg_one_mul] using ht (by simpa only [smul_eq_mul, neg_one_mul] using hneg)
  have hEq : K = J := continuous_Lp_representatives_eq_of_ae_slices
    (f := fun z : X × ℝ => F (z.1, -z.2)) (g := fun z : X × ℝ => F (z.1, -z.2))
    (by norm_num : (-1 : ℝ) < 1) K J hK hJ (Eventually.of_forall fun _ _ => EventuallyEq.rfl)
  exact congrArg (fun L => L ⟨1, by norm_num, le_rfl⟩) hEq

end StratificationTheory
