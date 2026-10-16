module

public import StratificationTheory.Foundation.CoordinateL2Trace

/-!
# Matching flat traces across an interior coordinate cut

The restrictions of one continuous L2 curve give the unique traces on both
subintervals. At almost every interior cut their common value is the original
raw slice class, with the same slice-membership witness on both sides.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology
namespace StratificationTheory

private theorem continuous_lp_curves_eq_of_ae_slices {α : Type*}
    [MeasurableSpace α] {q : ℕ} (σ : Measure α)
    {a b : ℝ} (hab : a < b) {f : α × ℝ → Ambient q}
    (H K : C(Icc a b, Lp (Ambient q) 2 σ))
    (hH : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t)))
    (hK : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
        K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) : K = H := by
  have hdiff : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      (K - H) ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ)) := by
    filter_upwards [hH, hK] with t hHt hKt ht
    obtain ⟨hHs, hHeq⟩ := hHt ht
    obtain ⟨hKs, hKeq⟩ := hKt ht
    change K ⟨t, ht.1.le, ht.2.le⟩ - H ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ))
    rw [mem_singleton_iff, sub_eq_zero]
    exact hKeq.trans ((hKs.toLp_congr hHs (Filter.EventuallyEq.rfl)).trans hHeq.symm)
  have hz := continuous_interval_mem_closed_of_ae hab (K - H) isClosed_singleton hdiff
  apply ContinuousMap.ext
  intro t
  exact sub_eq_zero.mp (mem_singleton_iff.mp (hz t))

/-- Both subinterval traces of the same continuous native L2 curve match
the same raw slice class at almost every interior cut, and each restriction
is uniquely determined by its original interior raw slice classes. -/
theorem continuous_lp_trace_cut_restrictions {α : Type*} [MeasurableSpace α]
    {q : ℕ} (σ : Measure α) {a b : ℝ} (_hab : a < b)
    {f : α × ℝ → Ambient q} (H : C(Icc a b, Lp (Ambient q) 2 σ))
    (hH : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) :
    ∀ᵐ c ∂volume, ∀ hc : c ∈ Ioo a b,
      ∃ hcut : MemLp (fun x => f (x, c)) 2 σ,
      ∃ L : C(Icc a c, Lp (Ambient q) 2 σ), ∃ R : C(Icc c b, Lp (Ambient q) 2 σ),
        (∀ t : Icc a c, L t = H ⟨t.val, t.property.1, t.property.2.trans hc.2.le⟩) ∧
        (∀ t : Icc c b, R t = H ⟨t.val, hc.1.le.trans t.property.1, t.property.2⟩) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
          ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
            L ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) ∧
        (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
          ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
            R ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) ∧
        L ⟨c, hc.1.le, le_rfl⟩ = hcut.toLp (fun x => f (x, c)) ∧
        R ⟨c, le_rfl, hc.2.le⟩ = hcut.toLp (fun x => f (x, c)) ∧
        (∀ K : C(Icc a c, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
            ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) → K = L) ∧
        ∀ K : C(Icc c b, Lp (Ambient q) 2 σ),
          (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
            ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
              K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) → K = R := by
  filter_upwards [hH] with c hHc
  intro hc
  obtain ⟨hcut, hcutEq⟩ := hHc hc
  let ιL : C(Icc a c, Icc a b) :=
    ⟨fun t => ⟨t.val, t.property.1, t.property.2.trans hc.2.le⟩,
      continuous_subtype_val.subtype_mk _⟩
  let ιR : C(Icc c b, Icc a b) :=
    ⟨fun t => ⟨t.val, hc.1.le.trans t.property.1, t.property.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let L := H.comp ιL
  let R := H.comp ιR
  have hL : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a c,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
        L ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t)) := by
    filter_upwards [hH] with t ht htI
    exact ht ⟨htI.1, htI.2.trans hc.2⟩
  have hR : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo c b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 σ,
        R ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t)) := by
    filter_upwards [hH] with t ht htI
    exact ht ⟨hc.1.trans htI.1, htI.2⟩
  refine ⟨hcut, L, R, fun _ => rfl, fun _ => rfl, hL, hR, hcutEq, hcutEq, ?_, ?_⟩
  · intro K hK
    exact continuous_lp_curves_eq_of_ae_slices σ hc.1 L K hL hK
  · intro K hK
    exact continuous_lp_curves_eq_of_ae_slices σ hc.2 R K hR hK

end StratificationTheory
