module

public import StratificationTheory.Foundation.CoordinateTraceRestrictions
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Continuous L2 slices with fixed scalar time coefficients

Two continuous endpoint families and actual scalar L2 time coefficients
produce one continuous L2 family of their pointwise affine combinations.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- Fixed scalar L2 coefficients transfer continuous endpoint families into
a continuous L2 curve representing every actual pointwise time slice. -/
theorem continuous_weighted_pair_lp_slices {T : Type*} [TopologicalSpace T] {q : ℕ}
    (ν : Measure ℝ) {α β : ℝ → ℝ} (hα : MemLp α 2 ν) (hβ : MemLp β 2 ν)
    (F G : C(T, Ambient q)) :
    ∃ H : C(T, Lp (Ambient q) 2 ν), ∀ s : T,
      ∃ hs : MemLp (fun t => β t • F s + α t • G s) 2 ν,
        H s = hs.toLp (fun t => β t • F s + α t • G s) := by
  let B : Ambient q →L[ℝ] ℝ →L[ℝ] Ambient q :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Ambient q →L[ℝ] Ambient q).flip
  let A := hα.toLp α
  let D := hβ.toLp β
  let MA : Ambient q →L[ℝ] Lp (Ambient q) 2 ν := (B.compLpL₂ 2 ν).flip A
  let MD : Ambient q →L[ℝ] Lp (Ambient q) 2 ν := (B.compLpL₂ 2 ν).flip D
  let H : C(T, Lp (Ambient q) 2 ν) :=
    ⟨fun s => MD (F s) + MA (G s),
      (MD.continuous.comp F.continuous).add (MA.continuous.comp G.continuous)⟩
  refine ⟨H, ?_⟩
  intro s
  have hEq : (fun t => (H s) t) =ᵐ[ν] (fun t => β t • F s + α t • G s) := by
    have hadd := Lp.coeFn_add ((B (F s)).compLp D) ((B (G s)).compLp A)
    have hD := (B (F s)).coeFn_compLp D
    have hA := (B (G s)).coeFn_compLp A
    filter_upwards [hadd, hD, hA, hβ.coeFn_toLp, hα.coeFn_toLp] with t ht htD htA htβ htα
    change (((B (F s)).compLp D) + ((B (G s)).compLp A)) t = _
    rw [ht, Pi.add_apply, htD, htA, htβ, htα]
    rfl
  have hs := (Lp.memLp (H s)).ae_eq hEq
  refine ⟨hs, ?_⟩
  apply Lp.ext
  exact hEq.trans hs.coeFn_toLp.symm

/-- Two continuous L2 curves with the same original interior a.e. slice
classes coincide on the entire closed interval. -/
theorem continuous_lp_curves_eq_of_ae_interior_slices {X : Type*} [MeasurableSpace X]
    {q : ℕ} (μ : Measure X) {a b : ℝ} (hab : a < b) {f : X × ℝ → Ambient q}
    (H K : C(Icc a b, Lp (Ambient q) 2 μ))
    (hH : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 μ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t)))
    (hK : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => f (x, t)) 2 μ,
        K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => f (x, t))) : K = H := by
  have hdiff : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      (K - H) ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 μ)) := by
    filter_upwards [hH, hK] with t hHt hKt ht
    obtain ⟨hHs, hHeq⟩ := hHt ht
    obtain ⟨hKs, hKeq⟩ := hKt ht
    change K ⟨t, ht.1.le, ht.2.le⟩ - H ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set _)
    rw [mem_singleton_iff, sub_eq_zero]
    exact hKeq.trans ((hKs.toLp_congr hHs (Filter.EventuallyEq.rfl)).trans hHeq.symm)
  have hz := continuous_interval_mem_closed_of_ae hab (K - H) isClosed_singleton hdiff
  apply ContinuousMap.ext
  intro t
  exact sub_eq_zero.mp (mem_singleton_iff.mp (hz t))

end StratificationTheory
