module

public import StratificationTheory.Foundation.AngularL2Membership
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.CompactOpen

/-!
# Continuous scalar fluxes of a native radial L2 trace

A continuous native-L2 curve pairs continuously with the radial restriction
of any continuous ambient test. The actual representative integral is
identified at every closed-interval radius, including the endpoints.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped RealInnerProductSpace
namespace StratificationTheory

/-- Pairing a continuous native-L2 curve with a radial scalar test gives
one continuous closed-interval scalar flux and an actual integrable formula. -/
theorem exists_continuous_radial_trace_flux {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (c : Domain n) (ψ : Domain n → ℝ) (hψ : Continuous ψ)
    (i : Fin n) (j : Fin q)
    (H : C(Icc a b, Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)))) :
    ∃ J : C(Icc a b, ℝ), ∀ r : Icc a b,
      Integrable (fun θ : sphere (0 : Domain n) 1 =>
        (H r θ) j * ψ (c + r.val • θ.val) * θ.val i)
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
      J r = r.val ^ (n - 1) *
        ∫ θ : sphere (0 : Domain n) 1,
          (H r θ) j * ψ (c + r.val • θ.val) * θ.val i
            ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  let G : C(Icc a b, C(sphere (0 : Domain n) 1, Ambient q)) :=
    (⟨fun p : Icc a b × sphere (0 : Domain n) 1 =>
      (ψ (c + p.1.val • p.2.val) * p.2.val i) • EuclideanSpace.single j (1 : ℝ),
        ((hψ.comp (continuous_const.add
          ((continuous_subtype_val.comp continuous_fst).smul
            (continuous_subtype_val.comp continuous_snd)))).mul
          ((EuclideanSpace.proj i).continuous.comp
            (continuous_subtype_val.comp continuous_snd))).smul continuous_const⟩ :
      C(Icc a b × sphere (0 : Domain n) 1, Ambient q)).curry
  let V : C(Icc a b, Lp (Ambient q) 2 σ) :=
    ⟨fun r => ContinuousMap.toLp 2 σ ℝ (G r),
      (ContinuousMap.toLp 2 σ ℝ).continuous.comp G.continuous⟩
  let J : C(Icc a b, ℝ) :=
    ⟨fun r => r.val ^ (n - 1) * inner ℝ (H r) (V r),
      (continuous_subtype_val.pow (n - 1)).mul (H.continuous.inner V.continuous)⟩
  refine ⟨J, ?_⟩
  intro r
  have hEq : (fun θ : sphere (0 : Domain n) 1 => inner ℝ (H r θ) (V r θ)) =ᵐ[σ]
      (fun θ => (H r θ) j * ψ (c + r.val • θ.val) * θ.val i) := by
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) σ (G r)] with θ hθ
    change inner ℝ (H r θ) ((ContinuousMap.toLp 2 σ ℝ (G r)) θ) = _
    rw [hθ]
    change inner ℝ (H r θ)
      ((ψ (c + r.val • θ.val) * θ.val i) • EuclideanSpace.single j (1 : ℝ)) = _
    rw [real_inner_smul_right, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    ring
  exact ⟨(L2.integrable_inner (H r) (V r)).congr hEq, by
    change r.val ^ (n - 1) * inner ℝ (H r) (V r) = _
    rw [L2.inner_def, integral_congr_ae hEq]⟩

/-- The original interior radial normalization identifies the same continuous
flux with the original raw map on almost every radius. It does not assign
raw endpoint values to either trace. -/
theorem exists_continuous_radial_flux_of_raw_trace {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (c : Domain n) (u : Domain n → Ambient q)
    (H : C(Icc a b, Lp (Ambient q) 2
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))))
    (hH : ∀ᵐ (r : ℝ) ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) 2
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)),
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)))
    (ψ : Domain n → ℝ) (hψ : Continuous ψ) (i : Fin n) (j : Fin q) :
    ∃ J : C(Icc a b, ℝ),
      (∀ r : Icc a b, J r = r.val ^ (n - 1) *
        ∫ θ : sphere (0 : Domain n) 1,
          (H r θ) j * ψ (c + r.val • θ.val) * θ.val i
            ∂Measure.euclideanHausdorffMeasure (n - 1)) ∧
      ∀ᵐ (r : ℝ) ∂volume, ∀ hr : r ∈ Ioo a b,
        Integrable (fun θ : sphere (0 : Domain n) 1 =>
          (u (c + r • θ.val)) j * ψ (c + r • θ.val) * θ.val i)
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)) ∧
        J ⟨r, hr.1.le, hr.2.le⟩ = r ^ (n - 1) *
          ∫ θ : sphere (0 : Domain n) 1,
            (u (c + r • θ.val)) j * ψ (c + r • θ.val) * θ.val i
              ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  obtain ⟨J, hJ⟩ := exists_continuous_radial_trace_flux hn c ψ hψ i j H
  refine ⟨J, fun r => (hJ r).2, ?_⟩
  filter_upwards [hH] with r hr hrI
  obtain ⟨hslice, hsliceEq⟩ := hr hrI
  let rI : Icc a b := ⟨r, hrI.1.le, hrI.2.le⟩
  have hEq : (fun θ : sphere (0 : Domain n) 1 =>
      (H rI θ) j * ψ (c + r • θ.val) * θ.val i) =ᵐ[
        Measure.euclideanHausdorffMeasure (n - 1)]
      (fun θ => (u (c + r • θ.val)) j * ψ (c + r • θ.val) * θ.val i) := by
    have hraw : (H rI : sphere (0 : Domain n) 1 → Ambient q) =ᵐ[
        Measure.euclideanHausdorffMeasure (n - 1)] (fun θ => u (c + r • θ.val)) := by
      rw [show H rI = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u (c + r • θ.val)) from hsliceEq]
      exact hslice.coeFn_toLp
    exact hraw.mono fun θ hθ => by
      dsimp only at hθ ⊢
      rw [hθ]
  refine ⟨(hJ rI).1.congr hEq, ?_⟩
  rw [(hJ rI).2, integral_congr_ae hEq]

end StratificationTheory
