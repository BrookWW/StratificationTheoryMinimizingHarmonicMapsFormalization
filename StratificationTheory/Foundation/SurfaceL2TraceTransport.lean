module

public import StratificationTheory.Foundation.CoordinateClosedTargetCubeSurface
public import StratificationTheory.Foundation.RadialTraceCompatibility
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Continuous L2 traces under native surface coordinates

A fixed homeomorphism whose pushforward measure is dominated by a finite
multiple preserves original L2 convergence and continuous L2 curves. The
radial cube coordinates therefore transport complete closed-interval trace
curves, including their endpoint classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace StratificationTheory

/-- A finite native measure bound controls the original pulled-back L2
seminorm, without selecting new representatives. -/
theorem homeomorph_eLpNorm_two_comp_le
    {X Y E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup E] (H : X ≃ₜ Y) {μ : Measure X} {ν : Measure Y}
    {c : ℝ≥0∞} (hmap : Measure.map H μ ≤ c • ν) (f : Y → E) :
    eLpNorm (f ∘ H) 2 μ ≤ c ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 ν := by
  rw [← H.measurableEmbedding.eLpNorm_map_measure]
  exact eLpNorm_le_of_measure_le_smul hmap

/-- The original L2 convergence transfers through fixed dominated surface
coordinates. The finite distortion is independent of the varying slices. -/
theorem homeomorph_tendsto_eLpNorm_two_comp_zero
    {ι X Y E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup E] (H : X ≃ₜ Y) {μ : Measure X} {ν : Measure Y}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hmap : Measure.map H μ ≤ c • ν)
    {l : Filter ι} {f : ι → Y → E}
    (hf : Tendsto (fun i => eLpNorm (f i) 2 ν) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm ((f i) ∘ H) 2 μ) l (𝓝 0) := by
  have hfinite : c ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc
  have hlim := ENNReal.Tendsto.const_mul hf (Or.inr hfinite)
  rw [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun i => homeomorph_eLpNorm_two_comp_le H hmap (f i))

/-- A complete continuous L2 curve transports through a fixed native surface
homeomorphism. Every time, including the endpoints, has its original
pulled-back class; no raw endpoint value is substituted for a trace. -/
theorem exists_continuous_L2_curve_homeomorph_pullback
    {T X Y E : Type*} [TopologicalSpace T]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup E] (H : X ≃ₜ Y) {μ : Measure X} {ν : Measure Y}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hmap : Measure.map H μ ≤ c • ν)
    (G : C(T, Lp E 2 ν)) :
    ∃ K : C(T, Lp E 2 μ),
      (∀ t, ∃ ht : MemLp (fun x => G t (H x)) 2 μ,
        K t = ht.toLp (fun x => G t (H x))) ∧
      (∀ t (f : Y → E) (hf : MemLp f 2 ν), G t = hf.toLp f →
        ∃ ht : MemLp (f ∘ H) 2 μ, K t = ht.toLp (f ∘ H)) ∧
      ∀ L : C(T, Lp E 2 μ),
        (∀ t, ∃ ht : MemLp (fun x => G t (H x)) 2 μ,
          L t = ht.toLp (fun x => G t (H x))) → L = K := by
  have hQ : Measure.QuasiMeasurePreserving H μ ν :=
    ⟨H.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hmap⟩
  have hmem (t : T) : MemLp (fun x => G t (H x)) 2 μ :=
    ((Lp.memLp (G t)).of_measure_le_smul hc hmap).comp_of_map
      H.continuous.measurable.aemeasurable
  let Kfun : T → Lp E 2 μ := fun t => (hmem t).toLp (fun x => G t (H x))
  have hcont : Continuous Kfun := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun s : T => fun x => G s (H x)) hmem
      (fun x => G t (H x)) (hmem t)).mpr
    have hlim : Tendsto (fun s : T => eLpNorm (fun y => G s y - G t y) 2 ν)
        (𝓝 t) (𝓝 0) := by
      exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
        (fun s : T => G s) (G t)).mp (G.continuous.tendsto t)
    exact homeomorph_tendsto_eLpNorm_two_comp_zero H (μ := μ) (ν := ν)
      hc hmap (f := fun s : T => fun y => G s y - G t y) hlim
  let K : C(T, Lp E 2 μ) := ⟨Kfun, hcont⟩
  refine ⟨K, fun t => ⟨hmem t, rfl⟩, ?_, ?_⟩
  · intro t f hf hG
    have hraw : (fun x => G t (H x)) =ᵐ[μ] f ∘ H := by
      have hfg : (G t : Y → E) =ᵐ[ν] f := by
        rw [hG]
        exact hf.coeFn_toLp
      exact hQ.ae hfg
    have hL : MemLp (f ∘ H) 2 μ := (hmem t).ae_eq hraw
    exact ⟨hL, (hmem t).toLp_congr hL hraw⟩
  · intro L hL
    apply ContinuousMap.ext
    intro t
    obtain ⟨ht, heq⟩ := hL t
    exact heq

/-- Normalization by almost every original interior slice determines the
transported curve uniquely on the whole closed interval. In particular its
endpoint classes are the pullbacks of the source trace classes. -/
theorem existsUnique_continuous_L2_raw_trace_homeomorph_pullback
    {X Y E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup E] (H : X ≃ₜ Y) {μ : Measure X} {ν : Measure Y}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hmap : Measure.map H μ ≤ c • ν)
    {a b : ℝ} (hab : a < b) (w : Y × ℝ → E)
    (G : C(Icc a b, Lp E 2 ν))
    (hG : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun y => w (y, t)) 2 ν,
        G ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun y => w (y, t))) :
    ∃! K : C(Icc a b, Lp E 2 μ),
      (∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun x => w (H x, t)) 2 μ,
          K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => w (H x, t))) ∧
      ∀ t (f : Y → E) (hf : MemLp f 2 ν), G t = hf.toLp f →
        ∃ ht : MemLp (f ∘ H) 2 μ, K t = ht.toLp (f ∘ H) := by
  obtain ⟨K, _hK, hraw, _huniq⟩ :=
    exists_continuous_L2_curve_homeomorph_pullback H hc hmap G
  have hnorm : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun x => w (H x, t)) 2 μ,
        K ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun x => w (H x, t)) := by
    filter_upwards [hG] with t hGt ht
    obtain ⟨hL, hEq⟩ := hGt ht
    exact hraw ⟨t, ht.1.le, ht.2.le⟩ (fun y => w (y, t)) hL hEq
  refine ⟨K, ⟨hnorm, hraw⟩, ?_⟩
  intro L hL
  exact continuous_Lp_representatives_eq_of_ae_slices
    (f := fun p : X × ℝ => w (H p.1, p.2))
    (g := fun p : X × ℝ => w (H p.1, p.2)) hab L K hL.1 hnorm
    (Eventually.of_forall fun _ _ => EventuallyEq.rfl)

/-- The actual cube-boundary radial homeomorphism transports every complete
continuous native L2 curve to the sphere. Its distortion is uniform on the
source radius interval and it preserves every original slice class. -/
theorem exists_cube_radial_continuous_L2_trace_transport {n : ℕ} {r : ℝ}
    (hrlo : (1 : ℝ) / 8 ≤ r) (hrhi : r ≤ (1 : ℝ) / 4)
    {T E : Type*} [TopologicalSpace T] [NormedAddCommGroup E]
    (G : C(T, Lp E 2 (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure {x : Domain n // ‖WithLp.ofLp x‖ = r}))) :
    ∃ H : sphere (0 : Domain n) 1 ≃ₜ {x : Domain n // ‖WithLp.ofLp x‖ = r},
      (∀ θ, (H θ).val = (r / ‖WithLp.ofLp θ.val‖) • θ.val) ∧
      (∀ x, (H.symm x).val = NormedSpace.normalize x.val) ∧
      ∃ K : C(T, Lp E 2 (Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1))),
        (∀ t (f : {x : Domain n // ‖WithLp.ofLp x‖ = r} → E)
          (hf : MemLp f 2 (Measure.euclideanHausdorffMeasure (n - 1))),
          G t = hf.toLp f →
          ∃ ht : MemLp (f ∘ H) 2 (Measure.euclideanHausdorffMeasure (n - 1)),
            K t = ht.toLp (f ∘ H)) ∧
        ∀ t, eLpNorm (fun θ => G t (H θ)) 2
            (Measure.euclideanHausdorffMeasure (n - 1) :
              Measure (sphere (0 : Domain n) 1)) ≤
          ((16 : ℝ≥0∞) ^ (n - 1)) ^ (1 / (2 : ℝ≥0∞)).toReal *
            eLpNorm (G t) 2 (Measure.euclideanHausdorffMeasure (n - 1) :
              Measure {x : Domain n // ‖WithLp.ofLp x‖ = r}) := by
  obtain ⟨H, hH, hHi, hmap, _hback, _hQ, _hQi⟩ :=
    exists_cube_radial_homeomorph_surface_transport (n := n) hrlo hrhi
  obtain ⟨K, _hK, hraw, _huniq⟩ := exists_continuous_L2_curve_homeomorph_pullback H
    (ENNReal.pow_ne_top (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)) hmap G
  exact ⟨H, hH, hHi, K, hraw,
    fun t => homeomorph_eLpNorm_two_comp_le H hmap (G t)⟩

end StratificationTheory
