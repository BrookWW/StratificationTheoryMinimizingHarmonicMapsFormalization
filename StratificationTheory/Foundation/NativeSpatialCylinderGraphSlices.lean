module

public import StratificationTheory.Foundation.NativeSpatialCylinderGoodRadius
public import StratificationTheory.Foundation.CoordinateSliceConvergence
public import HarmonicMaps.Analysis.SobolevSmoothDensity

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff
namespace StratificationTheory

/-- A genuine original Sobolev ball produces one smooth graph sequence
whose native spatial cylinder slices converge at almost every common radius.
The independent physical time variable is retained in every slice. -/
theorem exists_native_spatial_cylinder_graph_approximation {n q : ℕ}
    (hn : 0 < n) {s R a b : ℝ} (hs : 0 < s) (hsR : s < R)
    {center : Domain (n + 1)} {B : ℝ} (hB : 0 < B)
    (W : Domain (n + 1) → Ambient q) (DW : Domain (n + 1) → Gradient (n + 1) q)
    (hW : MemW12 (ballDomain center B) W DW) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := {y : Domain (n + 1) |
      (s < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    let F := fun (r : ℝ) (c : unitCylinder n a b) =>
      e.symm (r • (e c.val).1, (e c.val).2)
    Ω ⊆ ball center B →
    ∃ f : ℕ → Domain (n + 1) → Ambient q, ∃ hf : ∀ k, ContDiff ℝ ∞ (f k),
      ∀ᵐ r ∂volume.restrict (Ioo s R),
        (∀ k, MemLp (fun c => f k (F r c)) 2 μ) ∧
        MemLp (fun c => W (F r c)) 2 μ ∧
        (∀ i : Fin (n + 1),
          (∀ k, MemLp (fun c => coordinateDerivative (f k) (hf k) i (F r c)) 2 μ) ∧
          MemLp (fun c => DW (F r c) i) 2 μ) ∧
        Tendsto (fun k => eLpNorm (fun c => f k (F r c) - W (F r c)) 2 μ)
          atTop (𝓝 0) ∧
        ∀ i : Fin (n + 1), Tendsto (fun k => eLpNorm
          (fun c => coordinateDerivative (f k) (hf k) i (F r c) - DW (F r c) i) 2 μ)
          atTop (𝓝 0) := by
  classical
  intro e Ω μ F hΩ
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν := (volume : Measure ℝ).comap (Subtype.val : Icc a b → ℝ)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : SigmaFinite ν :=
    (measurePreserving_subtype_coe (measurableSet_Icc (a := a) (b := b))
      (μa := (volume : Measure ℝ))).sigmaFinite
  have hνmass : ν univ = (volume : Measure ℝ) (Icc a b) := by
    simpa only [preimage_univ, Measure.restrict_apply_univ] using
      (measurePreserving_subtype_coe (measurableSet_Icc (a := a) (b := b))
        (μa := (volume : Measure ℝ))).measure_preimage MeasurableSet.univ.nullMeasurableSet
  letI : IsFiniteMeasure ν := ⟨by rw [hνmass]; exact isCompact_Icc.measure_lt_top⟩
  have hμmass : (σ.prod ν) univ = μ univ := by
    simpa only [preimage_univ] using
      (unitCylinder_param_measurePreserving hn a b).2.measure_preimage
        MeasurableSet.univ.nullMeasurableSet
  letI : IsFiniteMeasure μ := ⟨by rw [← hμmass]; exact measure_lt_top (σ.prod ν) univ⟩
  let η := (Measure.volumeIoiPow (n - 1)).restrict
    {ρ : Ioi (0 : ℝ) | s < ρ.val ∧ ρ.val < R}
  have hη := native_spatial_radius_band_mass (n := n) hs hsR
  letI : IsFiniteMeasure η := ⟨hη.2.lt_top⟩
  have hm := (measurePreserving_native_cylinder_radial_inverse hn hs R a b).comp
    (Measure.measurePreserving_swap (μ := η) (ν := μ))
  have hMono : volume.restrict Ω ≤ volume.restrict (ball center B) :=
    Measure.restrict_mono_set volume hΩ
  obtain ⟨f, hf, hfW, hfConv, hfDConv⟩ := hW.smoothDensity_memW12_ball hB
  let A : Option (Fin (n + 1)) → ℕ → Domain (n + 1) → Ambient q := fun i k =>
    match i with
    | none => f k
    | some j => coordinateDerivative (f k) (hf k) j
  let U : Option (Fin (n + 1)) → Domain (n + 1) → Ambient q := fun i =>
    match i with
    | none => W
    | some j => fun y => DW y j
  have hA (i : Option (Fin (n + 1))) (k : ℕ) : MemLp (A i k) 2
      (volume.restrict (ball center B)) := by
    cases i with
    | none => exact (hfW k).2.1
    | some j => exact (hfW k).2.2 j
  have hU (i : Option (Fin (n + 1))) : MemLp (U i) 2
      (volume.restrict (ball center B)) := by
    cases i with
    | none => exact hW.2.1
    | some j => exact hW.2.2 j
  have hConv (i : Option (Fin (n + 1))) : Tendsto
      (fun k => eLpNorm (A i k - U i) 2 (volume.restrict (ball center B))) atTop (𝓝 0) := by
    cases i with
    | none => exact hfConv
    | some j => exact hfDConv j
  let G : Ioi (0 : ℝ) × unitCylinder n a b → Domain (n + 1) := fun p => F p.1.val p.2
  let AP := fun i k p => A i k (G p)
  let UP := fun i p => U i (G p)
  have hAP (i : Option (Fin (n + 1))) (k : ℕ) : MemLp (AP i k) 2 (η.prod μ) :=
    ((hA i k).mono_measure hMono).comp_measurePreserving hm
  have hUP (i : Option (Fin (n + 1))) : MemLp (UP i) 2 (η.prod μ) :=
    ((hU i).mono_measure hMono).comp_measurePreserving hm
  have hPConv (i : Option (Fin (n + 1))) : Tendsto
      (fun k => eLpNorm (AP i k - UP i) 2 (η.prod μ)) atTop (𝓝 0) := by
    have hEq (k : ℕ) : eLpNorm (AP i k - UP i) 2 (η.prod μ) =
        eLpNorm (A i k - U i) 2 (volume.restrict Ω) :=
      eLpNorm_comp_measurePreserving (((hA i k).sub (hU i)).mono_measure hMono).aestronglyMeasurable hm
    simp_rw [hEq]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hConv i)
      (fun _ => zero_le) (fun k => eLpNorm_mono_measure _ hMono)
  obtain ⟨κ, _hκ, hκ⟩ := exists_subseq_ae_tendsto_prod_l2_family hAP hUP hPConv
  refine ⟨fun k => f (κ k), fun k => hf (κ k), ?_⟩
  apply (ae_positive_radius_band_iff (n := n) hs _).mp
  filter_upwards [hκ] with ρ hρ
  exact ⟨(fun k => (hρ none).1 (κ k)), (hρ none).2.1,
    fun i => ⟨(fun k => (hρ (some i)).1 (κ k)), (hρ (some i)).2.1⟩,
    (hρ none).2.2, fun i => (hρ (some i)).2.2⟩

end StratificationTheory
