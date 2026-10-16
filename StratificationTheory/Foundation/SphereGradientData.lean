module

public import StratificationTheory.Frozen.SphereSobolev
public import StratificationTheory.Foundation.SphereNeighborhoodCollar
public import StratificationTheory.Foundation.SphereInteriorCutoff
public import StratificationTheory.Foundation.CompactSobolevCutoff
public import StratificationTheory.Foundation.SobolevAngularApproximation
public import StratificationTheory.Foundation.SphereRadialGradientExistence
public import StratificationTheory.Foundation.RadialWeakGradientLocality

/-!
# Actual radial weak-gradient data for sphere Sobolev maps

The literal neighborhood-extension predicate supplies a compact collar and
an interior smooth cutoff. A common smooth angular graph approximation at a
positive-measure family of radii constructs one actual radial weak gradient
on the whole punctured domain. Its angular columns are in native surface L2
and have zero radial contraction at every unit-sphere point.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff BigOperators

namespace StratificationTheory

/-- Every literal sphere Sobolev map has one actual degree-zero extension
and weak gradient on the whole punctured domain, with one angular L2 column
family satisfying the full reciprocal-radius formula and pointwise tangency. -/
theorem exists_sphere_radial_weak_gradient_data {n q : ℕ} (hn : 2 ≤ n)
    {v : sphere (0 : Domain n) 1 → Ambient q} (hv : MemSphereW12 hn v) :
    ∃ w : Domain n → Ambient q, ∃ D : Domain n → Gradient n q,
      ∃ A : sphere (0 : Domain n) 1 → Gradient n q,
        MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D ∧
        (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
          w (ρ.val • θ.val) = v θ) ∧
        (∀ i : Fin n, MemLp (fun θ => A θ i) 2
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1))) ∧
        (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
          D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i) ∧
        ∀ θ : sphere (0 : Domain n) 1, (∑ i : Fin n, θ.val i • A θ i) = 0 := by
  have hnpos : 0 < n := by omega
  obtain ⟨hvL, U, hSphere, _h0, u, Du, hu, huRay⟩ := hv
  have huLoc := hu.to_memW12Loc
  obtain ⟨δ, hδ, hδsmall, hclosed, _hcollar⟩ :=
    exists_memW12_radial_collar hSphere huLoc
  obtain ⟨χ, hχ, hcχ, _hvalues, _hsupport, hsχ, hχOne, hχDeriv⟩ :=
    exists_sphere_interior_cutoff_in_openDomain (n := n) hδ hδsmall U hclosed
  let uχ : Domain n → Ambient q := fun x => χ x • u x
  let Duχ : Domain n → Gradient n q := fun x i =>
    coordinateDerivative χ hχ i x • u x + χ x • Du x i
  have huχ : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) uχ Duχ :=
    huLoc.smoothCutoff_univ hχ hcχ hsχ
  obtain ⟨m, hm, _hmW, κ, _hκ, hae⟩ :=
    exists_smooth_subseq_ae_angular_graph_approximation hnpos huχ.to_memW12Loc
      (a := (0 : Domain n)) (R := 2) (by norm_num) (subset_univ _)
  have hband : Ioo (1 - δ / 2) (1 + δ / 2) ⊆ Ioo (0 : ℝ) 2 := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hbandnonzero : (volume : Measure ℝ) (Ioo (1 - δ / 2) (1 + δ / 2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by linarith : 0 < (1 + δ / 2) - (1 - δ / 2))).ne'
  obtain ⟨σ, hσ, hσData⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hbandnonzero
    (hae.filter_mono (ae_mono (Measure.restrict_mono_set volume hband)))
  obtain ⟨hσuL, hσDL, hσmL, _hσerrI, hσconv, hσDconv⟩ := hσData
  have hσpos : 0 < σ := by linarith [hσ.1]
  have hσnorm (θ : sphere (0 : Domain n) 1) : ‖σ • θ.val‖ = σ := by
    have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    rw [norm_smul, Real.norm_of_nonneg hσpos.le, hθ, mul_one]
  have hσInner (θ : sphere (0 : Domain n) 1) :
      σ • θ.val ∈ {x : Domain n | 1 - δ / 2 < ‖x‖ ∧ ‖x‖ < 1 + δ / 2} := by
    change 1 - δ / 2 < ‖σ • θ.val‖ ∧ ‖σ • θ.val‖ < 1 + δ / 2
    rw [hσnorm]
    exact hσ
  have hσU (θ : sphere (0 : Domain n) 1) : σ • θ.val ∈ U.val := by
    apply hclosed
    change 1 - δ ≤ ‖σ • θ.val‖ ∧ ‖σ • θ.val‖ ≤ 1 + δ
    rw [hσnorm]
    constructor <;> linarith [hσ.1, hσ.2]
  have huχSlice (θ : sphere (0 : Domain n) 1) : uχ (0 + σ • θ.val) = v θ := by
    simp only [zero_add, uχ, hχOne _ (hσInner θ), one_smul]
    exact huRay ⟨σ, hσpos⟩ θ (hσU θ)
  have hDuχSlice (θ : sphere (0 : Domain n) 1) : Duχ (0 + σ • θ.val) = Du (σ • θ.val) := by
    funext i
    simp only [zero_add, Duχ, hχDeriv _ (hσInner θ) i,
      hχOne _ (hσInner θ), zero_smul, one_smul, zero_add]
  obtain ⟨D, hW, hDRay⟩ := exists_radial_weak_gradient_of_smooth_angular_graph_limit
    hnpos (u := uχ) (Du := Duχ) (f := fun k => m (κ k))
    (fun k => hm (κ k)) (0 : Domain n) σ hσuL hσDL
      (fun k => (hσmL (κ k)).1) (fun k i => (hσmL (κ k)).2 i) hσconv hσDconv
  let w : Domain n → Ambient q := fun x => uχ (0 + σ • (‖x‖⁻¹ • x))
  let A : sphere (0 : Domain n) 1 → Gradient n q :=
    fun θ => σ • tangentialColumns θ (Du (σ • θ.val))
  have hwRay (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) :
      w (ρ.val • θ.val) = v θ := by
    change uχ (0 + σ • (‖ρ.val • θ.val‖⁻¹ • (ρ.val • θ.val))) = v θ
    rw [radial_smooth_pullback_ray uχ (0 : Domain n) σ ρ.property θ]
    exact huχSlice θ
  have hDuL (i : Fin n) : MemLp (fun θ : sphere (0 : Domain n) 1 => Du (σ • θ.val) i)
      2 (volume : Measure (Domain n)).toSphere := by
    have heq : (fun θ : sphere (0 : Domain n) 1 => Duχ (0 + σ • θ.val) i) =
        (fun θ => Du (σ • θ.val) i) := by
      funext θ
      rw [hDuχSlice]
    have hL := hσDL i
    rwa [heq] at hL
  have hAL (i : Fin n) : MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere :=
    (memLp_two_tangential_column hDuL i).const_smul σ
  have hD (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n) :
      D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i := by
    rw [hDRay ρ θ i, hDuχSlice]
    simp only [A, Pi.smul_apply, smul_smul, div_eq_mul_inv]
    rw [mul_comm σ ρ.val⁻¹]
  have hvAngular : MemLp v 2 (volume : Measure (Domain n)).toSphere := by
    rwa [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos] at hvL
  have hWLoc : MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D :=
    memW12Loc_punctured_of_radial_collar hnpos hvAngular hAL hwRay hD hW
  refine ⟨w, D, A, hWLoc, hwRay, ?_, hD, ?_⟩
  · intro i
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos]
    exact hAL i
  · intro θ
    simp only [A, Pi.smul_apply]
    simp_rw [smul_comm (θ.val _) σ]
    rw [← Finset.smul_sum, sum_smul_tangentialColumns_eq_zero, smul_zero]

end StratificationTheory
