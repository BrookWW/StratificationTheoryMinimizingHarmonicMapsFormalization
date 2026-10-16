module

public import StratificationTheory.Frozen.CylinderSobolev
public import StratificationTheory.Foundation.CylinderPointCoordinates
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.ContinuousMap.Algebra

import StratificationTheory.Foundation.CylinderRadialAverage
import StratificationTheory.Foundation.CylinderProbabilityWeak
import StratificationTheory.Foundation.CylinderLpWeakLifting

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff Topology
namespace StratificationTheory.Providers.CylinderTraceWellDefined

/-- A full cylinder Sobolev map has one closed-interval continuous native
L2 time representative, determined by its original interior slice classes. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : sphere (0 : Domain n) 1 × Icc a b → unitCylinder n a b := fun p =>
      ⟨e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2.val), unitCylinder_param_mem p.1 p.2⟩
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) := by
  intro e c σ
  obtain ⟨F₀, hF₀, hF₀s, _⟩ :=
    exists_lp_two_time_curve_of_native_cylinder (by omega : 0 < n) a b v hv.1
  obtain ⟨δ, hδ, hδs, U, hU, w, Dw, hW, hP, hWP, hDP, _hWA, _hDA, hraw⟩ :=
    exists_memCylinder_radial_average_data hn hab hv
  let J : Set (Ioi (0 : ℝ)) := {ρ | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
  let η := (Measure.volumeIoiPow (n - 1)).restrict J
  let P := (η univ)⁻¹ • η
  let f0 : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Ambient q := fun p =>
    w (e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2))
  let g0 : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Ambient q := fun p =>
    Dw (e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)) (Fin.natAdd n (0 : Fin 1))
  let f : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p => ∫ ρ, f0 (p, ρ) ∂P
  let g : sphere (0 : Domain n) 1 × ℝ → Ambient q := fun p => ∫ ρ, g0 (p, ρ) ∂P
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  letI : IsProbabilityMeasure P := hP
  have hzero : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ᵐ p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) ∂σ.prod P,
        (∫ t in Ioo a b, deriv φ t • f0 ((p.1, t), p.2) + φ t • g0 ((p.1, t), p.2)) = 0 := by
    intro φ hφ hc hs
    exact MemW12.native_radial_collar_time_test_ae (by omega : 0 < n) U hδ hδs hU hW hφ hc hs
  have havg := probability_average_raw_time_weak_identity a b hWP hDP hzero
  have hmeasure : (volume : Measure ℝ).restrict (Ioo a b) = volume.restrict (Icc a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  have hf : MemLp f 2 (σ.prod (volume.restrict (Icc a b))) := by
    rw [← hmeasure]
    exact havg.1
  have hg : MemLp g 2 (σ.prod (volume.restrict (Icc a b))) := by
    rw [← hmeasure]
    exact havg.2.1
  have hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ᵐ θ ∂σ, (∫ t in Icc a b, deriv φ t • f (θ, t)) = -(∫ t in Icc a b, φ t • g (θ, t)) := by
    intro φ hφ hc hs
    filter_upwards [havg.2.2.2 φ hφ hc hs] with θ hθ
    rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
    have hz := hθ.2.2.2
    rw [integral_add hθ.1 hθ.2.1] at hz
    exact eq_neg_iff_add_eq_zero.mpr hz
  have heq (t : ℝ) (ht : t ∈ Ioo a b) :
      (fun θ => f (θ, t)) = (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) := by
    funext θ
    let y := c (θ, ⟨t, ht.1.le, ht.2.le⟩)
    have hy : (e y.val).2 0 ∈ Ioo a b := by
      simpa only [y, c, e.apply_symm_apply, PiLp.single_apply, ite_true] using ht
    have hr := hraw y hy
    change (∫ ρ : Ioi (0 : ℝ),
      w (e.symm (ρ.val • (e (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t))).1,
        (e (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t))).2)) ∂P) = v y at hr
    rw [e.apply_symm_apply] at hr
    exact hr
  obtain ⟨F, G, _hF, hG, hFs, _hGs, hweak⟩ :=
    exists_native_lp_two_time_curves_with_weak_identity (by omega : 0 < n) a b hf hg hw
  have hF₀I : MemLp F₀ 2 (volume.restrict (Ioo a b)) := by
    rw [hmeasure]
    exact hF₀
  have hGI : MemLp G 2 (volume.restrict (Ioo a b)) := by
    rw [hmeasure]
    exact hG
  have hF₀sI := ae_mono (Measure.restrict_mono_set volume Ioo_subset_Icc_self) hF₀s
  have hFsI := ae_mono (Measure.restrict_mono_set volume Ioo_subset_Icc_self) hFs
  have hsame : F₀ =ᵐ[volume.restrict (Ioo a b)] F := by
    filter_upwards [hF₀sI, hFsI, ae_restrict_mem measurableSet_Ioo] with t h₀t hFt ht
    obtain ⟨h₀L, h₀eq⟩ := h₀t ⟨ht.1.le, ht.2.le⟩
    obtain ⟨hFL, hFeq⟩ := hFt
    have hclasses := h₀L.toLp_congr hFL
      (Eventually.of_forall fun θ => (congrFun (heq t ht) θ).symm)
    exact h₀eq.trans (hclasses.trans hFeq.symm)
  have hweak₀ : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t, deriv φ t • F₀ t) = -(∫ t, φ t • G t) := by
    intro φ hφ hc hs
    have htest : (fun t => deriv φ t • F₀ t) =ᵐ[volume] (fun t => deriv φ t • F t) := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hsame] with t ht
      by_cases hti : t ∈ Ioo a b
      · rw [ht hti]
      · have hz : deriv φ t = 0 := image_eq_zero_of_notMem_tsupport
          (fun hm => hti (hs (tsupport_deriv_subset hm)))
        rw [hz, zero_smul, zero_smul]
    rw [integral_congr_ae htest]
    exact (hweak φ hφ hc hs).2.2
  obtain ⟨H, hH, _hUnique⟩ :=
    banach_interval_weakDerivative_exists_unique_continuous_representative
      hab hF₀I hGI hweak₀
  have hF₀sV := (ae_restrict_iff' measurableSet_Icc).mp hF₀s
  have hHs : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) 2 σ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => v (c (θ, ⟨t, ht.1.le, ht.2.le⟩))) := by
    filter_upwards [hH.1, hF₀sV] with t hHt h₀t ht
    obtain ⟨hLt, h₀eq⟩ := h₀t ⟨ht.1.le, ht.2.le⟩ ⟨ht.1.le, ht.2.le⟩
    exact ⟨hLt, (hHt ht).trans h₀eq⟩
  refine ⟨H, hHs, ?_⟩
  intro K hKs
  have hdiff : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      (K - H) ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ)) := by
    filter_upwards [hKs, hHs] with t hKt hHt ht
    obtain ⟨hKtL, hKtEq⟩ := hKt ht
    obtain ⟨hHtL, hHtEq⟩ := hHt ht
    have hclasses := hKtL.toLp_congr hHtL (Filter.EventuallyEq.rfl)
    change K ⟨t, ht.1.le, ht.2.le⟩ - H ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ))
    rw [mem_singleton_iff, sub_eq_zero]
    exact hKtEq.trans (hclasses.trans hHtEq.symm)
  have hall := continuous_interval_mem_closed_of_ae hab (K - H) isClosed_singleton hdiff
  apply ContinuousMap.ext
  intro t
  exact sub_eq_zero.mp (Set.mem_singleton_iff.mp (hall t))

end StratificationTheory.Providers.CylinderTraceWellDefined
