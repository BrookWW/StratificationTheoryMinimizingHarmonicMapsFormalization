module

public import StratificationTheory.Foundation.SpatialConeTimeDifferential
public import StratificationTheory.Foundation.SmoothDomainPullbackEnergy
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Actual spatial cone-time Sobolev transport

One fixed smooth spatial chart and its native Jacobian produce the weak pair,
energy bound and original value constraints. The interpolation time is
unchanged. The carrier is restricted to a bounded Euclidean region with
positive spatial height; all constants precede the source map and interval.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ContDiff ENNReal BigOperators
namespace StratificationTheory

private theorem positive_band_nat_power_lintegral_ne_top (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ r in Ioo ρ 2, ENNReal.ofReal (r ^ n)) ≠ ⊤ := by
  have hIcc : Integrable (fun r : ℝ => r ^ n) (volume.restrict (Icc ρ 2)) :=
    (continuous_id.pow n).continuousOn.integrableOn_compact isCompact_Icc
  have hI : Integrable (fun r : ℝ => r ^ n) (volume.restrict (Ioo ρ 2)) :=
    Integrable.mono_measure hIcc (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  have hnonneg : ∀ᵐ r ∂volume.restrict (Ioo ρ 2), 0 ≤ r ^ n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact pow_nonneg (hρ.trans hr.1).le n
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnonneg]
  exact ENNReal.ofReal_ne_top

/-- The same explicit spatial cone-time chart constructs a full weak pair,
native energy bound and arbitrary original a.e. values on its entire bounded
positive-height preimage. The geometric constants are independent of the
interpolation interval, target dimension and original Sobolev data. -/
theorem exists_spatial_cone_time_sobolev_transport (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm ((T y)⁻¹ • (e ((E y).1)).1, (E y).2)
    let c : ℝ≥0∞ := ∫⁻ r in Ioo ρ 2, ENNReal.ofReal (r ^ n)
    c ≠ ⊤ ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ (B : OpenDomain n) (a b : ℝ),
      let Ω : OpenDomain (n + 1) :=
        ⟨{z | (e z).1 ∈ B.val ∧ (e z).2 0 ∈ Ioo a b},
          (B.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      ∃ U : OpenDomain (n + 1 + 1),
        U.val = ((T ⁻¹' Ioo ρ 2) ∩ F ⁻¹' Ω.val) ∩ ball 0 R ∧
        ∀ (q : ℕ) (w : Domain (n + 1) → Ambient q)
          (Dw : Domain (n + 1) → Gradient (n + 1) q), MemW12 Ω w Dw →
          let W := w ∘ F
          let D : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y i =>
            ∑ j : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single i 1)) j • Dw (F y) j
          MemW12 U W D ∧
            dirichletEnergy D U.val ≤
              ENNReal.ofReal (((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * L ^ 2) *
                c * dirichletEnergy Dw Ω.val ∧
            ∀ P : Ambient q → Prop, (∀ᵐ z ∂volume.restrict Ω.val, P (w z)) →
              ∀ᵐ y ∂volume.restrict U.val, P (W y) := by
  intro e E T F c
  have hc : c ≠ ⊤ := positive_band_nat_power_lintegral_ne_top n hρ
  obtain ⟨L, hL, hDF⟩ := exists_spatial_cone_time_differential_bound n hρ R
  refine ⟨hc, L, hL, ?_⟩
  intro B a b Ω
  have hT : Continuous T :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp (e.continuous.comp (continuous_fst.comp E.continuous)))
  have hpos : T ⁻¹' Ioo ρ 2 ⊆ {y | 0 < T y} := fun _ hy => hρ.trans hy.1
  have hF : ContDiffOn ℝ ∞ F (T ⁻¹' Ioo ρ 2) :=
    (contDiffOn_spatial_cone_time_coordinates n).mono hpos
  let V : Set (Domain (n + 1 + 1)) := (T ⁻¹' Ioo ρ 2) ∩ F ⁻¹' Ω.val
  have hV : IsOpen V :=
    hF.continuousOn.isOpen_inter_preimage (isOpen_Ioo.preimage hT) Ω.property
  let U : OpenDomain (n + 1 + 1) := ⟨V ∩ ball 0 R, hV.inter isOpen_ball⟩
  refine ⟨U, rfl, ?_⟩
  have hFU : MapsTo F U.val Ω.val := fun _ hy => hy.1.2
  have hDFU (y : Domain (n + 1 + 1)) (hy : y ∈ U.val) : ‖fderiv ℝ F y‖ ≤ L :=
    hDF y (mem_ball_zero_iff.mp hy.2).le hy.1.1.1.le
  let eξ : Domain (n + 1) → Domain n := fun z => ((e z).2 0)⁻¹ • (e z).1
  let C := {z : Domain (n + 1) | (e z).2 0 ∈ Ioo ρ 2 ∧ eξ z ∈ B.val}
  let A := {y : Domain (n + 1 + 1) | (E y).1 ∈ C ∧ (E y).2 0 ∈ Ioo a b}
  have hUA : U.val ⊆ A := by
    intro y hy
    have hΩ := hy.1.2
    change (e (F y)).1 ∈ B.val ∧ (e (F y)).2 0 ∈ Ioo a b at hΩ
    dsimp only [F] at hΩ
    rw [e.apply_symm_apply] at hΩ
    exact ⟨⟨hy.1.1, hΩ.1⟩, hΩ.2⟩
  have hFm : Measurable F := by
    apply e.symm.continuous.measurable.comp
    exact (hT.measurable.inv.smul
      (measurable_fst.comp (e.continuous.measurable.comp
        (measurable_fst.comp E.continuous.measurable)))).prodMk
      (measurable_snd.comp E.continuous.measurable)
  have hfull : Measure.map F (volume.restrict A) = c • volume.restrict Ω.val :=
    map_euclidean_spatial_cone_time B.property.measurableSet measurableSet_Ioo
      measurableSet_Ioo (fun _ hr => hρ.trans hr.1)
  have hmap : Measure.map F (volume.restrict U.val) ≤ c • volume.restrict Ω.val :=
    (Measure.map_mono (Measure.restrict_mono_set volume hUA) hFm).trans_eq hfull
  intro q w Dw hw W D
  obtain ⟨hW, _hpoint, henergy, hP⟩ := memW12_smooth_open_domain_pullback_energy hw U F
    (hF.mono (fun _ hy => hy.1.1)) hFU L hDFU c hc hmap
  exact ⟨hW, henergy, hP⟩

end StratificationTheory
