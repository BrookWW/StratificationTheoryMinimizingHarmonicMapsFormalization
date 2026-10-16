module

public import StratificationTheory.Foundation.PolarSlices
public import HarmonicMaps.Minimizer
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Almost-everywhere angular transport

Translated polar coordinates and their inverse preserve the actual measures
on the punctured Euclidean domain and sphere-radius product. Fubini transfers
arbitrary a.e. properties, including target membership, to angular slices on
almost every admissible radius. No pointwise map representative is selected.
-/

public section
open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

/-- An actual volume-a.e. property holds angular-a.e. at Lebesgue-almost every
positive radius after translation, without a measurable-predicate assumption. -/
theorem ae_polar_slice_of_ae_volume {n : ℕ} {P : Domain n → Prop}
    (hP : ∀ᵐ x ∂volume, P x) (a : Domain n) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂(volume : Measure (Domain n)).toSphere,
        P (a + r • θ.val) := by
  have hadd : ∀ᵐ x ∂volume, P (a + x) :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.ae hP
  have hsub : ∀ᵐ x : ({(0 : Domain n)}ᶜ : Set (Domain n))
      ∂Measure.comap (Subtype.val : ({(0 : Domain n)}ᶜ : Set (Domain n)) → Domain n) volume,
      P (a + x.val) :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Domain n)).compl).mp
      (hadd.filter_mono (ae_mono Measure.restrict_le_self))
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  have hinv := hm.symm (homeomorphUnitSphereProd (Domain n)).toMeasurableEquiv
  have hpolar : ∀ᵐ p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ)
      ∂(volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1)),
      P (a + p.2.val • p.1.val) := by
    simpa only [Homeomorph.toMeasurableEquiv_symm_coe, homeomorphUnitSphereProd_symm_apply_coe,
      finrank_euclideanSpace, Fintype.card_fin] using hinv.quasiMeasurePreserving.ae hsub
  have hswap : ∀ᵐ p : Ioi (0 : ℝ) × sphere (0 : Domain n) 1
      ∂(Measure.volumeIoiPow (n - 1)).prod (volume : Measure (Domain n)).toSphere,
      P (a + p.1.val • p.2.val) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpolar
  apply (ae_restrict_iff_subtype measurableSet_Ioi).mpr
  exact (ae_volumeIoiPow_iff (n - 1)).mp (Measure.ae_ae_of_ae_prod hswap)

/-- Ball-local a.e. data become the same property on actual angular slices at
almost every radius strictly inside the ball. -/
theorem ae_polar_slice_of_ae_ball {n : ℕ} {P : Domain n → Prop}
    {a : Domain n} {R : ℝ} (hP : ∀ᵐ x ∂volume.restrict (ball a R), P x) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂(volume : Measure (Domain n)).toSphere,
        P (a + r • θ.val) := by
  have hglobal : ∀ᵐ x ∂volume, x ∈ ball a R → P x :=
    (ae_restrict_iff' measurableSet_ball).mp hP
  have hsub : Ioo (0 : ℝ) R ⊆ Ioi (0 : ℝ) := fun _ h => h.1
  have hslices := (ae_polar_slice_of_ae_volume hglobal a).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hslices, ae_restrict_mem measurableSet_Ioo] with r hr hrR
  filter_upwards [hr] with θ hθ
  apply hθ
  rw [mem_ball, dist_eq_norm_sub, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg hrR.1.le]
  have hnorm : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
  simpa only [hnorm, mul_one] using hrR.2

/-- Actual a.e. target-valuedness is preserved on angular slices at almost
every radius of a compactly contained ball. -/
theorem ae_takesValuesIn_polar_slice {n q : ℕ} {Ω : OpenDomain n}
    {N : CompactSmoothEmbeddedTarget q} {u : Domain n → Ambient q}
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ}
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      ∀ᵐ θ : sphere (0 : Domain n) 1 ∂(volume : Measure (Domain n)).toSphere,
        u (a + r • θ.val) ∈ N.carrierSet := by
  apply ae_polar_slice_of_ae_ball (n := n) (a := a) (R := R)
    (P := fun x => u x ∈ N.carrierSet)
  exact hN.filter_mono (ae_mono (Measure.restrict_mono
    (ball_subset_closedBall.trans hball) le_rfl))

end StratificationTheory
