module

public import StratificationTheory.Foundation.PolarSlices
public import HarmonicMaps.EnergyLemmas
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Actual Sobolev energy and separation slices

Local Sobolev membership supplies the L1 inputs on a compactly contained
ball. Polar Fubini then gives one common full-measure radial set for the map,
every displayed gradient column and the Hilbert--Schmidt energy. For two
maps the same construction includes their actual squared L2 separation.
These statements provide integral slice data without asserting sphere weak
Sobolev derivatives or endpoint traces.
-/

public section
open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

/-- The actual map has an integrable squared norm on almost every angular slice. -/
theorem ae_integrable_polar_sobolev_map {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ}
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun θ : sphere (0 : Domain n) 1 => ‖u (a + r • θ.val)‖ ^ 2)
        (volume : Measure (Domain n)).toSphere := by
  have hmapClosed : IntegrableOn (fun x : Domain n => ‖u x‖ ^ 2) (closedBall a R) :=
    (hu.2.1 (closedBall a R) (isCompact_closedBall a R) hball).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  have hmap : IntegrableOn (fun x : Domain n => ‖u x‖ ^ 2) (ball a R) volume :=
    hmapClosed.mono_set ball_subset_closedBall
  exact ae_integrable_polar_slice_ball (n := n) (f := fun x : Domain n => ‖u x‖ ^ 2)
    (a := a) (R := R) hmap

/-- A displayed weak-gradient column has an integrable squared norm on almost
every angular slice. -/
theorem ae_integrable_polar_sobolev_column {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ}
    (hball : closedBall a R ⊆ Ω.val) (i : Fin n) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun θ : sphere (0 : Domain n) 1 => ‖Du (a + r • θ.val) i‖ ^ 2)
        (volume : Measure (Domain n)).toSphere := by
  have hcolClosed : IntegrableOn (fun x : Domain n => ‖Du x i‖ ^ 2) (closedBall a R) :=
    (hu.2.2 i (closedBall a R) (isCompact_closedBall a R) hball).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  have hcol : IntegrableOn (fun x : Domain n => ‖Du x i‖ ^ 2) (ball a R) volume :=
    hcolClosed.mono_set ball_subset_closedBall
  exact ae_integrable_polar_slice_ball (n := n) (f := fun x : Domain n => ‖Du x i‖ ^ 2)
    (a := a) (R := R) hcol

/-- Actual Hilbert--Schmidt energy is integrable on almost every angular slice. -/
theorem ae_integrable_polar_sobolev_energy {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ}
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Du (a + r • θ.val)))
        (volume : Measure (Domain n)).toSphere := by
  have henergy : IntegrableOn (fun x : Domain n => hsNormSq (Du x)) (ball a R) volume :=
    hu.integrable_hsNormSq_ball hball
  exact ae_integrable_polar_slice_ball (n := n) (f := fun x : Domain n => hsNormSq (Du x))
    (a := a) (R := R) henergy

/-- The squared separation of two actual locally Sobolev maps is integrable on
almost every angular slice. -/
theorem ae_integrable_polar_sobolev_separation {n q : ℕ}
    {Ω : OpenDomain n} {u v : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    {a : Domain n} {R : ℝ} (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun θ : sphere (0 : Domain n) 1 =>
        ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2)
        (volume : Measure (Domain n)).toSphere := by
  have hdiffClosed : IntegrableOn (fun x : Domain n => ‖u x - v x‖ ^ 2) (closedBall a R) :=
    ((hu.2.1 (closedBall a R) (isCompact_closedBall a R) hball).sub
      (hv.2.1 (closedBall a R) (isCompact_closedBall a R) hball)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  have hdiff : IntegrableOn (fun x : Domain n => ‖u x - v x‖ ^ 2) (ball a R) volume :=
    hdiffClosed.mono_set ball_subset_closedBall
  exact ae_integrable_polar_slice_ball (n := n) (f := fun x : Domain n => ‖u x - v x‖ ^ 2)
    (a := a) (R := R) hdiff

/-- The map, all displayed columns and their actual HS energy have integrable
angular squares at one common almost-everywhere set of admissible radii. -/
theorem ae_integrable_polar_sobolev_data {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ}
    (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun θ : sphere (0 : Domain n) 1 => ‖u (a + r • θ.val)‖ ^ 2)
        (volume : Measure (Domain n)).toSphere ∧
      (∀ i : Fin n, Integrable
        (fun θ : sphere (0 : Domain n) 1 => ‖Du (a + r • θ.val) i‖ ^ 2)
        (volume : Measure (Domain n)).toSphere) ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Du (a + r • θ.val)))
        (volume : Measure (Domain n)).toSphere := by
  have hcols : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), ∀ i : Fin n,
      Integrable (fun θ : sphere (0 : Domain n) 1 => ‖Du (a + r • θ.val) i‖ ^ 2)
        (volume : Measure (Domain n)).toSphere :=
    ae_all_iff.mpr fun i => ae_integrable_polar_sobolev_column hu hball i
  filter_upwards [ae_integrable_polar_sobolev_map hu hball, hcols,
    ae_integrable_polar_sobolev_energy hu hball] with r hm hc he
  exact ⟨hm, hc, he⟩

/-- Two actual locally Sobolev maps have their energy and squared separation
integrable on the same almost-everywhere family of angular slices. -/
theorem ae_integrable_polar_sobolev_pair {n q : ℕ}
    {Ω : OpenDomain n} {u v : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    {a : Domain n} {R : ℝ} (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Du (a + r • θ.val)))
        (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Dv (a + r • θ.val)))
        (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 =>
        ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2)
        (volume : Measure (Domain n)).toSphere := by
  filter_upwards [ae_integrable_polar_sobolev_energy hu hball,
    ae_integrable_polar_sobolev_energy hv hball,
    ae_integrable_polar_sobolev_separation hu hv hball] with r huSlice hvSlice hdiffSlice
  exact ⟨huSlice, hvSlice, hdiffSlice⟩

end StratificationTheory
