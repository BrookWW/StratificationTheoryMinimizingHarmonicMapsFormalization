-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.SphereGradientCharacterization
public import StratificationTheory.Frozen.UnitCylinder
public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic

import StratificationTheory.Providers.AffineAnnularPostcomposition

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff
namespace StratificationTheory

theorem exists_affine_annular_postcomposition {n q k : ℕ} (hn : 2 ≤ n)
    {a b s : ℝ} (hab : a < b) (ha : -1 < a) (hs : 0 < s)
    (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (C : NNReal) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let c : unitCylinder n a b → Ambient q := fun y =>
      (1 - ((e y.val).2 0 - a) / (b - a)) • u ⟨(e y.val).1, y.property.1⟩ +
        (((e y.val).2 0 - a) / (b - a)) • v ⟨(e y.val).1, y.property.1⟩
    let V : OpenDomain n := ⟨{x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)},
      isOpen_Ioo.preimage continuous_norm⟩
    let κ := max (s * (1 + a))⁻¹ s⁻¹
    (∀ᵐ y ∂(Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)),
      ‖fderiv ℝ F (c y)‖ ≤ (C : ℝ)) →
    ∃ W : Domain n → Ambient k, ∃ DW : Domain n → Gradient n k,
      MemW12 V W DW ∧
      (∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
        W ((s * (1 + t)) • θ.val) =
          F ((1 - (t - a) / (b - a)) • u θ + ((t - a) / (b - a)) • v θ)) ∧
      (∫ x in V.val, hsNormSq (DW x)) ≤
        (s * (s * (1 + b)) ^ (n - 1)) * κ ^ 2 * (C : ℝ) ^ 2 *
          (((b - a) / 2) * (∫ θ : sphere (0 : Domain n) 1,
            ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 +
              ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂Measure.euclideanHausdorffMeasure (n - 1)) +
            (b - a)⁻¹ * (∫ θ : sphere (0 : Domain n) 1, ‖v θ - u θ‖ ^ 2
              ∂Measure.euclideanHausdorffMeasure (n - 1))) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.AffineAnnularPostcomposition.result hn hab ha hs u v hu hv F hF L hDF C
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
