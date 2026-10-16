module

public import StratificationTheory.Frozen.SphereSobolev
public import StratificationTheory.Frozen.SphereTargetValues
public import HarmonicMaps.Minimizer

import StratificationTheory.Foundation.SobolevAngularApproximation
import StratificationTheory.Foundation.SphereSobolevSliceClosure
import StratificationTheory.Foundation.PolarAETransport

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology

namespace StratificationTheory.Providers.SphereSlices

/-- Actual locally Sobolev maps with a.e. target values give sphere-Sobolev
and target-valued slices on one radial full-measure set inside each contained ball. -/
theorem result {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    {a : Domain n} {R : ℝ} (hR : 0 < R) (hball : closedBall a R ⊆ Ω.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) ∧
      TakesSphereValuesIn hn N (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val)) := by
  have hnpos : 0 < n := by omega
  obtain ⟨m, hm, _hmW, κ, _hκ, hae⟩ :=
    exists_smooth_subseq_ae_angular_graph_approximation (n := n) (q := q)
      (Ω := Ω) (u := u) (Du := Du) (a := a) (R := R) hnpos hu hR hball
  have htarget := ae_takesValuesIn_polar_slice (n := n) (q := q) (Ω := Ω)
    (N := N) (u := u) (a := a) (R := R) hN hball
  filter_upwards [hae, htarget] with r hr ht
  refine ⟨?_, ?_⟩
  · have hmk (k : ℕ) :
        MemLp (fun θ : sphere (0 : Domain n) 1 => m (κ k) (a + r • θ.val))
          2 (volume : Measure (Domain n)).toSphere := (hr.2.2.1 (κ k)).1
    have hDmk (k : ℕ) (i : Fin n) :
        MemLp (fun θ : sphere (0 : Domain n) 1 =>
          coordinateDerivative (m (κ k)) (hm (κ k)) i (a + r • θ.val))
            2 (volume : Measure (Domain n)).toSphere := (hr.2.2.1 (κ k)).2 i
    exact @memSphereW12_of_smooth_angular_graph_limit n q hn u Du
      (fun k => m (κ k)) (fun (k : ℕ) => hm (κ k)) a r
      hr.1 hr.2.1 hmk hDmk hr.2.2.2.2.1 hr.2.2.2.2.2
  · unfold TakesSphereValuesIn
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos]
    exact ht

end StratificationTheory.Providers.SphereSlices
