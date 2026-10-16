module

public import StratificationTheory.Foundation.NormalizedEnergyOrder
public import HarmonicMaps.Analysis.BallEnergyAbsoluteContinuity

public section

open HarmonicMaps MeasureTheory Set
open scoped Topology

namespace HarmonicMaps

/-- Local Sobolev integrability and the genuine upstream ball-integral
absolute continuity make finite real Dirichlet energy continuous through both
endpoints of a compactly contained radius interval. -/
theorem MemW12Loc.continuousOn_dirichletEnergy_toReal_ball_radii {n q : ℕ}
    (hn : 0 < n) {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ} (hR : 0 ≤ R) (hball : Metric.closedBall a R ⊆ Ω.val) :
    ContinuousOn (fun r : ℝ => (dirichletEnergy Du (Metric.ball a r)).toReal) (Icc 0 R) := by
  have hAC := absolutelyContinuousOnInterval_integral_ball hn hR (hu.integrable_hsNormSq_ball hball)
  have hc : ContinuousOn (fun r : ℝ => ∫ x in Metric.ball a r, hsNormSq (Du x)) (Icc 0 R) := by
    simpa only [uIcc_of_le hR] using hAC.continuousOn
  apply hc.congr
  intro r hr
  exact dirichletEnergy_toReal (hu.integrable_hsNormSq_ball
    ((Metric.closedBall_subset_closedBall hr.2).trans hball))

/-- Finite real Dirichlet energy is continuous at every interior admissible
radius, for the actual displayed Sobolev gradient. -/
theorem MemW12Loc.continuousAt_dirichletEnergy_toReal_ball_radius {n q : ℕ}
    (hn : 0 < n) {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) :
    ContinuousAt (fun s : ℝ => (dirichletEnergy Du (Metric.ball a s)).toReal) r :=
  (hu.continuousOn_dirichletEnergy_toReal_ball_radii hn (hr.trans hrR).le hball).continuousAt
    (Icc_mem_nhds hr hrR)

/-- On positive radii strictly below an admissible outer radius, the exact
finite real normalized energy is continuous. -/
theorem MemW12Loc.continuousAt_normalizedEnergy_toReal_radius {n q : ℕ}
    (hn : 0 < n) {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ} (hball : Metric.closedBall a R ⊆ Ω.val)
    (r : PositiveRadius) (hrR : r.val < R) :
    ContinuousAt (fun s : PositiveRadius => (normalizedEnergy Du a s).toReal) r := by
  have he : ContinuousAt (fun s : PositiveRadius =>
      (dirichletEnergy Du (Metric.ball a s.val)).toReal) r :=
    (hu.continuousAt_dirichletEnergy_toReal_ball_radius hn r.property hrR hball).comp continuousAt_subtype_val
  have hp : ContinuousAt (fun s : PositiveRadius => s.val ^ (2 - (n : ℤ))) r :=
    continuousAt_subtype_val.zpow₀ _ (Or.inl r.property.ne')
  have hformula : (fun s : PositiveRadius => (normalizedEnergy Du a s).toReal) =
      (fun s : PositiveRadius => s.val ^ (2 - (n : ℤ)) *
        (dirichletEnergy Du (Metric.ball a s.val)).toReal) := by
    funext s
    unfold normalizedEnergy
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (zpow_pos s.property _))]
  rw [hformula]
  exact hp.mul he

/-- The normalized energy is continuous on the whole open admissible positive
radius range. -/
theorem MemW12Loc.continuousOn_normalizedEnergy_toReal_radii {n q : ℕ}
    (hn : 0 < n) {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ} (hball : Metric.closedBall a R ⊆ Ω.val) :
    ContinuousOn (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal)
      {r | r.val < R} := by
  intro r hr
  exact (hu.continuousAt_normalizedEnergy_toReal_radius hn hball r hr).continuousWithinAt

end HarmonicMaps
