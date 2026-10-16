module

public import StratificationTheory.Foundation.MonotoneLimitAtZero
public import HarmonicMaps.EnergyLemmas
public import HarmonicMaps.Analysis.SobolevAECongruence

public section

open MeasureTheory Filter Set
open scoped Topology

namespace HarmonicMaps

/-- Almost-everywhere equality of maps with weak gradients preserves their actual
extended normalized energies on every ball inside the common open domain. -/
theorem HasWeakGradient.normalizedEnergy_eq_of_ae_eq_map {n q : ℕ}
    {Ω : OpenDomain n} {u v : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) (hv : HasWeakGradient Ω v Dv)
    (huv : u =ᵐ[volume.restrict Ω.val] v) (a : Domain n) (r : PositiveRadius)
    (hball : Metric.ball a r.val ⊆ Ω.val) :
    normalizedEnergy Du a r = normalizedEnergy Dv a r := by
  unfold normalizedEnergy
  rw [dirichletEnergy_congr_ae
    (ae_restrict_of_ae_restrict_of_subset hball (hu.ae_eq_of_ae_eq_map hv huv))]

/-- The one-sided finite normalized-energy limit depends on the weak Sobolev
map class, rather than on its ambient representative or gradient choices. -/
theorem MemW12Loc.normalizedEnergy_tendsto_iff_of_ae_eq_map {n q : ℕ}
    {Ω : OpenDomain n} {u v : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    (huv : u =ᵐ[volume.restrict Ω.val] v) (a : Domain n) (ha : a ∈ Ω.val)
    (θ : ℝ) :
    Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal) atBot (𝓝 θ) ↔
      Tendsto (fun r : PositiveRadius => (normalizedEnergy Dv a r).toReal) atBot (𝓝 θ) := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds ha)
  have heq : (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal) =ᶠ[atBot]
      (fun r : PositiveRadius => (normalizedEnergy Dv a r).toReal) := by
    filter_upwards [eventually_le_atBot (⟨R, hR⟩ : PositiveRadius)] with r hr
    exact congrArg ENNReal.toReal (hu.1.normalizedEnergy_eq_of_ae_eq_map hv.1 huv a r
      (Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hr).trans hball)))
  exact tendsto_congr' heq

/-- Two finite normalized-energy limits of the same weak Sobolev map class
are equal. -/
theorem MemW12Loc.normalizedEnergy_limit_eq_of_ae_eq_map {n q : ℕ}
    {Ω : OpenDomain n} {u v : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    (huv : u =ᵐ[volume.restrict Ω.val] v) (a : Domain n) (ha : a ∈ Ω.val)
    {θ η : ℝ}
    (hθ : Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal) atBot (𝓝 θ))
    (hη : Tendsto (fun r : PositiveRadius => (normalizedEnergy Dv a r).toReal) atBot (𝓝 η)) :
    θ = η :=
  tendsto_nhds_unique ((hu.normalizedEnergy_tendsto_iff_of_ae_eq_map hv huv a ha θ).mp hθ) hη

end HarmonicMaps
