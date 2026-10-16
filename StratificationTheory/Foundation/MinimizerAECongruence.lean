module

public import HarmonicMaps.Minimizer
public import HarmonicMaps.EnergyLemmas
public import HarmonicMaps.Analysis.SobolevAECongruence

public section
open HarmonicMaps MeasureTheory Metric Filter Set

namespace HarmonicMaps

/-- Actual almost-everywhere replacement of a map and its displayed columns
preserves local minimality against the original zero-boundary competitors. -/
theorem IsLocallyEnergyMinimizing.congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {N : CompactSmoothEmbeddedTarget q}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du)
    (huv : u =ᵐ[volume.restrict Ω.val] v)
    (hDuDv : Du =ᵐ[volume.restrict Ω.val] Dv) :
    IsLocallyEnergyMinimizing N Ω v Dv := by
  intro a r hr hclosed z Dz hz hzN hboundary
  have hsub : (ballDomain a r).val ⊆ Ω.val := ball_subset_closedBall.trans hclosed
  have hMap : v =ᵐ[volume.restrict (ballDomain a r).val] u :=
    ae_restrict_of_ae_restrict_of_subset hsub huv.symm
  have hGrad : Dv =ᵐ[volume.restrict (ballDomain a r).val] Du :=
    ae_restrict_of_ae_restrict_of_subset hsub hDuDv.symm
  have hboundaryOld : HasZeroBoundaryDifference (ballDomain a r) u Du z Dz := by
    change HasZeroBoundaryValues (ballDomain a r) (z - v) (fun x i => Dz x i - Dv x i) at hboundary
    change HasZeroBoundaryValues (ballDomain a r) (z - u) (fun x i => Dz x i - Du x i)
    apply hboundary.congr_ae
    · exact hMap.mono fun x hx => congrArg (fun y => z x - y) hx
    · filter_upwards [hGrad] with x hx
      funext i
      exact congrArg (fun D : Gradient n q => Dz x i - D i) hx
  have hEnergy := hmin a r hr hclosed z Dz hz hzN hboundaryOld
  have hEq : dirichletEnergy Dv (ball a r) = dirichletEnergy Du (ball a r) :=
    dirichletEnergy_congr_ae hGrad
  exact hEq.trans_le hEnergy

end HarmonicMaps
