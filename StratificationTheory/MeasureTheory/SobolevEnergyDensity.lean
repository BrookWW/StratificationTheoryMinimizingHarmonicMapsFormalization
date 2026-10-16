/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Actual Sobolev energy densities and ball growth

The existing weak Sobolev columns give a locally integrable nonnegative
Hilbert--Schmidt energy density. Multiplication by the exact positive radius
power converts a finite normalized-energy lower bound into a real ball-integral
lower bound, on the same admissible ball.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology

namespace HarmonicMaps

/-- Actual local Sobolev columns make the Hilbert--Schmidt density locally
integrable on the actual open domain. -/
theorem MemW12Loc.locallyIntegrableOn_hsNormSq {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) :
    LocallyIntegrableOn (fun x => hsNormSq (Du x)) Ω.val volume := by
  intro a ha
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds ha)
  exact ⟨ball a R, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hR),
    hu.integrable_hsNormSq_ball hball⟩

/-- An actual finite normalized-energy lower bound gives the ball-integral
growth bound with exponent `n - 2` and unchanged radius and constant. -/
theorem MemW12Loc.ball_energy_growth_of_normalizedEnergy_lower_bound {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (a : Domain n) (r : PositiveRadius)
    (hball : closedBall a r.val ⊆ Ω.val) (c : ℝ)
    (hlower : c ≤ (normalizedEnergy Du a r).toReal) :
    c * r.val ^ ((n : ℝ) - 2) ≤ ∫ x in ball a r.val, hsNormSq (Du x) := by
  have hcast : (n : ℝ) - 2 = (((n : ℤ) - 2 : ℤ) : ℝ) := by
    norm_cast
  have hpower : r.val ^ (2 - (n : ℤ)) * r.val ^ ((n : ℝ) - 2) = 1 := by
    rw [hcast, Real.rpow_intCast, ← zpow_add₀ r.property.ne']
    have hexp : (2 - (n : ℤ)) + ((n : ℤ) - 2) = 0 := by ring
    rw [hexp, zpow_zero]
  calc
    c * r.val ^ ((n : ℝ) - 2) ≤
        (normalizedEnergy Du a r).toReal * r.val ^ ((n : ℝ) - 2) :=
      mul_le_mul_of_nonneg_right hlower (Real.rpow_nonneg r.property.le _)
    _ = ∫ x in ball a r.val, hsNormSq (Du x) := by
      rw [normalizedEnergy_toReal (hu.integrable_hsNormSq_ball hball)]
      calc
        (r.val ^ (2 - (n : ℤ)) * ∫ x in ball a r.val, hsNormSq (Du x)) *
            r.val ^ ((n : ℝ) - 2) =
            (r.val ^ (2 - (n : ℤ)) * r.val ^ ((n : ℝ) - 2)) *
              ∫ x in ball a r.val, hsNormSq (Du x) := by ring
        _ = _ := by rw [hpower, one_mul]

end HarmonicMaps
