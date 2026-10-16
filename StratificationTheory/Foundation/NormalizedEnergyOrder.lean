module

public import HarmonicMaps.Analysis.Monotonicity
public import HarmonicMaps.Analysis.AffineEnergyScaling

public section

open MeasureTheory Set

namespace HarmonicMaps

/-- Local Sobolev data make every normalized energy on a compactly contained
ball finite, before converting that energy to a real number. -/
theorem MemW12Loc.normalizedEnergy_ne_top_ball {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {r : PositiveRadius}
    (hball : Metric.closedBall a r.val ⊆ Ω.val) :
    normalizedEnergy Du a r ≠ ⊤ :=
  normalizedEnergy_ne_top_of_dirichletEnergy_ne_top (hu.dirichletEnergy_ne_top_ball hball)

/-- The finite real values retain the upstream normalized-energy monotonicity
on all positive radii up to the compactly contained outer ball. -/
theorem IsLocallyEnergyMinimizing.normalizedEnergy_toReal_monotoneOn {n q : ℕ}
    (hn : 2 ≤ n) {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) :
    MonotoneOn (fun t : PositiveRadius => (normalizedEnergy Du a t).toReal)
      {t | t.val ≤ R} := by
  intro s hs r hr hsr
  have hrball : Metric.closedBall a r.val ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall hr).trans hball
  exact ENNReal.toReal_mono (hu.normalizedEnergy_ne_top_ball hrball)
    ((hmin.normalizedEnergy_monotoneOn hn hu hN hR hball) hs hr hsr)

/-- Ball containment compares the actual extended Dirichlet energies. -/
theorem dirichletEnergy_le_of_subset {n q : ℕ} (Du : Domain n → Gradient n q)
    {U V : Set (Domain n)} (hUV : U ⊆ V) :
    dirichletEnergy Du U ≤ dirichletEnergy Du V :=
  lintegral_mono_set hUV

/-- The moving-center estimate keeps the normalization at the inner radius.
It does not replace that factor with the outer-radius normalization. -/
theorem normalizedEnergy_le_ball_energy {n q : ℕ} (Du : Domain n → Gradient n q)
    (a b : Domain n) (r s : PositiveRadius)
    (hball : r.val + dist a b ≤ s.val) :
    normalizedEnergy Du a r ≤
      ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
        dirichletEnergy Du (Metric.ball b s.val) :=
  mul_le_mul_right (dirichletEnergy_le_of_subset Du (Metric.ball_subset_ball' hball)) _

/-- For a finite outer-ball energy, ball containment also compares real
normalized energy with the genuine real energy integral. -/
theorem MemW12Loc.normalizedEnergy_toReal_le_ball_integral {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (a b : Domain n) (r s : PositiveRadius)
    (hball : r.val + dist a b ≤ s.val)
    (houter : Metric.closedBall b s.val ⊆ Ω.val) :
    (normalizedEnergy Du a r).toReal ≤
      r.val ^ (2 - (n : ℤ)) * ∫ x in Metric.ball b s.val, hsNormSq (Du x) := by
  have hfinite : ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
      dirichletEnergy Du (Metric.ball b s.val) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hu.dirichletEnergy_ne_top_ball houter)
  have hle := ENNReal.toReal_mono hfinite (normalizedEnergy_le_ball_energy Du a b r s hball)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (zpow_pos r.property _)),
    dirichletEnergy_toReal (hu.integrable_hsNormSq_ball houter)] at hle
  exact hle

/-- Positive affine pullback preserves normalized energy at every center and
positive radius, with its exact weak-gradient multiplier and Jacobian. -/
theorem normalizedEnergy_affine_pullback {n q : ℕ} (a b : Domain n)
    (ρ r : PositiveRadius) (Du : Domain n → Gradient n q) :
    normalizedEnergy (fun z i => ρ.val • Du (a + ρ.val • z) i) b r =
      normalizedEnergy Du (a + ρ.val • b) ⟨ρ.val * r.val, mul_pos ρ.property r.property⟩ := by
  have henergy := dirichletEnergy_affineBall (a + ρ.val • b) b ρ.property
    (ρ.val * r.val) Du
  have harg : (fun z i => ρ.val • Du (a + ρ.val • b + ρ.val • (z - b)) i) =
      (fun z i => ρ.val • Du (a + ρ.val • z) i) := by
    funext z i
    congr 2
    simp only [smul_sub]
    abel
  simp only [mul_div_cancel_left₀ _ ρ.property.ne', harg] at henergy
  unfold normalizedEnergy
  rw [henergy, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (zpow_pos r.property _))]
  congr 2
  rw [mul_zpow]
  exact mul_comm _ _

end HarmonicMaps
