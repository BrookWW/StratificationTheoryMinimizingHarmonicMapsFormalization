module

public import StratificationTheory.Foundation.DensityBounds
public import StratificationTheory.Foundation.RadialHomogeneity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Center comparison for maps with constant centered energy

For an actual globally local minimizing Sobolev map, constant normalized
energy at the origin bounds the energy and density at every other center.
The proof compares contained balls and lets an outer radius tend to infinity.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StratificationTheory.TangentMaps

theorem integral_energy_of_constant_normalizedEnergy_origin {n q : ℕ}
    (hn : 2 ≤ n) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (r : PositiveRadius) :
    (∫ x in Metric.ball (0 : Domain n) r.val, hsNormSq (Du x)) = r.val ^ (n - 2) * θ := by
  have h := henergy r
  have hexp : 2 - (n : ℤ) = -((n - 2 : ℕ) : ℤ) := by omega
  rw [normalizedEnergy_toReal (hu.integrable_hsNormSq_ball (subset_univ _)),
    hexp, zpow_neg, zpow_natCast] at h
  calc
    _ = (r.val ^ (n - 2) * (r.val ^ (n - 2))⁻¹) *
        ∫ x in Metric.ball (0 : Domain n) r.val, hsNormSq (Du x) := by
      rw [mul_inv_cancel₀ (pow_ne_zero _ r.property.ne'), one_mul]
    _ = r.val ^ (n - 2) * θ := by rw [mul_assoc, h]

theorem normalizedEnergy_toReal_le_shift_factor {n q : ℕ} (hn : 2 ≤ n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) (r : PositiveRadius) :
    (normalizedEnergy Du y r).toReal ≤ (1 + ‖y‖ / r.val) ^ (n - 2) * θ := by
  let s : PositiveRadius := ⟨r.val + ‖y‖, add_pos_of_pos_of_nonneg r.property (norm_nonneg _)⟩
  have hball : r.val + dist y (0 : Domain n) ≤ s.val := by
    simp only [dist_zero_right]
    exact le_rfl
  have hle := hu.normalizedEnergy_toReal_le_ball_integral y 0 r s hball (subset_univ _)
  rw [integral_energy_of_constant_normalizedEnergy_origin hn hu θ henergy s] at hle
  have hexp : 2 - (n : ℤ) = -((n - 2 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast] at hle
  apply hle.trans_eq
  calc
    (r.val ^ (n - 2))⁻¹ * (s.val ^ (n - 2) * θ) = (s.val / r.val) ^ (n - 2) * θ := by
      rw [div_pow, div_eq_mul_inv]
      ring
    _ = (1 + ‖y‖ / r.val) ^ (n - 2) * θ := by
      have hratio : s.val / r.val = 1 + ‖y‖ / r.val := by
        dsimp [s]
        rw [add_div, div_self r.property.ne']
      rw [hratio]

theorem normalizedEnergy_toReal_le_origin_constant {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) (r : PositiveRadius) :
    (normalizedEnergy Du y r).toReal ≤ θ := by
  have hR : Tendsto (fun k : ℕ => r.val + ((k : ℝ) + 1)) atTop atTop := by
    simpa only [add_comm] using tendsto_atTop_add_const_right atTop r.val
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hdiv : Tendsto (fun k : ℕ => ‖y‖ / (r.val + ((k : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hR
  have hlimit : Tendsto (fun k : ℕ =>
      (1 + ‖y‖ / (r.val + ((k : ℝ) + 1))) ^ (n - 2) * θ) atTop (𝓝 θ) := by
    simpa only [add_zero, one_pow, one_mul] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hdiv).pow
        (n - 2)).mul_const θ
  apply ge_of_tendsto hlimit
  apply Eventually.of_forall
  intro k
  let R : PositiveRadius := ⟨r.val + ((k : ℝ) + 1), add_pos r.property (by positivity)⟩
  have hrR : r.val ≤ R.val := by dsimp [R]; linarith only [Nat.cast_nonneg (α := ℝ) k]
  have hmono := (hmin.normalizedEnergy_toReal_monotoneOn hn hu hN (a := y)
    R.property (subset_univ _))
    (show r.val ≤ R.val from hrR) (show R.val ≤ R.val from le_rfl) hrR
  exact hmono.trans (normalizedEnergy_toReal_le_shift_factor hn hu θ henergy y R)

theorem density_le_origin_constant {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ)
    (y : Domain n) :
    density hn hmin hu hN ⟨y, mem_univ y⟩ ≤ θ := by
  exact (density_le_normalizedEnergy_toReal hn hmin hu hN ⟨y, mem_univ y⟩
    ⟨1, by norm_num⟩ (subset_univ _)).trans
    (normalizedEnergy_toReal_le_origin_constant hn hmin hu hN θ henergy y ⟨1, by norm_num⟩)

theorem density_origin_eq_constant {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (θ : ℝ)
    (henergy : ∀ r : PositiveRadius, (normalizedEnergy Du 0 r).toReal = θ) :
    density hn hmin hu hN ⟨0, mem_univ 0⟩ = θ := by
  have hconstant : (fun r : PositiveRadius => (normalizedEnergy Du 0 r).toReal) =
      (fun _ => θ) := funext henergy
  apply Eq.symm
  apply (density_characterization hn hmin hu hN ⟨0, mem_univ 0⟩).2.2.2 θ
  rw [hconstant]
  exact tendsto_const_nhds

end StratificationTheory.TangentMaps
