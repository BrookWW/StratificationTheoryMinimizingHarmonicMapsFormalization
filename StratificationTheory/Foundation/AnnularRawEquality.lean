module

public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.EnergyLemmas
import Mathlib.MeasureTheory.Integral.Bochner.Set

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

theorem annular_weak_columns_and_energy_eq_of_raw_ray_eq {n q : ℕ}
    {s a b : ℝ} (hs : 0 < s) (ha : -1 < a)
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 ⟨{x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)},
      isOpen_Ioo.preimage continuous_norm⟩ u Du)
    (hv : MemW12 ⟨{x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)},
      isOpen_Ioo.preimage continuous_norm⟩ v Dv)
    (hraw : ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
      u ((s * (1 + t)) • θ.val) = v ((s * (1 + t)) • θ.val)) :
    Du =ᵐ[volume.restrict {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}] Dv ∧
      (∫ x in {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}, hsNormSq (Du x)) =
        ∫ x in {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}, hsNormSq (Dv x) := by
  have hUV : u =ᵐ[volume.restrict
      {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}] v := by
    filter_upwards [ae_restrict_mem (isOpen_Ioo.preimage continuous_norm).measurableSet] with x hx
    have hrad : 0 < ‖x‖ := (mul_pos hs (by linarith only [ha])).trans hx.1
    let θ : sphere (0 : Domain n) 1 := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg x)]
      exact inv_mul_cancel₀ hrad.ne'⟩
    let t := ‖x‖ / s - 1
    have ht : t ∈ Ioo a b := by
      constructor
      · have hlow : 1 + a < ‖x‖ / s := (lt_div_iff₀ hs).mpr (by nlinarith only [hx.1])
        dsimp only [t]
        linarith only [hlow]
      · have hhi : ‖x‖ / s < 1 + b := (div_lt_iff₀ hs).mpr (by nlinarith only [hx.2])
        dsimp only [t]
        linarith only [hhi]
    have hR : s * (1 + t) = ‖x‖ := by
      dsimp only [t]
      field_simp
      ring
    have hcoord : (s * (1 + t)) • θ.val = x := by
      rw [hR]
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hrad.ne', one_smul]
    simpa only [hcoord] using hraw θ t ht
  have hcols := hu.1.ae_eq_of_ae_eq_map hv.1 hUV
  refine ⟨hcols, integral_congr_ae ?_⟩
  exact hcols.mono fun _ hx => congrArg hsNormSq hx

end StratificationTheory
