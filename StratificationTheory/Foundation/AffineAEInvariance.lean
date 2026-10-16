module

public import HarmonicMaps.Analysis.AffineBallMeasure

/-!
# Almost-everywhere affine invariance

Positive affine transformations preserve volume null sets. Homogeneity about
two centers therefore produces translation invariance of the same
almost-everywhere map class.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StratificationTheory

theorem ae_affine_volume {n : ℕ} (a b : Domain n) {l : ℝ} (hl : 0 < l)
    {p : Domain n → Prop} (hp : ∀ᵐ x ∂volume, p x) :
    ∀ᵐ x ∂volume, p (a + l • (x - b)) := by
  have hpc : ∀ᵐ x ∂(ENNReal.ofReal ((l ^ n)⁻¹) • volume), p x :=
    Measure.ae_smul_measure hp _
  rw [← affineBall_map_volume a b hl] at hpc
  exact ae_of_ae_map (affineBall_measurableEmbedding a b hl.ne').measurable.aemeasurable hpc

theorem ae_eq_translate_neg {n q : ℕ} {u : Domain n → Ambient q} (y : Domain n)
    (h : (fun x => u (x + y)) =ᵐ[volume] u) :
    (fun x => u (x - y)) =ᵐ[volume] u := by
  have hp := (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae h
  filter_upwards [hp] with x hx
  simpa only [sub_add_cancel] using hx.symm

theorem ae_eq_translate_add {n q : ℕ} {u : Domain n → Ambient q}
    (y z : Domain n) (hy : (fun x => u (x + y)) =ᵐ[volume] u)
    (hz : (fun x => u (x + z)) =ᵐ[volume] u) :
    (fun x => u (x + (y + z))) =ᵐ[volume] u := by
  have hyp := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae hy
  filter_upwards [hyp, hz] with x hxy hxz
  have hx := hxy.trans hxz
  simpa only [add_right_comm x z y, add_assoc] using hx

theorem ae_eq_translate_of_two_centered_dilations {n q : ℕ}
    {u : Domain n → Ambient q} (y : Domain n) {l : ℝ} (hl : 0 < l)
    (hzero : (fun x => u (l⁻¹ • x)) =ᵐ[volume] u)
    (hy : (fun x => u (y + l • (x - y))) =ᵐ[volume] u) :
    (fun x => u (x + (1 - l) • y)) =ᵐ[volume] u := by
  have hyp := ae_affine_volume (0 : Domain n) 0 (inv_pos.mpr hl) hy
  filter_upwards [hyp, hzero] with x hxy hx0
  have heq : y + l • ((0 : Domain n) + l⁻¹ • (x - 0) - y) = x + (1 - l) • y := by
    simp only [sub_zero, zero_add, smul_sub, smul_smul, mul_inv_cancel₀ hl.ne',
      one_smul, sub_smul]
    abel
  rw [heq] at hxy
  exact hxy.trans (by simpa only [zero_add, sub_zero] using hx0)

theorem ae_eq_translate_smul_of_all_centered_dilations {n q : ℕ}
    {u : Domain n → Ambient q} (y : Domain n)
    (hzero : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (hy : ∀ l : ℝ, 0 < l → (fun x => u (y + l • (x - y))) =ᵐ[volume] u)
    (t : ℝ) :
    (fun x => u (x + t • y)) =ᵐ[volume] u := by
  by_cases ht : t < 1
  · have hl : 0 < 1 - t := sub_pos.mpr ht
    have h := ae_eq_translate_of_two_centered_dilations y hl
      (hzero _ (inv_pos.mpr hl)) (hy _ hl)
    simpa only [sub_sub_cancel] using h
  · have hlt : -t < 1 := by linarith only [not_lt.mp ht]
    have hl : 0 < 1 - (-t) := sub_pos.mpr hlt
    have h := ae_eq_translate_of_two_centered_dilations y hl
      (hzero _ (inv_pos.mpr hl)) (hy _ hl)
    have hneg : (fun x => u (x + (-t) • y)) =ᵐ[volume] u := by
      simpa only [sub_sub_cancel] using h
    have hinv := ae_eq_translate_neg ((-t) • y) hneg
    simpa only [neg_smul, sub_neg_eq_add] using hinv

end StratificationTheory
