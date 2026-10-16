module

public import StratificationTheory.Foundation.DensityBounds
public import StratificationTheory.Foundation.NormalizedEnergyInvariance
public import HarmonicMaps.Analysis.AffineBallSobolev

/-!
# Density and the almost-everywhere map class

The registered density is unchanged by almost-everywhere replacement of a
Sobolev map with its actual weak gradient. An almost-everywhere translation
symmetry preserves normalized energy at each translated center.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StratificationTheory

theorem density_eq_of_ae_eq_map {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hminu : IsLocallyEnergyMinimizing N Ω u Du)
    (hminv : IsLocallyEnergyMinimizing N Ω v Dv)
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    (hNu : TakesValuesIn N Ω u) (hNv : TakesValuesIn N Ω v)
    (huv : u =ᵐ[volume.restrict Ω.val] v) (a : Ω.val) :
    density hn hminu hu hNu a = density hn hminv hv hNv a := by
  apply (density_characterization hn hminv hv hNv a).2.2.2
  have hfilter : (atBot : Filter PositiveRadius) =
      comap (Subtype.val : PositiveRadius → ℝ) (𝓝[>] (0 : ℝ)) := positiveRadius_atBot_eq
  rw [← hfilter]
  exact (hu.normalizedEnergy_tendsto_iff_of_ae_eq_map hv huv a.val a.property
    (density hn hminu hu hNu a)).mp
    (normalizedEnergy_tendsto_density_atBot hn hminu hu hNu a)

theorem normalizedEnergy_eq_of_ae_translate {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du) (y : Domain n)
    (htrans : (fun x => u (x + y)) =ᵐ[volume] u)
    (a : Domain n) (r : PositiveRadius) :
    normalizedEnergy Du (a + y) r = normalizedEnergy Du a r := by
  let R : ℝ := r.val + 1
  have hW := (hu.memW12_ball (a := a + y) (r := R) (subset_univ _)).affineBall_pullback
    a (by norm_num : (0 : ℝ) < 1)
  have harg (x : Domain n) : a + y + (1 : ℝ) • (x - a) = x + y := by
    rw [one_smul]
    abel
  have harg' (x : Domain n) : a + y + (x - a) = x + y := by abel
  have hv : MemW12 (ballDomain a R) (fun x => u (x + y)) (fun x i => Du (x + y) i) := by
    simpa only [div_one, harg, harg', one_smul] using hW
  have huBall := hu.memW12_ball (a := a) (r := R) (subset_univ _)
  have hsub : Metric.ball a r.val ⊆ (ballDomain a R).val :=
    Metric.ball_subset_ball (by dsimp [R]; linarith only)
  have hae : u =ᵐ[volume.restrict (ballDomain a R).val] (fun x => u (x + y)) :=
    ae_restrict_of_ae htrans.symm
  have heq := huBall.1.normalizedEnergy_eq_of_ae_eq_map hv.1 hae a r hsub
  have hscale := normalizedEnergy_affine_pullback y a ⟨1, by norm_num⟩ r Du
  have hnormalized : normalizedEnergy (fun x i => Du (x + y) i) a r =
      normalizedEnergy Du (a + y) r := by
    simpa only [one_smul, one_mul, add_comm y a, add_comm y] using hscale
  exact (heq.trans hnormalized).symm

theorem density_eq_of_ae_translate {n q : ℕ} (hn : 2 ≤ n)
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u) (y : Domain n)
    (htrans : (fun x => u (x + y)) =ᵐ[volume] u) (a : Domain n) :
    density hn hmin hu hN ⟨a + y, mem_univ _⟩ =
      density hn hmin hu hN ⟨a, mem_univ _⟩ := by
  have heq : (fun r : PositiveRadius => (normalizedEnergy Du (a + y) r).toReal) =
      (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal) := by
    funext r
    exact congrArg ENNReal.toReal (normalizedEnergy_eq_of_ae_translate hu y htrans a r)
  have hlimit := normalizedEnergy_tendsto_density_atBot hn hmin hu hN ⟨a + y, mem_univ _⟩
  rw [heq] at hlimit
  exact tendsto_nhds_unique hlimit
    (normalizedEnergy_tendsto_density_atBot hn hmin hu hN ⟨a, mem_univ _⟩)

theorem normalizedEnergy_eq_of_ae_dilation {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du) {l : ℝ} (hl : 0 < l)
    (hdilate : (fun x => u (l • x)) =ᵐ[volume] u) (r : PositiveRadius) :
    normalizedEnergy Du 0 ⟨l * r.val, mul_pos hl r.property⟩ =
      normalizedEnergy Du 0 r := by
  let R : ℝ := l * (r.val + 1)
  have hW := (hu.memW12_ball (a := 0) (r := R) (subset_univ _)).affineBall_pullback
    (0 : Domain n) hl
  have hv : MemW12 (ballDomain (0 : Domain n) (r.val + 1))
      (fun x => u (l • x)) (fun x i => l • Du (l • x) i) := by
    simpa only [R, mul_div_cancel_left₀ _ hl.ne', sub_zero, zero_add] using hW
  have huBall := hu.memW12_ball (a := 0) (r := r.val + 1) (subset_univ _)
  have hsub : Metric.ball (0 : Domain n) r.val ⊆
      (ballDomain (0 : Domain n) (r.val + 1)).val :=
    Metric.ball_subset_ball (by linarith only)
  have hae : u =ᵐ[volume.restrict (ballDomain (0 : Domain n) (r.val + 1)).val]
      (fun x => u (l • x)) := ae_restrict_of_ae hdilate.symm
  have heq := huBall.1.normalizedEnergy_eq_of_ae_eq_map hv.1 hae 0 r hsub
  have hscale := normalizedEnergy_affine_pullback (0 : Domain n) 0 ⟨l, hl⟩ r Du
  have hnormalized : normalizedEnergy (fun x i => l • Du (l • x) i) 0 r =
      normalizedEnergy Du 0 ⟨l * r.val, mul_pos hl r.property⟩ := by
    simpa only [zero_add, smul_zero] using hscale
  exact (heq.trans hnormalized).symm

theorem normalizedEnergy_eq_unit_of_ae_homogeneous {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (r : PositiveRadius) :
    normalizedEnergy Du 0 r = normalizedEnergy Du 0 ⟨1, by norm_num⟩ := by
  simpa only [mul_one] using normalizedEnergy_eq_of_ae_dilation hu r.property
    (hhom r.val r.property) ⟨1, by norm_num⟩

end StratificationTheory
