module

public import StratificationTheory.Foundation.CylinderBochnerL2

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

/-- Probability averaging preserves the actual product L2 data and their raw
vector time weak identity, with integrability derived from those data. -/
theorem probability_average_raw_time_weak_identity
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {σ : Measure α} {P : Measure β} [IsFiniteMeasure σ] [IsProbabilityMeasure P]
    {q : ℕ} (a b : ℝ) {f g : (α × ℝ) × β → Ambient q}
    (hf : MemLp f 2 ((σ.prod (volume.restrict (Ioo a b))).prod P))
    (hg : MemLp g 2 ((σ.prod (volume.restrict (Ioo a b))).prod P))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∀ᵐ p : α × β ∂σ.prod P,
        (∫ t in Ioo a b, deriv φ t • f ((p.1, t), p.2) +
          φ t • g ((p.1, t), p.2)) = 0) :
    MemLp (fun p : α × ℝ => ∫ r, f (p, r) ∂P) 2 (σ.prod (volume.restrict (Ioo a b))) ∧
    MemLp (fun p : α × ℝ => ∫ r, g (p, r) ∂P) 2 (σ.prod (volume.restrict (Ioo a b))) ∧
    (∀ᵐ x ∂σ,
      IntegrableOn (fun t => ∫ r, f ((x, t), r) ∂P) (Ioo a b) ∧
      IntegrableOn (fun t => ∫ r, g ((x, t), r) ∂P) (Ioo a b)) ∧
    ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∀ᵐ x ∂σ,
        IntegrableOn (fun t => deriv φ t • (∫ r, f ((x, t), r) ∂P)) (Ioo a b) ∧
        IntegrableOn (fun t => φ t • (∫ r, g ((x, t), r) ∂P)) (Ioo a b) ∧
        IntegrableOn (fun t => deriv φ t • (∫ r, f ((x, t), r) ∂P) +
          φ t • (∫ r, g ((x, t), r) ∂P)) (Ioo a b) ∧
        (∫ t in Ioo a b, deriv φ t • (∫ r, f ((x, t), r) ∂P) +
          φ t • (∫ r, g ((x, t), r) ∂P)) = 0 := by
  let ν : Measure ℝ := volume.restrict (Ioo a b)
  have hAf : MemLp (fun p : α × ℝ => ∫ r, f (p, r) ∂P) 2 (σ.prod ν) :=
    (memLp_two_probability_average hf).1
  have hAg : MemLp (fun p : α × ℝ => ∫ r, g (p, r) ∂P) 2 (σ.prod ν) :=
    (memLp_two_probability_average hg).1
  have hAfi : Integrable (fun p : α × ℝ => ∫ r, f (p, r) ∂P) (σ.prod ν) :=
    hAf.integrable (by norm_num)
  have hAgi : Integrable (fun p : α × ℝ => ∫ r, g (p, r) ∂P) (σ.prod ν) :=
    hAg.integrable (by norm_num)
  have hTime : ∀ᵐ x ∂σ,
      IntegrableOn (fun t => ∫ r, f ((x, t), r) ∂P) (Ioo a b) ∧
      IntegrableOn (fun t => ∫ r, g ((x, t), r) ∂P) (Ioo a b) := by
    filter_upwards [hAfi.prod_right_ae, hAgi.prod_right_ae] with x hfx hgx
    exact ⟨hfx, hgx⟩
  refine ⟨hAf, hAg, hTime, ?_⟩
  intro φ hφ hcφ hsφ
  have hDL : MemLp (deriv φ) ∞ ν :=
    (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hcφ.deriv ν
  have hφL : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hcφ ν
  have hAssoc := (measurePreserving_prodAssoc σ ν P).symm MeasurableEquiv.prodAssoc
  have hfA : MemLp (fun p : α × (ℝ × β) => f ((p.1, p.2.1), p.2.2)) 2
      (σ.prod (ν.prod P)) := hf.comp_measurePreserving hAssoc
  have hgA : MemLp (fun p : α × (ℝ × β) => g ((p.1, p.2.1), p.2.2)) 2
      (σ.prod (ν.prod P)) := hg.comp_measurePreserving hAssoc
  have hDfW : MemLp (fun p : α × (ℝ × β) => deriv φ p.2.1 • f ((p.1, p.2.1), p.2.2)) 2
      (σ.prod (ν.prod P)) := hfA.smul ((hDL.comp_fst P).comp_snd σ)
  have hφgW : MemLp (fun p : α × (ℝ × β) => φ p.2.1 • g ((p.1, p.2.1), p.2.2)) 2
      (σ.prod (ν.prod P)) := hgA.smul ((hφL.comp_fst P).comp_snd σ)
  have hDfi : Integrable (fun p : α × (ℝ × β) => deriv φ p.2.1 • f ((p.1, p.2.1), p.2.2))
      (σ.prod (ν.prod P)) := hDfW.integrable (by norm_num)
  have hφgi : Integrable (fun p : α × (ℝ × β) => φ p.2.1 • g ((p.1, p.2.1), p.2.2))
      (σ.prod (ν.prod P)) := hφgW.integrable (by norm_num)
  have hraw := Measure.ae_ae_of_ae_prod (hw φ hφ hcφ hsφ)
  filter_upwards [hDfi.prod_right_ae, hφgi.prod_right_ae, hTime, hraw] with x hDf hgφ hx hwx
  have hDfAvg : Integrable (fun t => deriv φ t • (∫ r, f ((x, t), r) ∂P)) ν :=
    hx.1.smul_of_top_right hDL
  have hgφAvg : Integrable (fun t => φ t • (∫ r, g ((x, t), r) ∂P)) ν :=
    hx.2.smul_of_top_right hφL
  refine ⟨hDfAvg, hgφAvg, hDfAvg.add hgφAvg, ?_⟩
  have hInner :
      (fun t => deriv φ t • (∫ r, f ((x, t), r) ∂P) + φ t • (∫ r, g ((x, t), r) ∂P)) =ᵐ[ν]
      (fun t => ∫ r, deriv φ t • f ((x, t), r) + φ t • g ((x, t), r) ∂P) := by
    filter_upwards [hDf.prod_right_ae, hgφ.prod_right_ae] with t hft hgt
    rw [integral_add hft hgt, integral_smul, integral_smul]
  calc
    (∫ t in Ioo a b, deriv φ t • (∫ r, f ((x, t), r) ∂P) +
        φ t • (∫ r, g ((x, t), r) ∂P)) =
        ∫ t, (∫ r, deriv φ t • f ((x, t), r) + φ t • g ((x, t), r) ∂P) ∂ν :=
      integral_congr_ae hInner
    _ = ∫ r, (∫ t, deriv φ t • f ((x, t), r) + φ t • g ((x, t), r) ∂ν) ∂P :=
      integral_integral_swap (hDf.add hgφ)
    _ = 0 := by
      calc
        _ = ∫ _ : β, (0 : Ambient q) ∂P := integral_congr_ae hwx
        _ = 0 := integral_zero _ _

end StratificationTheory
