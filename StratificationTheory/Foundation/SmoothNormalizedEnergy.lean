module

public import StratificationTheory.Foundation.NormalizedEnergyOrder
public import HarmonicMaps.Analysis.SobolevAECongruence
public import HolderToCK.Analysis.ClassicalWeakGradient
public import StratificationTheory.Foundation.PositiveRadiusLimits

public section

open MeasureTheory Filter Set
open scoped Topology

namespace HarmonicMaps

/-- A local bound for the actual Hilbert--Schmidt density gives a quadratic
bound for real normalized energy, with the volume of the unit ball. -/
theorem normalizedEnergy_toReal_le_radius_sq_of_ae_bound {n q : ℕ}
    (Du : Domain n → Gradient n q) (a : Domain n) (r : PositiveRadius) (C : ℝ)
    (hI : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball a r.val) volume)
    (hC : ∀ᵐ x ∂volume.restrict (Metric.ball a r.val), hsNormSq (Du x) ≤ C) :
    (normalizedEnergy Du a r).toReal ≤
      C * (volume (Metric.ball (0 : Domain n) 1)).toReal * r.val ^ 2 := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hbound := integral_mono_ae hI (integrable_const C) hC
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at hbound
  have hvolume : (volume (Metric.ball a r.val)).toReal =
      r.val ^ n * (volume (Metric.ball (0 : Domain n) 1)).toReal := by
    rw [Measure.addHaar_ball_of_pos volume a r.property, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg r.property.le _)]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
  have hpower : r.val ^ (2 - (n : ℤ)) * r.val ^ n = r.val ^ 2 := by
    rw [← zpow_natCast, ← zpow_add₀ r.property.ne']
    simp only [sub_add_cancel, zpow_ofNat]
  rw [normalizedEnergy_toReal hI]
  calc
    r.val ^ (2 - (n : ℤ)) * ∫ x in Metric.ball a r.val, hsNormSq (Du x) ≤
        r.val ^ (2 - (n : ℤ)) * ((volume (Metric.ball a r.val)).toReal * C) :=
      mul_le_mul_of_nonneg_left hbound (le_of_lt (zpow_pos r.property _))
    _ = C * (volume (Metric.ball (0 : Domain n) 1)).toReal * r.val ^ 2 := by
      rw [hvolume]
      calc
        r.val ^ (2 - (n : ℤ)) *
            (r.val ^ n * (volume (Metric.ball (0 : Domain n) 1)).toReal * C) =
            C * (volume (Metric.ball (0 : Domain n) 1)).toReal *
              (r.val ^ (2 - (n : ℤ)) * r.val ^ n) := by ring
        _ = _ := by rw [hpower]

/-- A C1 almost-everywhere representative forces the actual weak-gradient
normalized energy to tend to zero. The derivative identification follows from
upstream weak-gradient uniqueness. -/
theorem HasWeakGradient.normalizedEnergy_tendsto_zero_of_contDiffOn_rep {n q : ℕ}
    {Ω : OpenDomain n} {u f : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) (hf : ContDiffOn ℝ 1 f Ω.val)
    (huf : u =ᵐ[volume.restrict Ω.val] f) (a : Domain n) (ha : a ∈ Ω.val) :
    Tendsto (fun r : PositiveRadius => (normalizedEnergy Du a r).toReal)
      atBot (𝓝 (0 : ℝ)) := by
  classical
  let Df : Domain n → Gradient n q := fun x i =>
    fderiv ℝ f x (EuclideanSpace.single i 1)
  have hfW : MemW12Loc Ω f Df := HolderToCK.memW12Loc_of_contDiffOn_one Ω hf
  have hDuDf : Du =ᵐ[volume.restrict Ω.val] Df :=
    hu.ae_eq_of_ae_eq_map hfW.1 huf
  have hGcont : ContinuousOn (fun x => hsNormSq (Df x)) Ω.val := by
    have hderiv := hf.continuousOn_fderiv_of_isOpen Ω.property le_rfl
    dsimp [Df, hsNormSq]
    exact continuousOn_finsetSum Finset.univ fun i _ =>
      (hderiv.clm_apply continuousOn_const).norm.pow 2
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds ha)
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).bddAbove_image (hGcont.mono hball)
  have hupper : ∀ᶠ r : PositiveRadius in atBot,
      (normalizedEnergy Du a r).toReal ≤
        C * (volume (Metric.ball (0 : Domain n) 1)).toReal * r.val ^ 2 := by
    filter_upwards [eventually_le_atBot (⟨R, hR⟩ : PositiveRadius)] with r hr
    have hrclosed : Metric.closedBall a r.val ⊆ Ω.val :=
      (Metric.closedBall_subset_closedBall hr).trans hball
    have hropen : Metric.ball a r.val ⊆ Ω.val :=
      Metric.ball_subset_closedBall.trans hrclosed
    have henergy : normalizedEnergy Du a r = normalizedEnergy Df a r := by
      unfold normalizedEnergy
      rw [dirichletEnergy_congr_ae (ae_restrict_of_ae_restrict_of_subset hropen hDuDf)]
    rw [henergy]
    apply normalizedEnergy_toReal_le_radius_sq_of_ae_bound Df a r C
      (hfW.integrable_hsNormSq_ball hrclosed)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hC (mem_image_of_mem _ ((Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hr)) hx))
  have hval : Tendsto (Subtype.val : PositiveRadius → ℝ) atBot (𝓝 (0 : ℝ)) :=
    StratificationTheory.positiveRadius_val_tendsto_zero
  have hzero : Tendsto (fun r : PositiveRadius =>
      C * (volume (Metric.ball (0 : Domain n) 1)).toReal * r.val ^ 2) atBot (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      (hval.pow 2).const_mul (C * (volume (Metric.ball (0 : Domain n) 1)).toReal)
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hupper hzero

end HarmonicMaps
