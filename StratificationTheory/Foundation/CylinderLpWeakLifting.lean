module

public import StratificationTheory.Foundation.CylinderBochnerL2
public import StratificationTheory.Foundation.IntervalClosedConstraints

public section
open HarmonicMaps MeasureTheory Metric Set Filter MeasurableSpace
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

/-- Actual angular-time L2 data with their per-angle vector weak derivative
admit the same L2-valued slice representatives and their Bochner weak identity. -/
theorem exists_native_lp_two_time_curves_with_weak_identity
    {n q : ℕ} (hn : 0 < n) (a b : ℝ)
    {f g : sphere (0 : Domain n) 1 × ℝ → Ambient q}
    (hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))))
    (hg : MemLp g 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)),
        (∫ t in Icc a b, deriv φ t • f (θ, t)) =
          -(∫ t in Icc a b, φ t • g (θ, t))) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃ F G : ℝ → Lp (Ambient q) 2 σ,
      MemLp F 2 (volume.restrict (Icc a b)) ∧
      MemLp G 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ, F t = ht.toLp (fun θ => f (θ, t))) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ∃ ht : MemLp (fun θ => g (θ, t)) 2 σ, G t = ht.toLp (fun θ => g (θ, t))) ∧
      ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b →
        Integrable (fun t => deriv φ t • F t) ∧
        Integrable (fun t => φ t • G t) ∧
        (∫ t, deriv φ t • F t) = -(∫ t, φ t • G t) := by
  intro σ
  let ν : Measure ℝ := volume.restrict (Icc a b)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  obtain ⟨F, hF, hFs, hFp⟩ := exists_native_lp_two_time_curve_with_pairings hn a b hf
  obtain ⟨G, hG, hGs, hGp⟩ := exists_native_lp_two_time_curve_with_pairings hn a b hg
  refine ⟨F, G, hF, hG, hFs, hGs, ?_⟩
  intro φ hφ hcφ hsφ
  have hD : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hDL : MemLp (deriv φ) ∞ ν := hD.memLp_top_of_hasCompactSupport hcφ.deriv ν
  have hφL : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hcφ ν
  have hDFL : MemLp (fun t => deriv φ t • F t) 2 ν := hF.smul hDL
  have hφGL : MemLp (fun t => φ t • G t) 2 ν := hG.smul hφL
  have hDF : Integrable (fun t => deriv φ t • F t) ν := hDFL.integrable (by norm_num)
  have hφG : Integrable (fun t => φ t • G t) ν := hφGL.integrable (by norm_num)
  have hDFsupp : Function.support (fun t => deriv φ t • F t) ⊆ Icc a b := by
    intro t ht
    have hDt : deriv φ t ≠ 0 := by
      intro hz
      apply ht
      change deriv φ t • F t = 0
      rw [hz, zero_smul]
    exact Ioo_subset_Icc_self (hsφ (tsupport_deriv_subset (subset_tsupport _ hDt)))
  have hφGsupp : Function.support (fun t => φ t • G t) ⊆ Icc a b := by
    intro t ht
    have hφt : φ t ≠ 0 := by
      intro hz
      apply ht
      change φ t • G t = 0
      rw [hz, zero_smul]
    exact Ioo_subset_Icc_self (hsφ (subset_tsupport _ hφt))
  refine ⟨(integrableOn_iff_integrable_of_support_subset hDFsupp).mp hDF,
    (integrableOn_iff_integrable_of_support_subset hφGsupp).mp hφG, ?_⟩
  have hleft : (∫ t in Icc a b, deriv φ t • F t) = ∫ t, deriv φ t • F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact Function.notMem_support.mp (fun hmem => ht (hDFsupp hmem))
  have hright : (∫ t in Icc a b, φ t • G t) = ∫ t, φ t • G t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact Function.notMem_support.mp (fun hmem => ht (hφGsupp hmem))
  rw [← hleft, ← hright]
  apply ext_inner_left ℝ
  intro c
  rw [inner_neg_right, hFp (deriv φ) hD hcφ.deriv c, hGp φ hφ.continuous hcφ c,
    ← integral_neg]
  have hDProd : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => deriv φ p.2) ∞ (σ.prod ν) :=
    hDL.comp_snd σ
  have hφProd : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => φ p.2) ∞ (σ.prod ν) :=
    hφL.comp_snd σ
  have hDfL : MemLp (fun p => deriv φ p.2 • f p) 2 (σ.prod ν) := hf.smul hDProd
  have hφgL : MemLp (fun p => φ p.2 • g p) 2 (σ.prod ν) := hg.smul hφProd
  have hDf : Integrable (fun p => deriv φ p.2 • f p) (σ.prod ν) := hDfL.integrable (by norm_num)
  have hφg : Integrable (fun p => φ p.2 • g p) (σ.prod ν) := hφgL.integrable (by norm_num)
  apply integral_congr_ae
  filter_upwards [hDf.prod_right_ae, hφg.prod_right_ae, hw φ hφ hcφ hsφ] with θ hfθ hgθ hwθ
  calc
    (∫ t in Icc a b, deriv φ t * inner ℝ (c θ) (f (θ, t))) =
        inner ℝ (c θ) (∫ t in Icc a b, deriv φ t • f (θ, t)) := by
      simpa only [inner_smul_right] using (integral_inner (𝕜 := ℝ) hfθ (c θ))
    _ = inner ℝ (c θ) (-(∫ t in Icc a b, φ t • g (θ, t))) := congrArg _ hwθ
    _ = -(∫ t in Icc a b, φ t * inner ℝ (c θ) (g (θ, t))) := by
      rw [inner_neg_right, ← integral_inner (𝕜 := ℝ) hgθ (c θ)]
      simp only [inner_smul_right]
      rfl


/-- Conditional native L2 weak data determine exactly one continuous map
whose interior values represent the original angular slices almost everywhere. -/
theorem exists_unique_native_lp_continuous_representative_of_raw_time_identity
    {n q : ℕ} (hn : 0 < n) {a b : ℝ} (hab : a < b)
    {f g : sphere (0 : Domain n) 1 × ℝ → Ambient q}
    (hf : MemLp f 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))))
    (hg : MemLp g 2 ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)),
        (∫ t in Icc a b, deriv φ t • f (θ, t)) =
          -(∫ t in Icc a b, φ t • g (θ, t))) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃! H : C(Icc a b, Lp (Ambient q) 2 σ),
      ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ hslice : MemLp (fun θ => f (θ, t)) 2 σ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => f (θ, t)) := by
  intro σ
  obtain ⟨F, G, hF, hG, hFs, _, hweak⟩ :=
    exists_native_lp_two_time_curves_with_weak_identity hn a b hf hg hw
  have hFI : MemLp F 2 (volume.restrict (Ioo a b)) :=
    hF.mono_measure (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  have hGI : MemLp G 2 (volume.restrict (Ioo a b)) :=
    hG.mono_measure (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  have hweakI : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t, deriv φ t • F t) = -(∫ t, φ t • G t) :=
    fun φ hφ hcφ hsφ => (hweak φ hφ hcφ hsφ).2.2
  obtain ⟨H, hH, _⟩ :=
    banach_interval_weakDerivative_exists_unique_continuous_representative hab hFI hGI hweakI
  have hFsI : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ∃ ht : MemLp (fun θ => f (θ, t)) 2 σ, F t = ht.toLp (fun θ => f (θ, t)) :=
    ae_mono (Measure.restrict_mono_set volume Ioo_subset_Icc_self) hFs
  have hFsV := (ae_restrict_iff' measurableSet_Ioo).mp hFsI
  have hHs : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ => f (θ, t)) 2 σ,
        H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => f (θ, t)) := by
    filter_upwards [hH.1, hFsV] with t hHt hFt ht
    obtain ⟨hft, hFtEq⟩ := hFt ht
    exact ⟨hft, (hHt ht).trans hFtEq⟩
  refine ⟨H, hHs, ?_⟩
  intro K hKs
  have hdiff : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      (K - H) ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ)) := by
    filter_upwards [hKs, hHs] with t hKt hHt ht
    obtain ⟨hKtL, hKtEq⟩ := hKt ht
    obtain ⟨hHtL, hHtEq⟩ := hHt ht
    have heq : hKtL.toLp (fun θ => f (θ, t)) = hHtL.toLp (fun θ => f (θ, t)) :=
      hKtL.toLp_congr hHtL (Filter.EventuallyEq.rfl)
    change K ⟨t, ht.1.le, ht.2.le⟩ - H ⟨t, ht.1.le, ht.2.le⟩ ∈ ({0} : Set (Lp (Ambient q) 2 σ))
    rw [mem_singleton_iff, sub_eq_zero]
    exact hKtEq.trans (heq.trans hHtEq.symm)
  have hclosed := continuous_interval_mem_closed_of_ae hab (K - H) isClosed_singleton hdiff
  apply ContinuousMap.ext
  intro t
  exact sub_eq_zero.mp (Set.mem_singleton_iff.mp (hclosed t))

end StratificationTheory
