module

public import StratificationTheory.Foundation.PolarSliceConvergence
public import StratificationTheory.Foundation.AngularL2Membership

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology BigOperators ENNReal

namespace StratificationTheory


/-- A finite family of nonnegative actual ball L1 errors shares one strictly
increasing subsequence and one radial full-measure set of vanishing angular
integrals. Every original error retains angular integrability. -/
theorem exists_subseq_ae_tendsto_polar_integral_family_zero_ball
    {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    {f : ι → ℕ → Domain n → ℝ} {a : Domain n} {R : ℝ}
    (hf : ∀ i k, IntegrableOn (f i k) (ball a R))
    (hfn : ∀ i k x, 0 ≤ f i k x)
    (hlim : ∀ i, Tendsto (fun k => ∫ x in ball a R, f i k x) atTop (𝓝 0)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), ∀ i,
        (∀ k, Integrable (fun θ : sphere (0 : Domain n) 1 => f i k (a + r • θ.val))
          (volume : Measure (Domain n)).toSphere) ∧
        Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
          f i (κ k) (a + r • θ.val) ∂(volume : Measure (Domain n)).toSphere)
            atTop (𝓝 0) := by
  classical
  let F : ℕ → Domain n → ℝ := fun k x => ∑ i, f i k x
  have hF (k : ℕ) : IntegrableOn (F k) (ball a R) :=
    integrable_finsetSum _ (fun i _ => hf i k)
  have hFn (k : ℕ) (x : Domain n) : 0 ≤ F k x :=
    Finset.sum_nonneg fun i _ => hfn i k x
  have hFint (k : ℕ) : (∫ x in ball a R, F k x) = ∑ i, ∫ x in ball a R, f i k x :=
    integral_finsetSum _ (fun i _ => hf i k)
  have hFlim : Tendsto (fun k => ∫ x in ball a R, F k x) atTop (𝓝 0) := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
    simpa only [← hFint, Finset.sum_const_zero] using ht
  obtain ⟨κ, hκ, hκae⟩ := exists_subseq_ae_tendsto_polar_integral_zero_ball (n := n) (f := F)
    (a := a) (R := R) hn hF hFn hFlim
  have hi : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), ∀ i k,
      Integrable (fun θ : sphere (0 : Domain n) 1 => f i k (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k =>
      ae_integrable_polar_slice_ball (n := n) (f := f i k) (a := a) (R := R) (hf i k)
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hκae, hi] with r hr hri
  intro i
  refine ⟨hri i, ?_⟩
  have hbound (k : ℕ) :
      (∫ θ : sphere (0 : Domain n) 1, f i (κ k) (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) ≤
      (∫ θ : sphere (0 : Domain n) 1, F (κ k) (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) := by
    apply integral_mono (hri i (κ k)) (hr.1 (κ k))
    intro θ
    change f i (κ k) (a + r • θ.val) ≤ ∑ j, f j (κ k) (a + r • θ.val)
    exact Finset.single_le_sum (fun j _ => hfn j (κ k) (a + r • θ.val))
      (Finset.mem_univ i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr.2
    (fun k => integral_nonneg fun θ => hfn i (κ k) (a + r • θ.val)) hbound


private theorem tendsto_integral_norm_sq_zero_of_l2
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : ℕ → α → E}
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have heq (k : ℕ) : (∫ x, ‖f k x‖ ^ 2 ∂μ) = (eLpNorm (f k) 2 μ).toReal ^ 2 := by
    have hpos : 0 ≤ ∫ x, ‖f k x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have hnorm : eLpNorm (f k) 2 μ =
        ENNReal.ofReal ((∫ x, ‖f k x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hf k).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    rw [hnorm, ENNReal.toReal_ofReal (Real.rpow_nonneg hpos _)]
    exact (Real.rpow_inv_natCast_pow (n := 2) hpos (by decide)).symm
  have ht := ((ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hlim).pow 2
  simpa only [Function.comp_def, ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0),
    ← heq] using ht


/-- Actual L2 convergence of a finite family on a ball yields one subsequence
with angular squared errors vanishing on a shared radial full-measure set.
The actual original maps and all limits retain angular L2 membership. -/
theorem exists_subseq_ae_tendsto_polar_l2_family_ball
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] {n : ℕ} (hn : 0 < n)
    {f : ι → ℕ → Domain n → E} {u : ι → Domain n → E}
    {a : Domain n} {R : ℝ}
    (hf : ∀ i k, MemLp (f i k) 2 (volume.restrict (ball a R)))
    (hu : ∀ i, MemLp (u i) 2 (volume.restrict (ball a R)))
    (hlim : ∀ i, Tendsto (fun k => eLpNorm (f i k - u i) 2
      (volume.restrict (ball a R))) atTop (𝓝 0)) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), ∀ i,
        (∀ k, MemLp (fun θ : sphere (0 : Domain n) 1 => f i k (a + r • θ.val))
          2 (volume : Measure (Domain n)).toSphere) ∧
        MemLp (fun θ : sphere (0 : Domain n) 1 => u i (a + r • θ.val))
          2 (volume : Measure (Domain n)).toSphere ∧
        (∀ k, Integrable (fun θ : sphere (0 : Domain n) 1 =>
          ‖f i k (a + r • θ.val) - u i (a + r • θ.val)‖ ^ 2)
            (volume : Measure (Domain n)).toSphere) ∧
        Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
          ‖f i (κ k) (a + r • θ.val) - u i (a + r • θ.val)‖ ^ 2
            ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
  have he (i : ι) (k : ℕ) : MemLp (f i k - u i) 2 (volume.restrict (ball a R)) :=
    (hf i k).sub (hu i)
  have hint (i : ι) (k : ℕ) : IntegrableOn
      (fun x : Domain n => ‖f i k x - u i x‖ ^ 2) (ball a R) :=
    (he i k).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hs (i : ι) : Tendsto (fun k => ∫ x in ball a R, ‖f i k x - u i x‖ ^ 2)
      atTop (𝓝 0) := tendsto_integral_norm_sq_zero_of_l2 (he i) (hlim i)
  obtain ⟨κ, hκ, hκae⟩ := exists_subseq_ae_tendsto_polar_integral_family_zero_ball
    (n := n) (f := fun i k x => ‖f i k x - u i x‖ ^ 2) (a := a) (R := R) hn
      hint (fun _ _ _ => sq_nonneg _) hs
  have hmaps : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), ∀ i k,
      MemLp (fun θ : sphere (0 : Domain n) 1 => f i k (a + r • θ.val))
        2 (volume : Measure (Domain n)).toSphere :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k =>
      ae_memLp_two_polar_slice_ball (n := n) (f := f i k) (a := a) (R := R) (hf i k)
  have htargets : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), ∀ i,
      MemLp (fun θ : sphere (0 : Domain n) 1 => u i (a + r • θ.val))
        2 (volume : Measure (Domain n)).toSphere :=
    ae_all_iff.mpr fun i =>
      ae_memLp_two_polar_slice_ball (n := n) (f := u i) (a := a) (R := R) (hu i)
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hκae, hmaps, htargets] with r hr hmr hur
  intro i
  exact ⟨hmr i, hur i, (hr i).1, (hr i).2⟩

end StratificationTheory
