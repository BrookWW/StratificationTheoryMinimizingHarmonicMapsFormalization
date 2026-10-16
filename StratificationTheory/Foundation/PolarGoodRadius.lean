module

public import StratificationTheory.Foundation.SobolevPolarSlices
public import HarmonicMaps.Analysis.AnnularPolarIntegral
import Mathlib.MeasureTheory.Integral.Average

/-!
# Simultaneous selection of integral slices

Polar Fubini supplies actual integrable radial densities. A first-moment
argument selects one radius in a positive annulus with separate bounds for
two nonnegative densities. The Sobolev specialization uses Hilbert--Schmidt
energy and squared separation; the selected data are angular integrals.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter

namespace StratificationTheory

/-- A global L1 function has an integrable radial polar density with the exact
Jacobian, independently of any Sobolev regularity. -/
theorem integrable_polar_density {n : ℕ} {f : Domain n → ℝ}
    (hf : Integrable f volume) (a : Domain n) :
    IntegrableOn (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) (Ioi (0 : ℝ)) volume := by
  have hp := (integrable_polar_coordinates hf a).integral_prod_right
  rw [Measure.volumeIoiPow] at hp
  have hw := (integrable_withDensity_iff_integrable_smul'
    (measurable_subtype_coe.pow_const (n - 1)).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hp
  apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mpr
  apply hw.congr
  filter_upwards with r
  rw [ENNReal.toReal_ofReal (pow_nonneg r.property.le _), smul_eq_mul]
  rfl

/-- A ball-local L1 function has its own integrable radial polar density on the
exact open radius interval. -/
theorem integrable_polar_density_ball {n : ℕ} {f : Domain n → ℝ}
    {a : Domain n} {R : ℝ} (hf : IntegrableOn f (ball a R)) :
    IntegrableOn (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) (Ioo (0 : ℝ) R) volume := by
  have hi : Integrable ((ball a R).indicator f) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hf
  have hp := (integrable_polar_density hi a).mono_set
    (show Ioo (0 : ℝ) R ⊆ Ioi (0 : ℝ) from fun _ h => h.1)
  apply hp.congr_fun ?_ measurableSet_Ioo
  intro r hr
  apply congrArg (fun z : ℝ => r ^ (n - 1) * z)
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => indicator_of_mem (by
    rw [mem_ball, dist_eq_norm_sub, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.1.le]
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using θ.property
    simpa only [hθ, mul_one] using hr.2) f

private theorem exists_simultaneous_le_twice_mean
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : 0 ≤ᵐ[μ] f) (hgn : 0 ≤ᵐ[μ] g)
    {P : α → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧
      f x ≤ 2 * (∫ y, f y ∂μ) / μ.real univ ∧
      g x ≤ 2 * (∫ y, g y ∂μ) / μ.real univ := by
  let A : ℝ := ∫ y, f y ∂μ
  let B : ℝ := ∫ y, g y ∂μ
  have hA : 0 ≤ A := integral_nonneg_of_ae hfn
  have hB : 0 ≤ B := integral_nonneg_of_ae hgn
  have hzf : ∀ᵐ x ∂μ, A = 0 → f x = 0 := by
    by_cases hz : A = 0
    · exact ((integral_eq_zero_iff_of_nonneg_ae hfn hf).mp hz).mono
        (fun _ hx _ => hx)
    · exact Eventually.of_forall fun _ h => (hz h).elim
  have hzg : ∀ᵐ x ∂μ, B = 0 → g x = 0 := by
    by_cases hz : B = 0
    · exact ((integral_eq_zero_iff_of_nonneg_ae hgn hg).mp hz).mono
        (fun _ hx _ => hx)
    · exact Eventually.of_forall fun _ h => (hz h).elim
  let H : α → ℝ := fun x => f x / A + g x / B
  have hH : Integrable H μ := (hf.div_const A).add (hg.div_const B)
  have hHmean : (⨍ x, H x ∂μ) ≤ 2 / μ.real univ := by
    rw [average_eq, smul_eq_mul]
    have hHint : (∫ x, H x ∂μ) ≤ 2 := by
      dsimp only [H]
      rw [integral_add (hf.div_const A) (hg.div_const B), integral_div, integral_div]
      exact (add_le_add (div_self_le_one A) (div_self_le_one B)).trans_eq (by norm_num)
    calc
      (μ.real univ)⁻¹ * (∫ x, H x ∂μ) ≤ (μ.real univ)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hHint (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = 2 / μ.real univ := by rw [div_eq_mul_inv, mul_comm]
  have hall : ∀ᵐ x ∂μ, P x ∧ 0 ≤ f x ∧ 0 ≤ g x ∧
      (A = 0 → f x = 0) ∧ (B = 0 → g x = 0) := by
    filter_upwards [hP, hfn, hgn, hzf, hzg] with x hx hfx hgx hzfx hzgx
    exact ⟨hx, hfx, hgx, hzfx, hzgx⟩
  obtain ⟨x, hx, hHx⟩ := exists_notMem_null_le_average hμ hH (ae_iff.mp hall)
  have hx' := Classical.not_not.mp hx
  refine ⟨x, hx'.1, ?_, ?_⟩
  · change f x ≤ 2 * A / μ.real univ
    by_cases hz : A = 0
    · rw [hz, hx'.2.2.2.1 hz, mul_zero, zero_div]
    · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
      have hfx : f x / A ≤ 2 / μ.real univ :=
        (le_add_of_nonneg_right (div_nonneg hx'.2.2.1 hB)).trans (hHx.trans hHmean)
      exact ((div_le_iff₀ hAp).mp hfx).trans_eq (by ring)
  · change g x ≤ 2 * B / μ.real univ
    by_cases hz : B = 0
    · rw [hz, hx'.2.2.2.2 hz, mul_zero, zero_div]
    · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
      have hgx : g x / B ≤ 2 / μ.real univ :=
        (le_add_of_nonneg_left (div_nonneg hx'.2.1 hA)).trans (hHx.trans hHmean)
      exact ((div_le_iff₀ hBp).mp hgx).trans_eq (by ring)

/-- The simultaneous radial estimate can retain any property already known
at almost every admissible radius. No pointwise property is assumed. -/
theorem exists_polar_good_radius_with_property {n : ℕ} (hn : 0 < n)
    {f g : Domain n → ℝ} {a : Domain n} {s R : ℝ}
    (hs : 0 < s) (hsR : s < R)
    (hf : IntegrableOn f (ball a R)) (hg : IntegrableOn g (ball a R))
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume.restrict (Ioo s R), P r) :
    ∃ r ∈ Ioo s R, P r ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => g (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) ≤
          2 * (∫ x in ball a R \ ball a s, f x) / (R - s) ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1, g (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) ≤
          2 * (∫ x in ball a R \ ball a s, g x) / (R - s) := by
  let μ : Measure ℝ := volume.restrict (Ioo s R)
  let F : ℝ → ℝ := fun r => r ^ (n - 1) *
    ∫ θ : sphere (0 : Domain n) 1, f (a + r • θ.val)
      ∂(volume : Measure (Domain n)).toSphere
  let G : ℝ → ℝ := fun r => r ^ (n - 1) *
    ∫ θ : sphere (0 : Domain n) 1, g (a + r • θ.val)
      ∂(volume : Measure (Domain n)).toSphere
  have hsub : Ioo s R ⊆ Ioo (0 : ℝ) R := fun _ h => ⟨hs.trans h.1, h.2⟩
  have hF : Integrable F μ :=
    (integrable_polar_density_ball (n := n) (f := f) hf).mono_set hsub
  have hG : Integrable G μ :=
    (integrable_polar_density_ball (n := n) (f := g) hg).mono_set hsub
  have hFnonneg : 0 ≤ᵐ[μ] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_nonneg (pow_nonneg (hs.trans hr.1).le _)
      (integral_nonneg fun θ => hfn (a + r • θ.val))
  have hGnonneg : 0 ≤ᵐ[μ] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_nonneg (pow_nonneg (hs.trans hr.1).le _)
      (integral_nonneg fun θ => hgn (a + r • θ.val))
  have hfslice := (ae_integrable_polar_slice_ball (n := n) (f := f) hf).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hgslice := (ae_integrable_polar_slice_ball (n := n) (f := g) hg).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hμ : μ ≠ 0 := by
    dsimp only [μ]
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (sub_pos.mpr hsR)
  have hall : ∀ᵐ r ∂μ, r ∈ Ioo s R ∧ P r ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => g (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hP, hfslice, hgslice]
      with r hr hpr hfr hgr
    exact ⟨hr, hpr, hfr, hgr⟩
  obtain ⟨r, hr, hFr, hGr⟩ :=
    exists_simultaneous_le_twice_mean hμ hF hG hFnonneg hGnonneg hall
  have hmass : μ.real univ = R - s := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le hsR.le]
  have hFint : (∫ t, F t ∂μ) = ∫ x in ball a R \ ball a s, f x := by
    rw [integral_annulus_eq_polar hn hs hsR.le (hf.mono_set sdiff_subset),
      intervalIntegral.integral_of_le hsR.le, integral_Ioc_eq_integral_Ioo]
  have hGint : (∫ t, G t ∂μ) = ∫ x in ball a R \ ball a s, g x := by
    rw [integral_annulus_eq_polar hn hs hsR.le (hg.mono_set sdiff_subset),
      intervalIntegral.integral_of_le hsR.le, integral_Ioc_eq_integral_Ioo]
  rw [hmass, hFint] at hFr
  rw [hmass, hGint] at hGr
  exact ⟨r, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hFr, hGr⟩

/-- Two actual nonnegative L1 densities admit one common angular-integrable
radius in a positive annulus, with each weighted slice at most twice its own
annular radial average. -/
theorem exists_polar_good_radius {n : ℕ} (hn : 0 < n)
    {f g : Domain n → ℝ} {a : Domain n} {s R : ℝ}
    (hs : 0 < s) (hsR : s < R)
    (hf : IntegrableOn f (ball a R)) (hg : IntegrableOn g (ball a R))
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    ∃ r ∈ Ioo s R,
      Integrable (fun θ : sphere (0 : Domain n) 1 => f (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => g (a + r • θ.val))
        (volume : Measure (Domain n)).toSphere ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) ≤
          2 * (∫ x in ball a R \ ball a s, f x) / (R - s) ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1, g (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) ≤
          2 * (∫ x in ball a R \ ball a s, g x) / (R - s) := by
  obtain ⟨r, hr, _, hfr, hgr, hFr, hGr⟩ := exists_polar_good_radius_with_property hn hs hsR hf hg
    hfn hgn (P := fun _ => True) (Eventually.of_forall fun _ => trivial)
  exact ⟨r, hr, hfr, hgr, hFr, hGr⟩

/-- Two actual locally Sobolev maps admit one radius in a positive annulus
where both HS energies and their squared separation are angular-integrable.
The combined weighted energy and weighted squared separation are each bounded
by twice their own actual annular radial average. -/
theorem exists_polar_good_radius_sobolev_pair {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain n} {u v : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv)
    {a : Domain n} {s R : ℝ} (hball : closedBall a R ⊆ Ω.val)
    (hs : 0 < s) (hsR : s < R) :
    ∃ r ∈ Ioo s R,
      Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Du (a + r • θ.val)))
        (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (Dv (a + r • θ.val)))
        (volume : Measure (Domain n)).toSphere ∧
      Integrable (fun θ : sphere (0 : Domain n) 1 =>
        ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2)
        (volume : Measure (Domain n)).toSphere ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1,
        hsNormSq (Du (a + r • θ.val)) + hsNormSq (Dv (a + r • θ.val))
          ∂(volume : Measure (Domain n)).toSphere) ≤
            2 * (∫ x in ball a R \ ball a s, hsNormSq (Du x) + hsNormSq (Dv x)) / (R - s) ∧
      r ^ (n - 1) * (∫ θ : sphere (0 : Domain n) 1,
        ‖u (a + r • θ.val) - v (a + r • θ.val)‖ ^ 2
          ∂(volume : Measure (Domain n)).toSphere) ≤
            2 * (∫ x in ball a R \ ball a s, ‖u x - v x‖ ^ 2) / (R - s) := by
  have henergy : IntegrableOn
      (fun x : Domain n => hsNormSq (Du x) + hsNormSq (Dv x)) (ball a R) volume :=
    (hu.integrable_hsNormSq_ball hball).add (hv.integrable_hsNormSq_ball hball)
  have hdiffClosed : IntegrableOn (fun x : Domain n => ‖u x - v x‖ ^ 2) (closedBall a R) :=
    ((hu.2.1 (closedBall a R) (isCompact_closedBall a R) hball).sub
      (hv.2.1 (closedBall a R) (isCompact_closedBall a R) hball)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  have hdiff : IntegrableOn (fun x : Domain n => ‖u x - v x‖ ^ 2) (ball a R) volume :=
    hdiffClosed.mono_set ball_subset_closedBall
  have hsub : Ioo s R ⊆ Ioo (0 : ℝ) R := fun _ h => ⟨hs.trans h.1, h.2⟩
  have hpair := (ae_integrable_polar_sobolev_pair (n := n) (q := q) hu hv hball).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  obtain ⟨r, hr, hpr, _, _, hFr, hGr⟩ := exists_polar_good_radius_with_property (n := n) hn
    (f := fun x : Domain n => hsNormSq (Du x) + hsNormSq (Dv x))
    (g := fun x : Domain n => ‖u x - v x‖ ^ 2) hs hsR henergy hdiff
    (fun x => add_nonneg (hsNormSq_nonneg (Du x)) (hsNormSq_nonneg (Dv x)))
    (fun x => sq_nonneg ‖u x - v x‖) hpair
  exact ⟨r, hr, hpr.1, hpr.2.1, hpr.2.2, hFr, hGr⟩

end StratificationTheory
