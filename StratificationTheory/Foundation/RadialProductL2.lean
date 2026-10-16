module

public import StratificationTheory.Foundation.AngularL2Membership
public import StratificationTheory.Foundation.PolarSlices
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import HarmonicMaps.Analysis.VariableMollificationL2
import HarmonicMaps.Analysis.RadialIntegrability

/-!
# Ambient L2 data on positive radial intervals

The native angular measure times unweighted radius volume is controlled by
the reciprocal inner-radius Jacobian. This transfers actual ambient L2
membership and strong convergence, including the normalized weak radial
columns, to every compact positive radial interval inside a ball.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

private theorem memLp_polar_product_and_norm {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    {f : Domain n → E} (hf : MemLp f p volume) (c : Domain n) :
    MemLp (fun z : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      f (c + z.2.val • z.1.val)) p
      ((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) ∧
    eLpNorm (fun z : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      f (c + z.2.val • z.1.val)) p
      ((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) =
      eLpNorm f p volume := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have ht : MemLp (fun x => f (c + x)) p volume :=
    hf.comp_measurePreserving (measurePreserving_add_left volume c)
  have hsub := measurePreserving_subtype_coe
    (measurableSet_singleton (0 : Domain n)).compl
    (μa := (volume : Measure (Domain n)))
  rw [restrict_compl_singleton] at hsub
  have hs := ht.comp_measurePreserving hsub
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  have hi := hm.symm (homeomorphUnitSphereProd (Domain n)).toMeasurableEquiv
  have hp := hs.comp_measurePreserving hi
  have hnorm := (eLpNorm_comp_measurePreserving (p := p) hs.aestronglyMeasurable hi).trans
    ((eLpNorm_comp_measurePreserving (p := p) ht.aestronglyMeasurable hsub).trans
      (eLpNorm_comp_measurePreserving (p := p) hf.aestronglyMeasurable
        (measurePreserving_add_left volume c)))
  simpa only [Function.comp_def, Homeomorph.toMeasurableEquiv_symm_coe,
    homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace,
    Fintype.card_fin] using And.intro hp hnorm

private theorem radial_unweighted_restrict_le {k : ℕ} {a b : ℝ} (ha : 0 < a) :
    (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).restrict
      (Subtype.val ⁻¹' Icc a b) ≤
      ENNReal.ofReal ((a ^ k)⁻¹) • (Measure.volumeIoiPow k).restrict
        (Subtype.val ⁻¹' Icc a b) := by
  let μ := (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).restrict
    (Subtype.val ⁻¹' Icc a b)
  have hJ : MeasurableSet (Subtype.val ⁻¹' Icc a b : Set (Ioi (0 : ℝ))) :=
    measurable_subtype_coe measurableSet_Icc
  change μ ≤ ENNReal.ofReal ((a ^ k)⁻¹) •
    ((volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).withDensity
      (fun r => ENNReal.ofReal (r.val ^ k))).restrict (Subtype.val ⁻¹' Icc a b)
  rw [restrict_withDensity hJ, ← withDensity_smul]
  · conv_lhs => rw [← withDensity_one (μ := μ)]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hJ] with r hr
    change 1 ≤ ENNReal.ofReal ((a ^ k)⁻¹) * ENNReal.ofReal (r.val ^ k)
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg ha.le k))]
    apply ENNReal.one_le_ofReal.mpr
    have hpow : a ^ k ≤ r.val ^ k := pow_le_pow_left₀ ha.le hr.1 k
    calc
      1 = (a ^ k)⁻¹ * a ^ k := (inv_mul_cancel₀ (pow_pos ha k).ne').symm
      _ ≤ (a ^ k)⁻¹ * r.val ^ k := mul_le_mul_of_nonneg_left hpow
        (inv_nonneg.mpr (pow_nonneg ha.le k))
  · exact (measurable_subtype_coe.pow_const k).ennreal_ofReal

private theorem measurePreserving_positive_radius_restrict {a b : ℝ} (ha : 0 < a) :
    MeasurePreserving (Subtype.val : Ioi (0 : ℝ) → ℝ)
      ((volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).restrict
        (Subtype.val ⁻¹' Icc a b)) (volume.restrict (Icc a b)) := by
  have h := (measurePreserving_subtype_coe (measurableSet_Ioi (a := (0 : ℝ)))
    (μa := (volume : Measure ℝ))).restrict_preimage (measurableSet_Icc (a := a) (b := b))
  have hs : Icc a b ∩ Ioi (0 : ℝ) = Icc a b :=
    inter_eq_left.mpr fun r hr => ha.trans_le hr.1
  rwa [Measure.restrict_restrict measurableSet_Icc, hs] at h

/-- Actual ambient L2 data pull back to the native sphere times any finite
positive radial interval. The reciprocal inner-radius Jacobian controls the
unweighted product norm. -/
theorem memLp_two_radial_product_ball_and_norm {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {f : Domain n → E}
    {c : Domain n} {a b R : ℝ} (ha : 0 < a) (hbR : b < R)
    (hf : MemLp f 2 (volume.restrict (ball c R))) :
    MemLp (fun z : sphere (0 : Domain n) 1 × ℝ => f (c + z.2 • z.1.val)) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))) ∧
    eLpNorm (fun z : sphere (0 : Domain n) 1 × ℝ => f (c + z.2 • z.1.val)) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))) ≤
      ENNReal.ofReal ((a ^ (n - 1))⁻¹) ^ (1 / 2 : ℝ) *
        eLpNorm f 2 (volume.restrict (ball c R)) := by
  let g := (ball c R).indicator f
  have hg : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr hf
  obtain ⟨hp, hpnorm⟩ := memLp_polar_product_and_norm hn hg c
  let J : Set (Ioi (0 : ℝ)) := Subtype.val ⁻¹' Icc a b
  let σ := (volume : Measure (Domain n)).toSphere
  have hμ : σ.prod ((volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).restrict J) ≤
      ENNReal.ofReal ((a ^ (n - 1))⁻¹) •
        σ.prod ((Measure.volumeIoiPow (n - 1)).restrict J) := by
    rw [← Measure.prod_smul_right]
    exact Measure.prod_mono le_rfl (radial_unweighted_restrict_le (k := n - 1) ha)
  have hpJ : MemLp (fun z : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      g (c + z.2.val • z.1.val)) 2
      (σ.prod ((Measure.volumeIoiPow (n - 1)).restrict J)) :=
    hp.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hu := (hpJ.smul_measure ENNReal.ofReal_ne_top).mono_measure hμ
  letI : SigmaFinite (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
    (measurePreserving_subtype_coe (measurableSet_Ioi (a := (0 : ℝ)))
      (μa := (volume : Measure ℝ))).sigmaFinite
  have hparam := (MeasurePreserving.id σ).prod
    (measurePreserving_positive_radius_restrict (b := b) ha)
  have hemb : MeasurableEmbedding
      (Prod.map (id : sphere (0 : Domain n) 1 → sphere (0 : Domain n) 1)
        (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe (measurableSet_Ioi (a := (0 : ℝ))))
  have hreal : MemLp (fun z : sphere (0 : Domain n) 1 × ℝ =>
      g (c + z.2 • z.1.val)) 2 (σ.prod (volume.restrict (Icc a b))) := by
    rw [← hparam.map_eq]
    exact hemb.memLp_map_measure_iff.mpr hu
  dsimp only [σ] at hreal
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere hn] at hreal
  have hEq : (fun z : sphere (0 : Domain n) 1 × ℝ => g (c + z.2 • z.1.val)) =ᵐ[
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))]
      (fun z => f (c + z.2 • z.1.val)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (measurableSet_Icc (a := a) (b := b)))] with z hz
    have hθ : ‖z.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.1.property
    have hdist : dist (c + z.2 • z.1.val) c = z.2 := by
      rw [dist_eq_norm_sub, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (ha.le.trans hz.1), hθ, mul_one]
    exact indicator_of_mem (by rw [mem_ball, hdist]; exact hz.2.trans_lt hbR) f
  refine ⟨hreal.ae_eq hEq, ?_⟩
  rw [← eLpNorm_congr_ae hEq]
  rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
  change eLpNorm (fun z : sphere (0 : Domain n) 1 × ℝ =>
    g (c + z.2 • z.1.val)) 2 (σ.prod (volume.restrict (Icc a b))) ≤ _
  rw [← hparam.map_eq, hemb.eLpNorm_map_measure]
  calc
    _ ≤ eLpNorm (fun z : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
        g (c + z.2.val • z.1.val)) 2
        (ENNReal.ofReal ((a ^ (n - 1))⁻¹) •
          σ.prod ((Measure.volumeIoiPow (n - 1)).restrict J)) :=
      eLpNorm_mono_measure _ hμ
    _ ≤ ENNReal.ofReal ((a ^ (n - 1))⁻¹) ^ (1 / 2 : ℝ) *
        eLpNorm (fun z : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
          g (c + z.2.val • z.1.val)) 2
          (σ.prod ((Measure.volumeIoiPow (n - 1)).restrict J)) := by
      simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
        smul_eq_mul] using eLpNorm_smul_measure_le
        (ENNReal.ofReal ((a ^ (n - 1))⁻¹))
        (fun z : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
          g (c + z.2.val • z.1.val)) 2
        (σ.prod ((Measure.volumeIoiPow (n - 1)).restrict J))
    _ ≤ ENNReal.ofReal ((a ^ (n - 1))⁻¹) ^ (1 / 2 : ℝ) *
        eLpNorm (fun z : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
          g (c + z.2.val • z.1.val)) 2
          (σ.prod (Measure.volumeIoiPow (n - 1))) :=
      mul_le_mul_right (eLpNorm_mono_measure _
        (Measure.prod_mono le_rfl Measure.restrict_le_self)) _
    _ = _ := by
      rw [hpnorm, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]


/-- Ambient L2 membership supplies the actual unweighted radial product class. -/
theorem memLp_two_radial_product_ball {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {f : Domain n → E}
    {c : Domain n} {a b R : ℝ} (ha : 0 < a) (hbR : b < R)
    (hf : MemLp f 2 (volume.restrict (ball c R))) :
    MemLp (fun z : sphere (0 : Domain n) 1 × ℝ => f (c + z.2 • z.1.val)) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))) :=
  (memLp_two_radial_product_ball_and_norm hn ha hbR hf).1

/-- Strong ambient L2 convergence gives strong convergence of the same raw
radial product representatives on every positive interior closed interval. -/
theorem tendsto_eLpNorm_two_radial_product_sub {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {f : ℕ → Domain n → E} {u : Domain n → E}
    {c : Domain n} {a b R : ℝ} (ha : 0 < a) (hbR : b < R)
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (ball c R)))
    (hu : MemLp u 2 (volume.restrict (ball c R)))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2
      (volume.restrict (ball c R))) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun z : sphere (0 : Domain n) 1 × ℝ =>
      f k (c + z.2 • z.1.val) - u (c + z.2 • z.1.val)) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Icc a b))))
      atTop (𝓝 0) := by
  have hC : ENNReal.ofReal ((a ^ (n - 1))⁻¹) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    finiteness
  have hlim := ENNReal.Tendsto.const_mul hconv (Or.inr hC)
  rw [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le)
  intro k
  exact (memLp_two_radial_product_ball_and_norm hn ha hbR ((hf k).sub hu)).2

private theorem normalized_radial_columns_aestronglyMeasurable {n q : ℕ}
    {Du : Domain n → Gradient n q} {μ : Measure (Domain n)}
    (hDu : ∀ i, MemLp (fun x => Du x i) 2 μ) (c : Domain n) :
    AEStronglyMeasurable (fun x => ‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • Du x i) μ := by
  have hs : AEStronglyMeasurable (fun x => ∑ i : Fin n, (x - c) i • Du x i) μ :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ =>
      (by fun_prop : Continuous (fun x : Domain n => (x - c) i)).aestronglyMeasurable.smul
        (hDu i).aestronglyMeasurable
  exact ((by fun_prop : Continuous (fun x : Domain n => ‖x - c‖)).aestronglyMeasurable.inv₀).smul hs

/-- The actual weak columns evaluated in the radial unit direction are L2;
no value of an arbitrary ambient gradient on a surface is used. -/
theorem memLp_two_normalized_radial_columns {n q : ℕ}
    {Du : Domain n → Gradient n q} {μ : Measure (Domain n)}
    (hDu : ∀ i, MemLp (fun x => Du x i) 2 μ) (c : Domain n) :
    MemLp (fun x => ‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • Du x i) 2 μ :=
  (memLp_two_iff_integrable_sq_norm
    (normalized_radial_columns_aestronglyMeasurable hDu c)).mpr
      (integrable_radial_columns_of_memLp hDu c)

/-- Strong convergence of the original weak columns controls their actual
normalized radial sums in the same ambient L2 space. -/
theorem tendsto_eLpNorm_two_normalized_radial_columns_sub {n q : ℕ}
    {μ : Measure (Domain n)} {D : ℕ → Domain n → Gradient n q}
    {Du : Domain n → Gradient n q}
    (hD : ∀ k i, MemLp (fun x => D k x i) 2 μ)
    (hDu : ∀ i, MemLp (fun x => Du x i) 2 μ)
    (hconv : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i - Du x i) 2 μ)
      atTop (𝓝 0)) (c : Domain n) :
    Tendsto (fun k => eLpNorm (fun x =>
      (‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • D k x i) -
      (‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • Du x i)) 2 μ)
      atTop (𝓝 0) := by
  let V : ℕ → Domain n → Gradient n q := fun k x i => D k x i - Du x i
  have hV (k : ℕ) (i : Fin n) : MemLp (fun x => V k x i) 2 μ :=
    (hD k i).sub (hDu i)
  have htotal := tendsto_integral_hsNormSq_zero hV hconv
  have hradial : Tendsto (fun k => ∫ x, ‖‖x - c‖⁻¹ •
      ∑ i : Fin n, (x - c) i • V k x i‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun k => integral_mono_ae (integrable_radial_columns_of_memLp (hV k) c)
        (integrable_hsNormSq_of_memLp_columns (hV k))
        (Eventually.of_forall fun x => norm_sq_radial_columns_le (V k x) (x - c))) htotal
  have heq (k : ℕ) : (fun x => ‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • V k x i) =
      (fun x => (‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • D k x i) -
        (‖x - c‖⁻¹ • ∑ i : Fin n, (x - c) i • Du x i)) := by
    funext x
    simp only [V, smul_sub, Finset.sum_sub_distrib]
  have hnorm := tendsto_eLpNorm_two_zero_of_integral_norm_sq
    (fun k => memLp_two_normalized_radial_columns (hV k) c) hradial
  simpa only [heq] using hnorm

end StratificationTheory
