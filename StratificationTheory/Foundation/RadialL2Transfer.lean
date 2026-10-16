module

public import StratificationTheory.Foundation.AngularL2Membership
public import StratificationTheory.Foundation.SphericalProjectionDifferential
public import HarmonicMaps.Analysis.VariableMollificationL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Angular L2 transfer to Euclidean radial extensions

Actual polar coordinates transfer angular L2 data to finite Euclidean balls.
The volume factor is the integral of the true radial Jacobian. On collars
bounded away from zero, reciprocal-radius multiplication preserves L2.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators

namespace StratificationTheory

/-- The exact L2 volume factor for a degree-zero radial function is obtained
from the actual polar Jacobian, including its dimensional normalization. -/
theorem memLp_two_radial_ball_and_norm {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E]
    {v : sphere (0 : Domain n) 1 → E}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    {w : Domain n → E}
    (hRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      w (ρ.val • θ.val) = v θ)
    {R : ℝ} (hR : 0 < R) :
    MemLp w 2 (volume.restrict (ball (0 : Domain n) R)) ∧
      eLpNorm w 2 (volume.restrict (ball (0 : Domain n) R)) =
        (ENNReal.ofReal (R ^ n / n)) ^ (1 / 2 : ℝ) *
          eLpNorm v 2 (volume : Measure (Domain n)).toSphere := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let X := ({(0 : Domain n)}ᶜ : Set (Domain n))
  let σ := (volume : Measure (Domain n)).toSphere
  let ν := Measure.volumeIoiPow (n - 1)
  let J := Iio (⟨R, hR⟩ : Ioi (0 : ℝ))
  let νR := ν.restrict J
  have hνmass : νR univ = ENNReal.ofReal (R ^ n / n) := by
    simp only [νR, Measure.restrict_apply_univ, ν, J, Measure.volumeIoiPow_apply_Iio]
    have hd : n - 1 + 1 = n := by omega
    have hdreal : (n - 1 : ℕ) + 1 = (n : ℝ) := by exact_mod_cast hd
    rw [hd, hdreal]
  letI : IsFiniteMeasure νR := ⟨by rw [hνmass]; exact ENNReal.ofReal_lt_top⟩
  have hprod : MemLp (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) => v p.1)
      2 (σ.prod νR) := hv.comp_fst νR
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hm
  have hmR := hm.restrict_preimage (MeasurableSet.univ.prod (measurableSet_Iio
    (a := (⟨R, hR⟩ : Ioi (0 : ℝ)))))
  have hpre : (homeomorphUnitSphereProd (Domain n)) ⁻¹'
      (univ ×ˢ J) = (Subtype.val : X → Domain n) ⁻¹' ball 0 R := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, true_and, J, mem_Iio,
      mem_ball, dist_zero_right]
    change ((homeomorphUnitSphereProd (Domain n) x).2.val < R) ↔ ‖x.val‖ < R
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  rw [hpre, ← Measure.prod_restrict] at hmR
  simp only [Measure.restrict_univ] at hmR
  have heq : (fun x : X => w x.val) =
      (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) => v p.1) ∘
        homeomorphUnitSphereProd (Domain n) := by
    funext x
    let p := homeomorphUnitSphereProd (Domain n) x
    have hp : p.2.val • p.1.val = x.val := by
      have he := congrArg (fun z : X => z.val)
        ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply x)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using he
    change w x.val = v p.1
    rw [← hp]
    exact hRay ⟨p.2.val, p.2.property⟩ p.1
  have hwSub : MemLp (fun x : X => w x.val) 2
      ((volume : Measure (Domain n)).comap (Subtype.val : X → Domain n) |>.restrict
        ((Subtype.val : X → Domain n) ⁻¹' ball 0 R)) := by
    rw [heq]
    exact hprod.comp_measurePreserving hmR
  have hc := (measurePreserving_subtype_coe
    ((measurableSet_singleton (0 : Domain n)).compl) (μa := volume)).restrict_preimage
      (measurableSet_ball (x := (0 : Domain n)) (ε := R))
  rw [restrict_compl_singleton] at hc
  have hw : MemLp w 2 (volume.restrict (ball (0 : Domain n) R)) := by
    rw [← hc.map_eq]
    exact (MeasurableEmbedding.subtype_coe
      ((measurableSet_singleton (0 : Domain n)).compl)).memLp_map_measure_iff.mpr hwSub
  refine ⟨hw, ?_⟩
  have hσ : MemLp v 2 (νR univ • σ) := hv.smul_measure (by rw [hνmass]; finiteness)
  have hnormProd : eLpNorm
      (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) => v p.1) 2 (σ.prod νR) =
        νR univ ^ (1 / 2 : ℝ) * eLpNorm v 2 σ := by
    have hmap : AEStronglyMeasurable v (Measure.map Prod.fst (σ.prod νR)) := by
      rw [Measure.map_fst_prod]
      exact hσ.aestronglyMeasurable
    change eLpNorm (v ∘ Prod.fst) 2 (σ.prod νR) = _
    rw [← eLpNorm_map_measure hmap measurable_fst.aemeasurable,
      Measure.map_fst_prod, eLpNorm_smul_measure_of_ne_top (by norm_num)]
    norm_num
  calc
    eLpNorm w 2 (volume.restrict (ball (0 : Domain n) R)) =
        eLpNorm (fun x : X => w x.val) 2
          ((volume : Measure (Domain n)).comap (Subtype.val : X → Domain n) |>.restrict
            ((Subtype.val : X → Domain n) ⁻¹' ball 0 R)) :=
      (eLpNorm_comp_measurePreserving hw.aestronglyMeasurable hc).symm
    _ = eLpNorm (fun p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) => v p.1)
        2 (σ.prod νR) := by
      rw [heq]
      exact eLpNorm_comp_measurePreserving hprod.aestronglyMeasurable hmR
    _ = _ := by rw [hnormProd, hνmass]

/-- Angular L2 data give actual L2 data on every finite radial collar, with
the ball Jacobian factor as a quantitative upper bound. -/
theorem memLp_two_radial_collar_and_norm {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E]
    {v : sphere (0 : Domain n) 1 → E}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    {w : Domain n → E}
    (hRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      w (ρ.val • θ.val) = v θ)
    (ε : ℝ) {R : ℝ} (hR : 0 < R) :
    MemLp w 2 (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) ∧
      eLpNorm w 2 (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) ≤
        (ENNReal.ofReal (R ^ n / n)) ^ (1 / 2 : ℝ) *
          eLpNorm v 2 (volume : Measure (Domain n)).toSphere := by
  have hsub : {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R} ⊆ ball 0 R := by
    intro x hx
    simpa only [mem_ball, dist_zero_right] using hx.2
  have h := memLp_two_radial_ball_and_norm hn hv hRay hR
  exact ⟨h.1.mono_measure (Measure.restrict_mono_set volume hsub),
    (eLpNorm_mono_measure w (Measure.restrict_mono_set volume hsub)).trans_eq h.2⟩

private theorem radial_collar_measurableSet {n : ℕ} (ε R : ℝ) :
    MeasurableSet {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R} :=
  (isOpen_Ioo.preimage continuous_norm).measurableSet

private theorem memLp_top_inverse_norm_collar {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (R : ℝ) :
    MemLp (fun x : Domain n => ‖x‖⁻¹) ∞
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) := by
  have hc : ContinuousOn (fun x : Domain n => ‖x‖⁻¹)
      {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R} :=
    continuous_norm.continuousOn.inv₀
      (fun x hx => (hε.trans hx.1).ne')
  apply memLp_top_of_bound
    (hc.aestronglyMeasurable (radial_collar_measurableSet ε R)) ε⁻¹
  filter_upwards [ae_restrict_mem (radial_collar_measurableSet (n := n) ε R)] with x hx
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact (inv_le_inv₀ (hε.trans hx.1) hε).mpr hx.1.le

/-- A reciprocal-radius radial function has actual collar L2 membership and
the explicit angular L2 bound. Its ray formula is actual function data; no
weak-gradient or sphere-Sobolev conclusion is assumed. -/
theorem memLp_two_weighted_radial_collar_and_norm {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : sphere (0 : Domain n) 1 → E}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    {W : Domain n → E} (r : ℝ)
    (hRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      W (ρ.val • θ.val) = (r / ρ.val) • v θ)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    MemLp W 2 (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) ∧
      eLpNorm W 2 (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) ≤
        ENNReal.ofReal (|r| / ε) * (ENNReal.ofReal (R ^ n / n)) ^ (1 / 2 : ℝ) *
          eLpNorm v 2 (volume : Measure (Domain n)).toSphere := by
  let z : Domain n → E := fun x => ‖x‖ • W x
  have hzRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      z (ρ.val • θ.val) = r • v θ := by
    intro ρ θ
    have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    simp only [z, hRay, norm_smul, Real.norm_of_nonneg ρ.property.le,
      hθ, mul_one, smul_smul]
    rw [mul_div_cancel₀ r ρ.property.ne']
  have hz := memLp_two_radial_collar_and_norm hn (hv.const_smul r) hzRay ε hR
  have hInv := memLp_top_inverse_norm_collar (n := n) hε R
  have hiLp : MemLp (fun x : Domain n => ‖x‖⁻¹ • z x) 2
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) := hz.1.smul (r := 2) hInv
  have heq : W =ᵐ[volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}]
      (fun x : Domain n => ‖x‖⁻¹ • z x) := by
    filter_upwards [ae_restrict_mem (radial_collar_measurableSet (n := n) ε R)] with x hx
    simp only [z, smul_smul, inv_mul_cancel₀ (hε.trans hx.1).ne', one_smul]
  refine ⟨hiLp.ae_eq heq.symm, ?_⟩
  have hb : eLpNorm (fun x : Domain n => ‖x‖⁻¹ • z x) 2
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) ≤
        ENNReal.ofReal ε⁻¹ * eLpNorm z 2
          (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
    filter_upwards [ae_restrict_mem (radial_collar_measurableSet (n := n) ε R)] with x hx
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ (hε.trans hx.1) hε).mpr hx.1.le) (norm_nonneg _)
  rw [eLpNorm_congr_ae heq]
  calc
    _ ≤ ENNReal.ofReal ε⁻¹ * eLpNorm z 2
        (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) := hb
    _ ≤ ENNReal.ofReal ε⁻¹ *
        ((ENNReal.ofReal (R ^ n / n)) ^ (1 / 2 : ℝ) *
          eLpNorm (r • v) 2 (volume : Measure (Domain n)).toSphere) :=
      mul_le_mul_right hz.2 _
    _ = _ := by
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs]
      simp only [div_eq_mul_inv, ENNReal.ofReal_mul (abs_nonneg r)]
      ac_rfl

/-- The actual tangential projection respects subtraction of displayed
ambient column families. -/
theorem tangentialColumns_sub {n q : ℕ} (θ : sphere (0 : Domain n) 1)
    (A B : Gradient n q) :
    tangentialColumns θ (A - B) = tangentialColumns θ A - tangentialColumns θ B := by
  funext i
  simp only [tangentialColumns, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
  abel

/-- Actual angular L2 membership of all ambient columns gives angular L2
membership of each tangentially projected column. -/
theorem memLp_two_tangential_column {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ j : Fin n, MemLp (fun θ => A θ j) 2 (volume : Measure (Domain n)).toSphere)
    (i : Fin n) :
    MemLp (fun θ => tangentialColumns θ (A θ) i) 2
      (volume : Measure (Domain n)).toSphere := by
  have hC (j : Fin n) : MemLp (fun θ : sphere (0 : Domain n) 1 => θ.val j) ∞
      (volume : Measure (Domain n)).toSphere := by
    have hc : Continuous (fun θ : sphere (0 : Domain n) 1 => θ.val j) :=
      (EuclideanSpace.proj j).continuous.comp continuous_subtype_val
    exact hc.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (volume : Measure (Domain n)).toSphere
  have hsum : MemLp (fun θ : sphere (0 : Domain n) 1 => ∑ j : Fin n, θ.val j • A θ j)
      2 (volume : Measure (Domain n)).toSphere :=
    memLp_finsetSum Finset.univ (fun j _ => (hA j).smul (r := 2) (hC j))
  exact (hA i).sub (hsum.smul (r := 2) (hC i))

/-- The squared L2 norm of one actual projected column is bounded by the
sum of the actual ambient-column squared L2 norms. -/
theorem integral_tangential_column_sq_le {n q : ℕ}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ j : Fin n, MemLp (fun θ => A θ j) 2 (volume : Measure (Domain n)).toSphere)
    (i : Fin n) :
    (∫ θ : sphere (0 : Domain n) 1, ‖tangentialColumns θ (A θ) i‖ ^ 2
      ∂(volume : Measure (Domain n)).toSphere) ≤
        ∑ j : Fin n, ∫ θ : sphere (0 : Domain n) 1, ‖A θ j‖ ^ 2
          ∂(volume : Measure (Domain n)).toSphere := by
  have hi (j : Fin n) : Integrable (fun θ : sphere (0 : Domain n) 1 => ‖A θ j‖ ^ 2)
      (volume : Measure (Domain n)).toSphere :=
    (hA j).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hInt : Integrable (fun θ : sphere (0 : Domain n) 1 => hsNormSq (A θ))
      (volume : Measure (Domain n)).toSphere :=
    integrable_finsetSum Finset.univ (fun j _ => hi j)
  rw [← integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply integral_mono
    ((memLp_two_tangential_column hA i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) hInt
  intro θ
  have hc : ‖tangentialColumns θ (A θ) i‖ ^ 2 ≤ hsNormSq (tangentialColumns θ (A θ)) := by
    change ‖tangentialColumns θ (A θ) i‖ ^ 2 ≤
      ∑ j : Fin n, ‖tangentialColumns θ (A θ) j‖ ^ 2
    exact Finset.single_le_sum (f := fun j : Fin n => ‖tangentialColumns θ (A θ) j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact hc.trans (hsNormSq_tangentialColumns_le θ (A θ))

/-- Vanishing actual angular square errors in every ambient column give
strong angular L2 convergence of every actual projected column. -/
theorem tendsto_eLpNorm_tangential_column_zero {n q : ℕ}
    {A : ℕ → sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ k (j : Fin n), MemLp (fun θ => A k θ j) 2
      (volume : Measure (Domain n)).toSphere)
    (hconv : ∀ j : Fin n, Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
      ‖A k θ j‖ ^ 2 ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0))
    (i : Fin n) :
    Tendsto (fun k => eLpNorm (fun θ => tangentialColumns θ (A k θ) i) 2
      (volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
  have htotal : Tendsto (fun k => ∑ j : Fin n,
      ∫ θ : sphere (0 : Domain n) 1, ‖A k θ j‖ ^ 2
        ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun j _ => hconv j)
  have hproj : Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
      ‖tangentialColumns θ (A k θ) i‖ ^ 2 ∂(volume : Measure (Domain n)).toSphere)
        atTop (𝓝 0) :=
    squeeze_zero (fun k => integral_nonneg fun θ => sq_nonneg _)
      (fun k => integral_tangential_column_sq_le (hA k) i) htotal
  exact tendsto_eLpNorm_two_zero_of_integral_norm_sq
    (fun k => memLp_two_tangential_column (hA k) i) hproj

/-- Vanishing actual angular L2 data give vanishing actual degree-zero
radial L2 data on a finite collar. -/
theorem tendsto_eLpNorm_radial_collar_zero {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E]
    {v : ℕ → sphere (0 : Domain n) 1 → E}
    (hv : ∀ k, MemLp (v k) 2 (volume : Measure (Domain n)).toSphere)
    (hconv : Tendsto (fun k => eLpNorm (v k) 2
      (volume : Measure (Domain n)).toSphere) atTop (𝓝 0))
    {w : ℕ → Domain n → E}
    (hRay : ∀ k (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      w k (ρ.val • θ.val) = v k θ)
    (ε : ℝ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun k => eLpNorm (w k) 2
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R})) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := (ENNReal.ofReal (R ^ n / n)) ^ (1 / 2 : ℝ)
  have hC : C ≠ ⊤ := by dsimp [C]; finiteness
  have ht : Tendsto (fun k => C * eLpNorm (v k) 2
      (volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hconv (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) (fun k => (memLp_two_radial_collar_and_norm hn (hv k) (hRay k) ε hR).2)

/-- Vanishing actual angular L2 data give vanishing actual reciprocal-radius
radial L2 data on every collar bounded away from the origin. -/
theorem tendsto_eLpNorm_weighted_radial_collar_zero {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → sphere (0 : Domain n) 1 → E}
    (hv : ∀ k, MemLp (v k) 2 (volume : Measure (Domain n)).toSphere)
    (hconv : Tendsto (fun k => eLpNorm (v k) 2
      (volume : Measure (Domain n)).toSphere) atTop (𝓝 0))
    {W : ℕ → Domain n → E} (r : ℝ)
    (hRay : ∀ k (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      W k (ρ.val • θ.val) = (r / ρ.val) • v k θ)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    Tendsto (fun k => eLpNorm (W k) 2
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R})) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (|r| / ε) * (ENNReal.ofReal (R ^ n / n)) ^ (1 / 2 : ℝ)
  have hC : C ≠ ⊤ := by dsimp [C]; finiteness
  have ht : Tendsto (fun k => C * eLpNorm (v k) 2
      (volume : Measure (Domain n)).toSphere) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hconv (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le)
    (fun k => (memLp_two_weighted_radial_collar_and_norm hn (hv k) r (hRay k) hε hR).2)

/-- Actual angular ambient-column L2 data produce actual finite collar L2
data for columns with the literal reciprocal-radius tangential ray formula. -/
theorem memLp_two_tangential_radial_columns {n q : ℕ} (hn : 0 < n)
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2 (volume : Measure (Domain n)).toSphere)
    {D : Domain n → Gradient n q} (r : ℝ)
    (hRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D (ρ.val • θ.val) i = (r / ρ.val) • tangentialColumns θ (A θ) i)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (i : Fin n) :
    MemLp (fun x => D x i) 2
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R}) :=
  (memLp_two_weighted_radial_collar_and_norm hn (memLp_two_tangential_column hA i)
    r (fun ρ θ => hRay ρ θ i) hε hR).1

/-- Actual angular ambient-column square errors control the actual collar
L2 errors of the corresponding reciprocal-radius tangential columns. -/
theorem tendsto_eLpNorm_tangential_radial_column_error_zero {n q : ℕ} (hn : 0 < n)
    {A : ℕ → sphere (0 : Domain n) 1 → Gradient n q}
    {B : sphere (0 : Domain n) 1 → Gradient n q}
    (hA : ∀ k (j : Fin n), MemLp (fun θ => A k θ j) 2
      (volume : Measure (Domain n)).toSphere)
    (hB : ∀ j : Fin n, MemLp (fun θ => B θ j) 2 (volume : Measure (Domain n)).toSphere)
    (hconv : ∀ j : Fin n, Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
      ‖A k θ j - B θ j‖ ^ 2 ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0))
    {D : ℕ → Domain n → Gradient n q} {DB : Domain n → Gradient n q} (r : ℝ)
    (hD : ∀ k (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D k (ρ.val • θ.val) i = (r / ρ.val) • tangentialColumns θ (A k θ) i)
    (hDB : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      DB (ρ.val • θ.val) i = (r / ρ.val) • tangentialColumns θ (B θ) i)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (i : Fin n) :
    Tendsto (fun k => eLpNorm (fun x => D k x i - DB x i) 2
      (volume.restrict {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R})) atTop (𝓝 0) := by
  let E : ℕ → sphere (0 : Domain n) 1 → Gradient n q := fun k θ => A k θ - B θ
  have hE (k : ℕ) (j : Fin n) : MemLp (fun θ => E k θ j) 2
      (volume : Measure (Domain n)).toSphere := (hA k j).sub (hB j)
  have hlim := tendsto_eLpNorm_tangential_column_zero hE hconv i
  apply tendsto_eLpNorm_weighted_radial_collar_zero hn
    (fun k => memLp_two_tangential_column (hE k) i) hlim r ?_ hε hR
  intro k ρ θ
  rw [hD k ρ θ i, hDB ρ θ i]
  change (r / ρ.val) • tangentialColumns θ (A k θ) i -
    (r / ρ.val) • tangentialColumns θ (B θ) i =
      (r / ρ.val) • tangentialColumns θ (A k θ - B θ) i
  rw [tangentialColumns_sub, Pi.sub_apply, smul_sub]

end StratificationTheory
