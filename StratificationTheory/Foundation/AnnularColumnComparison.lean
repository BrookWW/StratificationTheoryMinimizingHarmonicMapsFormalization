module

public import StratificationTheory.Foundation.AnnularCylinderEnergy
public import StratificationTheory.Foundation.AnnularGradientEnergy
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Actual annular energy of native tangential and temporal columns

An almost-everywhere formula for the original field gives its L2 columns and
an integral comparison on the actual annulus. The factor is the upper annular
Jacobian times the square of the larger reciprocal spatial or temporal scale.
No weak-gradient conclusion is imposed on an arbitrary input column field.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal BigOperators
namespace StratificationTheory

theorem annular_column_energy_le_of_native_formula {n q : ℕ} (hn : 0 < n)
    {s a b : ℝ} (hs : 0 < s) (ha : -1 < a) (hab : a < b)
    (D : Domain n → Gradient n q)
    (A : sphere (0 : Domain n) 1 × ℝ → Gradient n q)
    (B : sphere (0 : Domain n) 1 × ℝ → Ambient q) :
    let μ := (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Ioo a b))
    let V := {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}
    let C := max (s * (1 + a))⁻¹ s⁻¹
    (∀ i : Fin n, MemLp (fun p => A p i) 2 μ) → MemLp B 2 μ →
    (∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
      D ((s * (1 + p.2)) • p.1.val) =
        fun i => (s * (1 + p.2))⁻¹ • tangentialColumns p.1 (A p) i +
          (s⁻¹ * p.1.val i) • B p) →
    (∀ i : Fin n, MemLp (fun x => D x i) 2 (volume.restrict V)) ∧
      Integrable (fun x => hsNormSq (D x)) (volume.restrict V) ∧
      (∫ x in V, hsNormSq (D x)) ≤
        (s * (s * (1 + b)) ^ (n - 1)) * C ^ 2 *
          ∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (A p) + ‖B p‖ ^ 2 ∂μ := by
  intro μ V C hA hB hFormula
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have htime : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ, p.2 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  have hlo : 0 < s * (1 + a) := mul_pos hs (by linarith only [ha])
  have hinv : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => (s * (1 + p.2))⁻¹) ∞ μ := by
    have hcont : Continuous (fun p : sphere (0 : Domain n) 1 × ℝ => s * (1 + p.2)) := by fun_prop
    apply memLp_top_of_bound hcont.aestronglyMeasurable.inv₀ ((s * (1 + a))⁻¹)
    filter_upwards [htime] with p hp
    have hrad : 0 < s * (1 + p.2) := mul_pos hs (by linarith only [ha, hp.1])
    change ‖(s * (1 + p.2))⁻¹‖ ≤ (s * (1 + a))⁻¹
    rw [norm_inv, Real.norm_of_nonneg hrad.le]
    exact (inv_le_inv₀ hrad hlo).mpr (mul_le_mul_of_nonneg_left (by linarith only [hp.1]) hs.le)
  have hθ (i : Fin n) : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => p.1.val i) ∞ μ := by
    apply memLp_top_of_bound (by fun_prop) 1
    exact ae_of_all _ fun p =>
      (PiLp.norm_apply_le p.1.val i).trans_eq (mem_sphere_zero_iff_norm.mp p.1.property)
  have hsum : MemLp (fun p => ∑ j : Fin n, p.1.val j • A p j) 2 μ :=
    memLp_finsetSum Finset.univ fun j _ => (hA j).smul (hθ j)
  have htang (i : Fin n) : MemLp (fun p => tangentialColumns p.1 (A p) i) 2 μ :=
    (hA i).sub (hsum.smul (hθ i))
  have hθS (i : Fin n) : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => s⁻¹ * p.1.val i) ∞ μ := by
    exact (hθ i).const_mul s⁻¹
  have hDL (i : Fin n) : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
      D ((s * (1 + p.2)) • p.1.val) i) 2 μ := by
    have hL : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
        (s * (1 + p.2))⁻¹ • tangentialColumns p.1 (A p) i + (s⁻¹ * p.1.val i) • B p) 2 μ :=
      ((htang i).smul hinv).add (hB.smul (hθS i))
    apply hL.ae_eq
    filter_upwards [hFormula] with p hp
    exact (congrFun hp i).symm
  have hI (i : Fin n) : Integrable (fun p : sphere (0 : Domain n) 1 × ℝ =>
      ‖D ((s * (1 + p.2)) • p.1.val) i‖ ^ 2) μ :=
    (hDL i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hIntD : Integrable (fun p : sphere (0 : Domain n) 1 × ℝ =>
      hsNormSq (D ((s * (1 + p.2)) • p.1.val))) μ :=
    integrable_finsetSum Finset.univ fun i _ => hI i
  have hIntAB : Integrable (fun p : sphere (0 : Domain n) 1 × ℝ =>
      hsNormSq (A p) + ‖B p‖ ^ 2) μ :=
    (integrable_finsetSum Finset.univ fun i _ =>
      (hA i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).add
        (hB.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hPoint : (fun p : sphere (0 : Domain n) 1 × ℝ =>
      hsNormSq (D ((s * (1 + p.2)) • p.1.val))) ≤ᵐ[μ]
      (fun p => C ^ 2 * (hsNormSq (A p) + ‖B p‖ ^ 2)) := by
    filter_upwards [hFormula, htime] with p hp ht
    have hrad : 0 < s * (1 + p.2) := mul_pos hs (by linarith only [ha, ht.1])
    have hrec : (s * (1 + p.2))⁻¹ ≤ C :=
      ((inv_le_inv₀ hrad hlo).mpr
        (mul_le_mul_of_nonneg_left (by linarith only [ht.1]) hs.le)).trans (le_max_left _ _)
    have hr2 := pow_le_pow_left₀ (inv_nonneg.mpr hrad.le) hrec 2
    have hs2 := pow_le_pow_left₀ (inv_nonneg.mpr hs.le) (le_max_right (s * (1 + a))⁻¹ s⁻¹) 2
    rw [hp]
    calc
      _ ≤ ((s * (1 + p.2))⁻¹) ^ 2 * hsNormSq (A p) + (s⁻¹) ^ 2 * ‖B p‖ ^ 2 := by
        simpa only [mul_smul] using
          hsNormSq_annular_columns_le p.1 (A p) (B p) (s * (1 + p.2))⁻¹ s⁻¹
      _ ≤ C ^ 2 * hsNormSq (A p) + C ^ 2 * ‖B p‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hr2 (hsNormSq_nonneg _))
          (mul_le_mul_of_nonneg_right hs2 (sq_nonneg _))
      _ = _ := (mul_add _ _ _).symm
  have hNativeBound : (∫ p : sphere (0 : Domain n) 1 × ℝ,
      hsNormSq (D ((s * (1 + p.2)) • p.1.val)) ∂μ) ≤
      C ^ 2 * ∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (A p) + ‖B p‖ ^ 2 ∂μ := by
    calc
      _ ≤ ∫ p : sphere (0 : Domain n) 1 × ℝ,
          C ^ 2 * (hsNormSq (A p) + ‖B p‖ ^ 2) ∂μ :=
        integral_mono_ae hIntD (hIntAB.const_mul (C ^ 2)) hPoint
      _ = _ := integral_const_mul _ _
  have htransfer := annular_column_energy_of_cylinder_pullback hn hs ha hab D hDL
  refine ⟨htransfer.1, htransfer.2.1, ?_⟩
  have hhi : 0 < s * (1 + b) := mul_pos hs (by linarith only [ha, hab])
  calc
    _ ≤ (s * (s * (1 + b)) ^ (n - 1)) *
        ∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (D ((s * (1 + p.2)) • p.1.val)) ∂μ :=
      htransfer.2.2
    _ ≤ (s * (s * (1 + b)) ^ (n - 1)) *
        (C ^ 2 * ∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (A p) + ‖B p‖ ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hNativeBound (mul_nonneg hs.le (pow_nonneg hhi.le _))
    _ = _ := by ring

end StratificationTheory
