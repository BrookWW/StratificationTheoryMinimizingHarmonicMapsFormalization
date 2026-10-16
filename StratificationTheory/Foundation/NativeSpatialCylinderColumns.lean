module

public import StratificationTheory.Foundation.NativeSpatialRadialDifferential
public import StratificationTheory.Foundation.CoherentCylinderGradientEnergy

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

private theorem native_split_symm_spatial_apply {n : ℕ} (v : Domain n) (t : Domain 1) (i : Fin n) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm (v, t) (Fin.castAdd 1 i) = v i := by
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd, PiLp.sumPiLpEquivProdLpPiLp]
  rfl

private theorem native_split_symm_time_apply {n : ℕ} (v : Domain n) (t : Domain 1) (i : Fin 1) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm (v, t) (Fin.natAdd n i) = t i := by
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd, PiLp.sumPiLpEquivProdLpPiLp]
  rfl

private theorem sum_tangential_matrix {n q : ℕ} (θ : sphere (0 : Domain n) 1)
    (A : Gradient n q) (h : ℝ) (i : Fin n) :
    (∑ j : Fin n, ((h • ((EuclideanSpace.single i (1 : ℝ) : Domain n) - θ.val i • θ.val) : Domain n) j) • A j) =
      h • tangentialColumns θ A i := by
  calc
    _ = h • (∑ j : Fin n, (((EuclideanSpace.single i (1 : ℝ) : Domain n) - θ.val i • θ.val) j) • A j) := by
      simp only [Finset.smul_sum, PiLp.smul_apply, smul_eq_mul, mul_smul]
    _ = _ := by
      congr 1
      simp only [tangentialColumns, PiLp.sub_apply, PiLp.smul_apply,
        PiLp.single_apply, smul_eq_mul, sub_smul, mul_smul]
      rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
      simp

/-- The same literal radial weak columns are coherent with the actual
native tangential spatial columns and the original independent-time column. -/
theorem native_spatial_radial_chain_columns {n q : ℕ} {a b : ℝ}
    (r : ℝ) (DW : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let X : unitCylinder n a b → Domain (n + 1) := fun c => e.symm (r • (e c.val).1, (e c.val).2)
    let F : Domain (n + 1) → Domain (n + 1) := fun y => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y i => ∑ j : Fin (n + 1),
      (fderiv ℝ F y (EuclideanSpace.single i 1)) j • DW (F y) j
    let g : unitCylinder n a b → Gradient (n + 1) q := fun c => Fin.addCases
      (fun i : Fin n => r • tangentialColumns ⟨(e c.val).1, c.property.1⟩
        (fun j => DW (X c) (Fin.castAdd 1 j)) i)
      (fun _ : Fin 1 => DW (X c) (Fin.natAdd n (0 : Fin 1)))
    ∀ (ρ : ℝ), 0 < ρ → ∀ c : unitCylinder n a b,
      (∀ i : Fin n, D (e.symm (ρ • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
        ρ⁻¹ • g c (Fin.castAdd 1 i)) ∧
      D (e.symm (ρ • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
        g c (Fin.natAdd n (0 : Fin 1)) := by
  intro e X F D g ρ hρ c
  have hLeft (v : Domain n) (t : Domain 1) (i : Fin n) :
      e.symm (v, t) (Fin.castAdd 1 i) = v i := native_split_symm_spatial_apply v t i
  have hRight (v : Domain n) (t : Domain 1) (i : Fin 1) :
      e.symm (v, t) (Fin.natAdd n i) = t i := native_split_symm_time_apply v t i
  have hDF := fderiv_native_spatial_radial_chart_columns r hρ c
  have hRay : F (e.symm (ρ • (e c.val).1, (e c.val).2)) = X c :=
    native_spatial_radial_chart_ray_value r hρ c
  constructor
  · intro i
    change (∑ j : Fin (n + 1),
      (fderiv ℝ F (e.symm (ρ • (e c.val).1, (e c.val).2))
        (EuclideanSpace.single (Fin.castAdd 1 i) 1)) j •
          DW (F (e.symm (ρ • (e c.val).1, (e c.val).2))) j) = _
    have hDFi : fderiv ℝ F (e.symm (ρ • (e c.val).1, (e c.val).2))
        (EuclideanSpace.single (Fin.castAdd 1 i) 1) =
      e.symm ((r / ρ) • (EuclideanSpace.single i 1 - (e c.val).1 i • (e c.val).1), 0) := hDF.1 i
    rw [hDFi, hRay, Fin.sum_univ_add, Fin.sum_univ_one]
    simp only [hLeft, hRight, PiLp.zero_apply]
    change (∑ j : Fin n,
      (((r / ρ) • ((EuclideanSpace.single i (1 : ℝ) : Domain n) - (e c.val).1 i • (e c.val).1) : Domain n) j) •
        DW (X c) (Fin.castAdd 1 j)) + (0 : ℝ) • DW (X c) (Fin.natAdd n (0 : Fin 1)) = _
    rw [zero_smul, add_zero, sum_tangential_matrix ⟨(e c.val).1, c.property.1⟩
      (fun j => DW (X c) (Fin.castAdd 1 j)) (r / ρ) i]
    simp only [g, Fin.addCases_left, smul_smul, div_eq_mul_inv, mul_comm]
  · change (∑ j : Fin (n + 1),
      (fderiv ℝ F (e.symm (ρ • (e c.val).1, (e c.val).2))
        (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1)) j •
          DW (F (e.symm (ρ • (e c.val).1, (e c.val).2))) j) = _
    have hDFt : fderiv ℝ F (e.symm (ρ • (e c.val).1, (e c.val).2))
        (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) =
      e.symm (0, EuclideanSpace.single (0 : Fin 1) 1) := hDF.2
    rw [hDFt, hRay, Fin.sum_univ_add, Fin.sum_univ_one]
    simp only [hLeft, hRight, PiLp.zero_apply, PiLp.single_apply, ite_true]
    change (∑ j : Fin n, (0 : ℝ) • DW (X c) (Fin.castAdd 1 j)) +
      (1 : ℝ) • DW (X c) (Fin.natAdd n (0 : Fin 1)) = _
    simp only [zero_smul, Finset.sum_const_zero, one_smul, zero_add, g, Fin.addCases_right]

/-- Actual native original cut columns produce the same projected field's
L2 columns, zero radial contraction and the non-increasing energy bound. -/
theorem native_spatial_projected_column_data {n q : ℕ} {a b : ℝ}
    (r : ℝ) (DW : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    let X : unitCylinder n a b → Domain (n + 1) := fun c => e.symm (r • (e c.val).1, (e c.val).2)
    let g : unitCylinder n a b → Gradient (n + 1) q := fun c => Fin.addCases
      (fun i : Fin n => r • tangentialColumns ⟨(e c.val).1, c.property.1⟩
        (fun j => DW (X c) (Fin.castAdd 1 j)) i)
      (fun _ : Fin 1 => DW (X c) (Fin.natAdd n (0 : Fin 1)))
    (∀ i : Fin (n + 1), MemLp (fun c => DW (X c) i) 2 μ) →
    (∀ i : Fin (n + 1), MemLp (fun c => g c i) 2 μ) ∧
      (∀ c : unitCylinder n a b, (∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i)) = 0) ∧
      Integrable (fun c => hsNormSq (g c)) μ ∧
      (|r| ≤ 1 → (∀ c, hsNormSq (g c) ≤ hsNormSq (DW (X c))) ∧
        (∫ c, hsNormSq (g c) ∂μ) ≤ ∫ c, hsNormSq (DW (X c)) ∂μ) := by
  intro e μ X g hDW
  have hTheta (j : Fin n) : MemLp (fun c : unitCylinder n a b => (e c.val).1 j) ∞ μ := by
    apply memLp_top_of_bound (by fun_prop) 1
    filter_upwards with c
    have hj := PiLp.norm_apply_le ((e c.val).1) j
    have hN : ‖(e c.val).1‖ = 1 := mem_sphere_zero_iff_norm.mp c.property.1
    simpa only [hN] using hj
  have hRadial : MemLp (fun c : unitCylinder n a b => ∑ j : Fin n,
      (e c.val).1 j • DW (X c) (Fin.castAdd 1 j)) 2 μ := by
    simpa only [Finset.sum_apply, Pi.smul_apply'] using
      memLp_finsetSum Finset.univ (fun j _ => (hDW (Fin.castAdd 1 j)).smul
        (r := (2 : ℝ≥0∞)) (hTheta j))
  have hg (i : Fin (n + 1)) : MemLp (fun c => g c i) 2 μ := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have h := ((hDW (Fin.castAdd 1 j)).sub
        (hRadial.smul (r := (2 : ℝ≥0∞)) (hTheta j))).const_smul r
      change MemLp (fun c : unitCylinder n a b => r •
        (DW (X c) (Fin.castAdd 1 j) - (e c.val).1 j •
          ∑ k : Fin n, (e c.val).1 k • DW (X c) (Fin.castAdd 1 k))) 2 μ at h
      simpa only [g, Fin.addCases_left, tangentialColumns] using h
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa only [g, Fin.addCases_right] using hDW (Fin.natAdd n (0 : Fin 1))
  have hTangency (c : unitCylinder n a b) : (∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i)) = 0 := by
    let θ : sphere (0 : Domain n) 1 := ⟨(e c.val).1, c.property.1⟩
    let A : Gradient n q := fun j => DW (X c) (Fin.castAdd 1 j)
    simp only [g, Fin.addCases_left]
    change (∑ i : Fin n, θ.val i • (r • tangentialColumns θ A i)) = 0
    calc
      _ = r • (∑ i : Fin n, θ.val i • tangentialColumns θ A i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact smul_comm (θ.val i) r (tangentialColumns θ A i)
      _ = 0 := by rw [sum_smul_tangentialColumns_eq_zero, smul_zero]
  have hInt : Integrable (fun c => hsNormSq (g c)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hg i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  refine ⟨hg, hTangency, hInt, ?_⟩
  intro hr
  have hPoint (c : unitCylinder n a b) : hsNormSq (g c) ≤ hsNormSq (DW (X c)) := by
    let θ : sphere (0 : Domain n) 1 := ⟨(e c.val).1, c.property.1⟩
    let A : Gradient n q := fun j => DW (X c) (Fin.castAdd 1 j)
    have hProj := hsNormSq_tangentialColumns_le θ A
    have hNonneg := hsNormSq_nonneg (tangentialColumns θ A)
    have hR : r ^ 2 ≤ 1 := by have hh := abs_le.mp hr; nlinarith [hh.1, hh.2]
    have hScaled : r ^ 2 * hsNormSq (tangentialColumns θ A) ≤ hsNormSq A := by
      exact (mul_le_of_le_one_left hNonneg hR).trans hProj
    have hG : hsNormSq (g c) = r ^ 2 * hsNormSq (tangentialColumns θ A) +
        ‖DW (X c) (Fin.natAdd n (0 : Fin 1))‖ ^ 2 := by
      simp only [hsNormSq, g, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
        Fin.sum_univ_one, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [Finset.mul_sum]
    have hSource : hsNormSq (DW (X c)) = hsNormSq A +
        ‖DW (X c) (Fin.natAdd n (0 : Fin 1))‖ ^ 2 := by
      simp only [hsNormSq, A, Fin.sum_univ_add, Fin.sum_univ_one]
    rw [hG, hSource]
    exact add_le_add hScaled le_rfl
  exact ⟨hPoint, integral_mono hInt (integrable_finsetSum Finset.univ (fun i _ => (hDW i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))) hPoint⟩

end StratificationTheory
