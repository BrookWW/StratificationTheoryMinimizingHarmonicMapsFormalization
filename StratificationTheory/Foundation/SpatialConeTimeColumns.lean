module

public import StratificationTheory.Foundation.SpatialConeTimeRayCalculus
public import HarmonicMaps.EnergyLemmas
import StratificationTheory.Foundation.CylinderTimeTests
import StratificationTheory.Foundation.CubicalConeGradientBound

/-!
# Original columns in the spatial cone-time chart

The actual chain-rule columns retain the unscaled time derivative. Spatial
columns and the spatial height column have their exact reciprocal-height
formulas, and the same finite family has its exact Hilbert--Schmidt square.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff BigOperators
namespace StratificationTheory

private theorem cone_time_spatial_basis (n : ℕ) (i : Fin n) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      (EuclideanSpace.single (Fin.castAdd 1 i) (1 : ℝ)) =
        (EuclideanSpace.single i 1, 0) := by
  apply Prod.ext
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]
  · ext j
    simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, Pi.single_apply]

private theorem cone_time_column_sum_split {n q : ℕ}
    (x : Domain n) (t : Domain 1) (A : Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∑ j : Fin (n + 1), (e.symm (x, t)) j • A j) =
      (∑ i : Fin n, x i • A (Fin.castAdd 1 i)) + t 0 • A (Fin.natAdd n (0 : Fin 1)) := by
  intro e
  have hfirst (i : Fin n) : (e.symm (x, t)) (Fin.castAdd 1 i) = x i := by
    change (e (e.symm (x, t))).1 i = x i
    rw [e.apply_symm_apply]
  have hlast : (e.symm (x, t)) (Fin.natAdd n (0 : Fin 1)) = t 0 := by
    change (e (e.symm (x, t))).2 0 = t 0
    rw [e.apply_symm_apply]
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [hfirst, hlast]

/-- The same literal chain-rule family has every actual spatial, height and
independent time column expressed in the original source columns. -/
theorem spatial_cone_time_chain_columns {n q : ℕ}
    (Dw : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let X : Domain (n + 1 + 1) → Domain n := fun y => (e ((E y).1)).1
    let ξ : Domain (n + 1 + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y => e.symm (ξ y, (E y).2)
    let D : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y i =>
      ∑ j : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single i 1)) j • Dw (F y) j
    ∀ y, T y ≠ 0 →
      (∀ i : Fin n, D y (Fin.castAdd 1 (Fin.castAdd 1 i)) =
        (T y)⁻¹ • Dw (F y) (Fin.castAdd 1 i)) ∧
      D y (Fin.castAdd 1 (Fin.natAdd n (0 : Fin 1))) =
        -((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • Dw (F y) (Fin.castAdd 1 i)) ∧
      D y (Fin.natAdd (n + 1) (0 : Fin 1)) = Dw (F y) (Fin.natAdd n (0 : Fin 1)) := by
  intro e E T X ξ F D y hy
  have hformula (v : Domain (n + 1 + 1)) :
      fderiv ℝ F y v =
        e.symm ((T y)⁻¹ • X v - (((T y) ^ 2)⁻¹ * T v) • X y, (E v).2) :=
    fderiv_spatial_cone_time_coordinates_apply n y hy v
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hE := cone_time_spatial_basis (n + 1) (Fin.castAdd 1 i)
    have he := cone_time_spatial_basis n i
    change E (EuclideanSpace.single (Fin.castAdd 1 (Fin.castAdd 1 i)) 1) =
      (EuclideanSpace.single (Fin.castAdd 1 i) 1, 0) at hE
    change e (EuclideanSpace.single (Fin.castAdd 1 i) 1) = (EuclideanSpace.single i 1, 0) at he
    have hdiff : fderiv ℝ F y
        (EuclideanSpace.single (Fin.castAdd 1 (Fin.castAdd 1 i)) 1) =
        e.symm ((T y)⁻¹ • EuclideanSpace.single i 1, 0) := by
      rw [hformula]
      simp only [X, T, hE, he, PiLp.zero_apply, mul_zero, zero_smul, sub_zero]
    dsimp only [D]
    rw [hdiff, cone_time_column_sum_split]
    simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_smul, WithLp.ofLp_zero, Pi.zero_apply, zero_smul, add_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hE := cone_time_spatial_basis (n + 1) (Fin.natAdd n (0 : Fin 1))
    have he := finAddEquivProd_time_basis n
    change E (EuclideanSpace.single (Fin.castAdd 1 (Fin.natAdd n (0 : Fin 1))) 1) =
      (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1, 0) at hE
    change e (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) =
      (0, EuclideanSpace.single (0 : Fin 1) 1) at he
    have hdiff : fderiv ℝ F y
        (EuclideanSpace.single (Fin.castAdd 1 (Fin.natAdd n (0 : Fin 1))) 1) =
        e.symm (-((T y)⁻¹ • ξ y), 0) := by
      rw [hformula]
      simp only [X, T, hE, he, PiLp.single_apply, ite_true, smul_zero, zero_sub, mul_one]
      change e.symm (-(((T y) ^ 2)⁻¹ • X y), 0) = e.symm (-((T y)⁻¹ • ξ y), 0)
      dsimp only [ξ]
      rw [smul_smul, ← inv_pow, pow_two]
    dsimp only [D]
    rw [hdiff, cone_time_column_sum_split]
    simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, neg_smul, mul_smul,
      Finset.sum_neg_distrib, ← Finset.smul_sum, WithLp.ofLp_zero, Pi.zero_apply,
      zero_smul, add_zero]
  · have hE := finAddEquivProd_time_basis (n + 1)
    change E (EuclideanSpace.single (Fin.natAdd (n + 1) (0 : Fin 1)) 1) =
      (0, EuclideanSpace.single (0 : Fin 1) 1) at hE
    have hdiff : fderiv ℝ F y (EuclideanSpace.single (Fin.natAdd (n + 1) (0 : Fin 1)) 1) =
        e.symm (0, EuclideanSpace.single (0 : Fin 1) 1) := by
      rw [hformula]
      simp only [X, T, hE, map_zero, Prod.fst_zero, Prod.snd_zero, PiLp.zero_apply,
        smul_zero, mul_zero, zero_smul, sub_zero]
    dsimp only [D]
    rw [hdiff, cone_time_column_sum_split]
    simp only [PiLp.zero_apply, zero_smul, Finset.sum_const_zero, PiLp.ofLp_single,
      Pi.single_apply, if_true, one_smul, zero_add]

private theorem hsNormSq_spatial_cone_time_column_family {n q : ℕ}
    (x : Domain n) (A : Gradient n q) (B : Ambient q) (t : ℝ) :
    hsNormSq (Fin.addCases (motive := fun _ : Fin (n + 1 + 1) => Ambient q)
      (fun j : Fin (n + 1) => Fin.addCases (motive := fun _ : Fin (n + 1) => Ambient q)
        (fun i : Fin n => t⁻¹ • A i)
        (fun _ : Fin 1 => -(t⁻¹ • ∑ i : Fin n, x i • A i)) j)
      (fun _ : Fin 1 => B)) =
      (t⁻¹) ^ 2 * (hsNormSq A + ‖∑ i : Fin n, x i • A i‖ ^ 2) + ‖B‖ ^ 2 := by
  rw [hsNormSq, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one]
  change hsNormSq (Fin.addCases (motive := fun _ : Fin (n + 1) => Ambient q)
    (fun i : Fin n => t⁻¹ • A i)
    (fun _ : Fin 1 => -(t⁻¹ • ∑ i : Fin n, x i • A i))) + ‖B‖ ^ 2 = _
  rw [hsNormSq_face_cone_columns]

/-- The actual same chain-rule family has the exact spatial cone energy
plus the unscaled original independent time-column energy. -/
theorem hsNormSq_spatial_cone_time_chain_columns {n q : ℕ}
    (Dw : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e ((E y).1)).2 0
    let X : Domain (n + 1 + 1) → Domain n := fun y => (e ((E y).1)).1
    let ξ : Domain (n + 1 + 1) → Domain n := fun y => (T y)⁻¹ • X y
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y => e.symm (ξ y, (E y).2)
    let D : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y i =>
      ∑ j : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single i 1)) j • Dw (F y) j
    ∀ y, T y ≠ 0 → hsNormSq (D y) =
      ((T y)⁻¹) ^ 2 *
        (hsNormSq (fun i : Fin n => Dw (F y) (Fin.castAdd 1 i)) +
          ‖∑ i : Fin n, (ξ y) i • Dw (F y) (Fin.castAdd 1 i)‖ ^ 2) +
        ‖Dw (F y) (Fin.natAdd n (0 : Fin 1))‖ ^ 2 := by
  intro e E T X ξ F D y hy
  obtain ⟨hspace, hheight, htime⟩ := spatial_cone_time_chain_columns Dw y hy
  let A : Gradient n q := fun i => Dw (F y) (Fin.castAdd 1 i)
  let B : Ambient q := Dw (F y) (Fin.natAdd n (0 : Fin 1))
  have hfamily : D y =
      Fin.addCases (motive := fun _ : Fin (n + 1 + 1) => Ambient q)
        (fun j : Fin (n + 1) => Fin.addCases (motive := fun _ : Fin (n + 1) => Ambient q)
          (fun i : Fin n => (T y)⁻¹ • A i)
          (fun _ : Fin 1 => -((T y)⁻¹ • ∑ i : Fin n, (ξ y) i • A i)) j)
        (fun _ : Fin 1 => B) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [Fin.addCases_left] using hspace k
      · have hk : k = 0 := Subsingleton.elim _ _
        subst k
        simpa only [Fin.addCases_left, Fin.addCases_right] using hheight
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa only [Fin.addCases_right] using htime
  rw [hfamily]
  exact hsNormSq_spatial_cone_time_column_family (ξ y) A B (T y)

end StratificationTheory
