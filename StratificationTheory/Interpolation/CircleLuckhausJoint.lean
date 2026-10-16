module
public import StratificationTheory.Interpolation.AffineCylinderRayEnergy
public import StratificationTheory.Interpolation.CircleCylinderDistance
public import StratificationTheory.Interpolation.LinearCylinderTrace
public import StratificationTheory.Foundation.CylinderNativeGradientL2
public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory
/-- The exact two-dimensional specialization of the joint Luckhaus estimate. -/
theorem luckhaus_joint_twoDimensional :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (N : Set (Ambient q)), IsCompact N →
      ∀ (u v : sphere (0 : Domain 2) 1 → Ambient q)
        (hu : MemSphereW12 (Nat.le_refl 2) u) (hv : MemSphereW12 (Nat.le_refl 2) v),
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (2 - 1) :
        Measure (sphere (0 : Domain 2) 1)), u θ ∈ N) →
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (2 - 1) :
        Measure (sphere (0 : Domain 2) 1)), v θ ∈ N) →
      ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) (1 / 8)),
      let σ : Measure (sphere (0 : Domain 2) 1) := Measure.euclideanHausdorffMeasure (2 - 1)
      let A : ℝ := ∫ θ : sphere (0 : Domain 2) 1,
        hsNormSq (fun i : Fin 2 => (sphereGradient (Nat.le_refl 2) u hu i) θ) +
          hsNormSq (fun i : Fin 2 => (sphereGradient (Nat.le_refl 2) v hv i) θ) ∂σ
      let D : ℝ := ∫ θ : sphere (0 : Domain 2) 1, ‖u θ - v θ‖ ^ 2 ∂σ
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
      let μ : Measure (unitCylinder 2 0 ε) := Measure.euclideanHausdorffMeasure 2
      let U : OpenDomain (2 + 1) :=
        ⟨{y | ‖(e y).1‖ ∈ Ioo (1 / 2 : ℝ) 2 ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε},
          (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      ∃ (w : unitCylinder 2 0 ε → Ambient q) (hw : MemCylinderW12 (Nat.le_refl 2) hε.1 w)
        (W : Domain (2 + 1) → Ambient q) (DW : Domain (2 + 1) → Gradient (2 + 1) q)
        (g : unitCylinder 2 0 ε → Gradient (2 + 1) q),
        MemW12 U W DW ∧
        (∀ (r : ℝ), r ∈ Ioo (1 / 2 : ℝ) 2 → ∀ c : unitCylinder 2 0 ε,
          (e c.val).2 0 ∈ Ioo (0 : ℝ) ε →
            W (e.symm (r • (e c.val).1, (e c.val).2)) = w c) ∧
        (∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
          ∀ᵐ c : unitCylinder 2 0 ε ∂μ, (e c.val).2 0 ∈ Ioo (0 : ℝ) ε →
            (∀ i : Fin 2,
              DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
                r⁻¹ • g c (Fin.castAdd 1 i)) ∧
            DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.natAdd 2 (0 : Fin 1)) =
              g c (Fin.natAdd 2 (0 : Fin 1))) ∧
        (∀ i : Fin (2 + 1), MemLp (fun c : unitCylinder 2 0 ε => g c i) 2 μ) ∧
        (∀ᵐ c : unitCylinder 2 0 ε ∂μ,
          (∑ i : Fin 2, (e c.val).1 i • g c (Fin.castAdd 1 i)) = 0) ∧
        Integrable (fun c : unitCylinder 2 0 ε => hsNormSq (g c)) μ ∧
        (∫ c : unitCylinder 2 0 ε, hsNormSq (g c) ∂μ) ≤ C * ε * A + C / ε * D ∧
        (∀ᵐ c : unitCylinder 2 0 ε ∂μ,
          (infDist (w c) N) ^ 2 ≤
            C * ε ^ (1 - (2 : ℤ)) * Real.sqrt A * Real.sqrt D +
              C * ε ^ (-(2 : ℤ)) * D) ∧
        cylinderTrace (Nat.le_refl 2) hε.1 w hw ⟨0, le_rfl, hε.1.le⟩ = hu.1.toLp u ∧
        cylinderTrace (Nat.le_refl 2) hε.1 w hw ⟨ε, hε.1.le, le_rfl⟩ = hv.1.toLp v  := by
  refine ⟨8, by norm_num, ?_⟩
  intro q N hN u v hu hv huN hvN ε hε σ A D e μ U
  let c : unitCylinder 2 0 ε → Ambient q := fun y =>
    (1 - (e y.val).2 0 / ε) • u ⟨(e y.val).1, y.property.1⟩ +
      ((e y.val).2 0 / ε) • v ⟨(e y.val).1, y.property.1⟩
  obtain ⟨W, DW, hW, hRaw, hAll, hInt, hEnergy⟩ :=
    exists_cylinder_affine_all_radius_native_energy (Nat.le_refl 2) hε.1 u v hu hv
  have hOne : ∀ᵐ θ : sphere (0 : Domain 2) 1 ∂σ, ∀ t : ℝ,
      DW (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
        Fin.addCases
          (fun i => (1 - t / ε) • (sphereGradient (Nat.le_refl 2) u hu i) θ +
            (t / ε) • (sphereGradient (Nat.le_refl 2) v hv i) θ)
          (fun _ => ε⁻¹ • (v θ - u θ)) := by
    simpa only [sub_zero, one_smul, inv_one] using hAll ⟨1, by norm_num⟩
  have hColumns : ∀ i : Fin 3, MemLp (fun y : unitCylinder 2 0 ε => DW y.val i) 2 μ := by
    exact memLp_native_cylinder_columns_of_affine_formula (by decide : 0 < 2)
      hε.1 u v hu.1 hv.1 (sphereGradient (Nat.le_refl 2) u hu)
        (sphereGradient (Nat.le_refl 2) v hv) DW (by simpa only [sub_zero] using hOne)
  have hc : MemCylinderW12 (Nat.le_refl 2) hε.1 c := by
    simpa only [sub_zero] using memCylinderW12_linearInterpolation (Nat.le_refl 2) hε.1 hu hv
  obtain ⟨hc', hTrace, hLeft, hRight, hIncrements⟩ :=
    cylinderTrace_linearInterpolation (Nat.le_refl 2) hε.1 u v hu hv
  refine ⟨c, hc, W, DW, (fun y => DW y.val), ?_, ?_, ?_, hColumns, ?_, hInt, ?_, ?_, ?_, ?_⟩
  · exact hW
  · intro r hr y ht
    have hSpatial : r • (e y.val).1 ∈
        ({x : Domain 2 | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2} : Set (Domain 2)) := by
      have hy : ‖(e y.val).1‖ = 1 := mem_sphere_zero_iff_norm.mp y.property.1
      simp only [mem_setOf_eq, norm_smul, Real.norm_eq_abs, hy, mul_one,
        abs_of_pos (by linarith [hr.1] : 0 < r)]
      exact hr
    simpa only [sub_zero, c] using hRaw ⟨r, by linarith [hr.1]⟩ y ht hSpatial
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply ae_unitCylinder_of_ae_forall_time (by decide : 0 < 2)
    filter_upwards [hOne, hAll ⟨r, by linarith [hr.1]⟩] with θ h1 hrθ
    intro t ht
    simp only [e, ContinuousLinearEquiv.apply_symm_apply]
    change (∀ i : Fin 2,
      DW (e.symm (r • θ.val, EuclideanSpace.single (0 : Fin 1) t.val)) (Fin.castAdd 1 i) =
        r⁻¹ • DW (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t.val)) (Fin.castAdd 1 i)) ∧
      DW (e.symm (r • θ.val, EuclideanSpace.single (0 : Fin 1) t.val)) (Fin.natAdd 2 (0 : Fin 1)) =
        DW (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t.val)) (Fin.natAdd 2 (0 : Fin 1))
    rw [hrθ t.val, h1 t.val]
    simp only [Fin.addCases_left, Fin.addCases_right, sub_zero]
    refine ⟨?_, trivial⟩
    intro i
    rw [smul_add]
    congr 1 <;> simp only [smul_smul] <;> congr 1 <;> ring
  · apply ae_unitCylinder_of_ae_forall_time (by decide : 0 < 2)
    filter_upwards [hOne, (sphereGradient_characterization (Nat.le_refl 2) u hu).1.2.1,
      (sphereGradient_characterization (Nat.le_refl 2) v hv).1.2.1] with θ h1 huT hvT
    intro t
    change (∑ i : Fin 2, θ.val i •
      DW (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t.val)) (Fin.castAdd 1 i)) = 0
    rw [h1 t.val]
    simp only [Fin.addCases_left, smul_add, Finset.sum_add_distrib]
    have huSwap : (∑ i : Fin 2, θ.val i • ((1 - t.val / ε) •
        (sphereGradient (Nat.le_refl 2) u hu i) θ)) =
        (1 - t.val / ε) • (∑ i : Fin 2, θ.val i • (sphereGradient (Nat.le_refl 2) u hu i) θ) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact smul_comm _ _ _
    have hvSwap : (∑ i : Fin 2, θ.val i • ((t.val / ε) •
        (sphereGradient (Nat.le_refl 2) v hv i) θ)) =
        (t.val / ε) • (∑ i : Fin 2, θ.val i • (sphereGradient (Nat.le_refl 2) v hv i) θ) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact smul_comm _ _ _
    rw [huSwap, hvSwap, huT, hvT, smul_zero, smul_zero, add_zero]
  · have hA : 0 ≤ A := integral_nonneg fun θ => add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _)
    have hD : 0 ≤ D := integral_nonneg fun θ => sq_nonneg _
    have he : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.1.le
    have hEnergy' : (∫ y : unitCylinder 2 0 ε, hsNormSq (DW y.val) ∂μ) ≤
        (ε / 2) * A + ε⁻¹ * D := by
      simpa only [sub_zero, A, D, σ, hsNormSq, ← Finset.sum_add_distrib, norm_sub_rev] using hEnergy
    have hInv : (8 : ℝ) / ε = 8 * ε⁻¹ := div_eq_mul_inv _ _
    rw [hInv]
    nlinarith [mul_nonneg hε.1.le hA, mul_nonneg he hD]
  · have hDistance := circle_affine_cylinder_distance_bound hε.1 u v hu hv N (Or.inl huN)
    have hA : 0 ≤ A := integral_nonneg fun θ => add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _)
    have hD : 0 ≤ D := integral_nonneg fun θ => sq_nonneg _
    have hε1 : ε ≤ 1 := by linarith [hε.2]
    have hInv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε.1).mpr hε1
    have hInv2 : 1 ≤ ε⁻¹ ^ 2 := one_le_pow₀ hInv
    have hPower1 : ε ^ (1 - (2 : ℤ)) = ε⁻¹ := by norm_num
    have hPower2 : ε ^ (-(2 : ℤ)) = ε⁻¹ ^ 2 := by simp only [zpow_neg, zpow_ofNat, inv_pow]
    have hMon1 := mul_le_mul_of_nonneg_right hInv
      (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg D))
    have hMon2 := mul_le_mul_of_nonneg_right hInv2 hD
    filter_upwards [hDistance] with y hy
    have hy' : (infDist (c y) N) ^ 2 ≤ 8 * Real.sqrt (A * D) + 8 * D := by
      simpa only [sub_zero, c, A, D, σ, hsNormSq, ← Finset.sum_add_distrib] using hy
    rw [Real.sqrt_mul hA] at hy'
    rw [hPower1, hPower2]
    nlinarith
  · simpa only [sub_zero, c] using hLeft
  · simpa only [sub_zero, c] using hRight
end StratificationTheory
