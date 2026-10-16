module

public import StratificationTheory.Interpolation.SpherePairQualifiedCylinderRadius
public import StratificationTheory.Foundation.NativeSpatialCylinderFieldData
public import StratificationTheory.Foundation.JointPrismScalarConstant
public import StratificationTheory.Foundation.CylinderTraceConstantBands
public import StratificationTheory.Foundation.CylinderTimeRestriction

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- The complete coupled Luckhaus estimate in every ambient dimension
at least three, with one dimension-only constant and both original named
trace classes for the same actual coherent weak columns. -/
theorem luckhaus_joint_high_dimensional (k : ℕ) :
    let n := k + 3
    let hn : 2 ≤ n := by omega

    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (N : Set (Ambient q)), IsCompact N →
      ∀ (u v : sphere (0 : Domain n) 1 → Ambient q)
        (hu : MemSphereW12 hn u) (hv : MemSphereW12 hn v),
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)), u θ ∈ N) →
      (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (sphere (0 : Domain n) 1)), v θ ∈ N) →
      ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) (1 / 8)),
      let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
      let A : ℝ := ∫ θ : sphere (0 : Domain n) 1,
        hsNormSq (fun i : Fin n => (sphereGradient hn u hu i) θ) +
          hsNormSq (fun i : Fin n => (sphereGradient hn v hv i) θ) ∂σ
      let D : ℝ := ∫ θ : sphere (0 : Domain n) 1, ‖u θ - v θ‖ ^ 2 ∂σ
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let μ : Measure (unitCylinder n 0 ε) := Measure.euclideanHausdorffMeasure n
      let U : OpenDomain (n + 1) :=
        ⟨{y | ‖(e y).1‖ ∈ Ioo (1 / 2 : ℝ) 2 ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε},
          (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      ∃ (w : unitCylinder n 0 ε → Ambient q) (hw : MemCylinderW12 hn hε.1 w)
        (W : Domain (n + 1) → Ambient q) (DW : Domain (n + 1) → Gradient (n + 1) q)
        (g : unitCylinder n 0 ε → Gradient (n + 1) q),
        MemW12 U W DW ∧
        (∀ (r : ℝ), r ∈ Ioo (1 / 2 : ℝ) 2 → ∀ c : unitCylinder n 0 ε,
          (e c.val).2 0 ∈ Ioo (0 : ℝ) ε →
            W (e.symm (r • (e c.val).1, (e c.val).2)) = w c) ∧
        (∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
          ∀ᵐ c : unitCylinder n 0 ε ∂μ, (e c.val).2 0 ∈ Ioo (0 : ℝ) ε →
            (∀ i : Fin n,
              DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
                r⁻¹ • g c (Fin.castAdd 1 i)) ∧
            DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
              g c (Fin.natAdd n (0 : Fin 1))) ∧
        (∀ i : Fin (n + 1), MemLp (fun c : unitCylinder n 0 ε => g c i) 2 μ) ∧
        (∀ᵐ c : unitCylinder n 0 ε ∂μ,
          (∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i)) = 0) ∧
        Integrable (fun c : unitCylinder n 0 ε => hsNormSq (g c)) μ ∧
        (∫ c : unitCylinder n 0 ε, hsNormSq (g c) ∂μ) ≤ C * ε * A + C / ε * D ∧
        (∀ᵐ c : unitCylinder n 0 ε ∂μ,
          (infDist (w c) N) ^ 2 ≤
            C * ε ^ (1 - (n : ℤ)) * Real.sqrt A * Real.sqrt D +
              C * ε ^ (-(n : ℤ)) * D) ∧
        cylinderTrace hn hε.1 w hw ⟨0, le_rfl, hε.1.le⟩ = hu.1.toLp u ∧
        cylinderTrace hn hε.1 w hw ⟨ε, hε.1.le, le_rfl⟩ = hv.1.toLp v 
 := by
  classical
  intro n hn
  let R : ℝ := (k : ℝ) + 4
  let J := (r : Fin (n + 1)) × (Fin r.val ↪ Fin n)
  let CE : ℝ := R ^ (n - 2) / (n - 2)
  let CD : ℝ := R ^ n / n
  let K : ℝ≥0∞ := 4 * (Fintype.card J : ℝ≥0∞) * (Fintype.card J : ℝ≥0∞) *
    (6 * ((n + 1 : ℕ) : ℝ≥0∞)) ^ (n - 1)
  let η := (Measure.volumeIoiPow (n - 1)).restrict
    {ρ : Ioi (0 : ℝ) | (1 / 4 : ℝ) < ρ.val ∧ ρ.val < (1 / 2 : ℝ)}
  let Le : ℝ := (η univ).toReal⁻¹ * K.toReal
  let Lt : ℝ := ((2 : ℝ) ^ (n - 1) * (n.factorial : ℝ)) * (4 * (Fintype.card J : ℝ))
  have hLe : 0 ≤ Le := mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  have hLt : 0 ≤ Lt := by dsimp only [Lt]; positivity
  have hCE : 0 ≤ CE := by
    have hd : (0 : ℝ) ≤ (n : ℝ) - 2 := by
      have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact div_nonneg (pow_nonneg (by dsimp only [R]; positivity) _) hd
  have hCD : 0 ≤ CD := by dsimp only [CD, R]; positivity
  obtain ⟨C, hC, hEst⟩ := exists_joint_prism_scalar_constant n Le Lt CE CD hLe hLt hCE hCD
  refine ⟨C, hC, ?_⟩
  intro q N hN u v hu hv hNu hNv ε hε σ A D e μ U
  have hεpos : 0 < ε := hε.1
  let pair : Fin 2 → sphere (0 : Domain n) 1 → Ambient q := ![u, v]
  have hPairZero : pair 0 = u := rfl
  have hPairOne : pair 1 = v := rfl
  have hPair : ∀ l, MemSphereW12 hn (pair l) := by
    intro l
    fin_cases l
    · exact hu
    · exact hv
  have hTargetZero : ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (k + 2) :
      Measure (sphere (0 : Domain n) 1)), u θ ∈ N := by
    simpa only [n, show k + 3 - 1 = k + 2 by omega] using hNu
  have hTargetOne : ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (k + 2) :
      Measure (sphere (0 : Domain n) 1)), v θ ∈ N := by
    simpa only [n, show k + 3 - 1 = k + 2 by omega] using hNv
  have hTarget : ∀ l, ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (k + 2) :
      Measure (sphere (0 : Domain n) 1)), pair l θ ∈ N := by
    intro l
    filter_upwards [hTargetZero, hTargetOne] with θ hθ₀ hθ₁
    have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
    rcases hl with rfl | rfl
    · rw [hPairZero]
      exact hθ₀
    · rw [hPairOne]
      exact hθ₁
  obtain ⟨r, hr, V, DV, _M, hNative, hFullExt, _hM, hLeft, hRight,
    _hLp, hCols, _hInt, hP, hSourceEnergy⟩ :=
      exists_sphere_pair_qualified_cylinder_radius pair hPair N hN hTarget ε hε.1 hε.2
  let X := fun {a b : ℝ} (c : unitCylinder n a b) => e.symm (r • (e c.val).1, (e c.val).2)
  let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
  let W := V ∘ F
  let DW := fun (y : Domain (n + 1)) (i : Fin (n + 1)) => ∑ j : Fin (n + 1),
    (fderiv ℝ F y (EuclideanSpace.single i 1)) j • DV (F y) j
  let wExt := fun c : unitCylinder n (-(1 / 4 : ℝ)) (1 / 4 : ℝ) => V (X c)
  let incl : unitCylinder n 0 ε → unitCylinder n (-(1 / 4 : ℝ)) (1 / 4 : ℝ) := fun c =>
    ⟨c.val, c.property.1, by linarith [c.property.2.1], by linarith [c.property.2.2, hε.2]⟩
  let w := wExt ∘ incl
  let g : unitCylinder n 0 ε → Gradient (n + 1) q := fun c => Fin.addCases
    (fun i : Fin n => r • tangentialColumns ⟨(e c.val).1, c.property.1⟩
      (fun j => DV (X c) (Fin.castAdd 1 j)) i)
    (fun _ : Fin 1 => DV (X c) (Fin.natAdd n (0 : Fin 1)))
  have hFull : MemW12 U W DW := by
    have hSub : U.val ⊆ {y : Domain (n + 1) |
        ((1 / 2 : ℝ) < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧
          (e y).2 0 ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)} := by
      intro y hy
      change (‖(e y).1‖ ∈ Ioo (1 / 2 : ℝ) 2 ∧ (e y).2 0 ∈ Ioo (0 : ℝ) ε) at hy
      exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2, hε.2]⟩
    exact ⟨hFullExt.1.mono hSub,
      hFullExt.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i => (hFullExt.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  have hab : (-(1 / 4 : ℝ)) < (1 / 4 : ℝ) := by norm_num
  have has : (-(1 / 4 : ℝ)) ≤ 0 := by norm_num
  have htb : ε ≤ (1 / 4 : ℝ) := by linarith [hε.2]
  obtain ⟨hw, hTrace⟩ := exists_cylinder_time_restriction hn hab hε.1 has htb wExt hNative
  have hNative0 : MemCylinderW12 hn hε.1 w := by with_reducible exact hw
  have hRay (ρ : ℝ) (hρ : 0 < ρ) (c : unitCylinder n 0 ε) :
      W (e.symm (ρ • (e c.val).1, (e c.val).2)) = w c :=
    congrArg V (native_spatial_radial_chart_ray_value r hρ c)
  obtain ⟨hFields, hgLp, hgTangent, hgInt, hgEnergy⟩ := native_spatial_cylinder_field_data (a := 0) (b := ε) r DV hCols
  have hrAbs : |r| ≤ 1 := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hgE : (∫ c, hsNormSq (g c) ∂μ) ≤ ∫ c : unitCylinder n 0 ε, hsNormSq (DV (X c)) ∂μ :=
    hgEnergy hrAbs
  have hA : 0 ≤ A := integral_nonneg fun θ => add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _)
  have hD : 0 ≤ D := integral_nonneg fun θ => sq_nonneg _
  have hEambient : ENNReal.ofReal (∫ c : unitCylinder n 0 ε, hsNormSq (DV (X c)) ∂μ) ≤
      ENNReal.ofReal ((η univ).toReal⁻¹) * K *
        (ENNReal.ofReal ε * ENNReal.ofReal (CE * A) + (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal (CD * D)) := by
    with_reducible simpa only [hPairZero, hPairOne, A, D, σ, μ, X, e, n, R, J, CE, CD, K, η,
      show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel_right] using hSourceEnergy
  have hKfinite : K ≠ ⊤ := by dsimp only [K]; finiteness
  have hBudget : 0 ≤ Le * (ε * (CE * A) + ε⁻¹ * (CD * D)) := by positivity
  have hRight : ENNReal.ofReal ((η univ).toReal⁻¹) * K *
      (ENNReal.ofReal ε * ENNReal.ofReal (CE * A) + (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal (CD * D)) =
        ENNReal.ofReal (Le * (ε * (CE * A) + ε⁻¹ * (CD * D))) := by
    rw [ENNReal.ofReal_mul hLe, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hε.1.le, ENNReal.ofReal_mul (inv_nonneg.mpr hε.1.le),
      ENNReal.ofReal_inv_of_pos hε.1]
    dsimp only [Le]
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hKfinite]
  have hEreal : (∫ c : unitCylinder n 0 ε, hsNormSq (DV (X c)) ∂μ) ≤
      Le * (ε * (CE * A) + ε⁻¹ * (CD * D)) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hEambient.trans_eq hRight)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun c => hsNormSq_nonneg _),
      ENNReal.toReal_ofReal hBudget] using hh
  have hTsource : ∀ᵐ c : unitCylinder n 0 ε ∂μ,
      (infDist (w c) N) ^ 2 ≤ Lt * (ε ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt (CE * A) * Real.sqrt (CD * D) +
        ε ^ (-(n : ℤ)) * (CD * D)) := by
    filter_upwards [hP] with c hc
    change _ ∧ _ at hc
    have h' : (infDist (w c) N) ^ 2 ≤ ((2 : ℝ) ^ (n - 1) * (n.factorial : ℝ)) *
        ((4 * (Fintype.card J : ℝ)) * ε ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt (CE * A) * Real.sqrt (CD * D) +
          (4 * (Fintype.card J : ℝ)) * ε ^ (-(n : ℤ)) * (CD * D)) := by
      with_reducible simpa only [w, wExt, incl, X, e, Function.comp_apply, hPairZero, hPairOne, A, D, σ, μ, n, R, J, CE, CD,
        show k + 3 - 1 = k + 2 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel_right] using hc.2
    calc
      _ ≤ _ := h'
      _ = _ := by dsimp only [Lt]; ring
  have hEfinal : (∫ c, hsNormSq (g c) ∂μ) ≤ C * ε * A + C / ε * D :=
    (hEst ε A D (∫ c, hsNormSq (g c) ∂μ) 0 hε.1 hA hD (hgE.trans hEreal)
      (by positivity)).1
  have hTfinal : ∀ᵐ c : unitCylinder n 0 ε ∂μ,
      (infDist (w c) N) ^ 2 ≤ C * ε ^ (1 - (n : ℤ)) * Real.sqrt A * Real.sqrt D + C * ε ^ (-(n : ℤ)) * D := by
    filter_upwards [hTsource] with c hc
    exact (hEst ε A D 0 ((infDist (w c) N) ^ 2) hε.1 hA hD (by positivity) hc).2
  clear hTarget hTargetZero hTargetOne hNu hNv hPairZero hPairOne hPair hCols _hLp _hInt
    hSourceEnergy hEambient hRight hEreal hP hTsource hEst hgEnergy hBudget hKfinite
  refine ⟨w, hNative0, W, DW, g, hFull, ?_, ?_, hgLp,
    hgTangent, hgInt, hEfinal, hTfinal, ?_, ?_⟩
  · intro ρ hρ c _ht
    exact hRay ρ (by linarith [hρ.1]) c
  · with_reducible exact hFields
  · have hLeftTrace := cylinderTrace_eq_of_left_constant_band hn hab
      (by norm_num : (-(1 / 4 : ℝ)) < 0) (by norm_num : (0 : ℝ) ≤ 1 / 4) wExt hNative u hu.1 hLeft
    exact (hTrace ⟨0, le_rfl, hε.1.le⟩).trans hLeftTrace
  · have hRightTrace := cylinderTrace_eq_of_right_constant_band hn hab
      (by linarith : (-(1 / 4 : ℝ)) ≤ ε) (by linarith [hε.2] : ε < (1 / 4 : ℝ)) wExt hNative v hv.1 hRight
    exact (hTrace ⟨ε, hε.1.le, le_rfl⟩).trans hRightTrace

end StratificationTheory
