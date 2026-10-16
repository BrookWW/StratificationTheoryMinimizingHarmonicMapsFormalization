module

public import StratificationTheory.Interpolation.SpherePairExtendedPrismSlab
public import StratificationTheory.Foundation.NativeSpatialCylinderQualifiedRadius
public import StratificationTheory.Foundation.NativeSpatialCylinderSobolevSlices

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- One radius of the actual source connector retains its extended native
weak graph, both original constant outer time bands, the coupled original
energy bound, and its original target-distance constraint. -/
theorem exists_sphere_pair_qualified_cylinder_radius {n q : ℕ}
    (u : Fin 2 → sphere (0 : Domain (n + 3)) 1 → Ambient q)
    (hu : ∀ l, MemSphereW12 (by omega : 2 ≤ n + 3) (u l))
    (N : Set (Ambient q)) (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n + 2) :
      Measure (sphere (0 : Domain (n + 3)) 1)), u l θ ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < (1 / 8 : ℝ)) :
    let m := n + 3
    let R : ℝ := (n : ℝ) + 4
    let J := (r : Fin (m + 1)) × (Fin r.val ↪ Fin m)
    let A : ℝ := ∫ θ : sphere (0 : Domain m) 1,
      hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ m) (u 0) (hu 0) i) θ) +
        hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ m) (u 1) (hu 1) i) θ)
          ∂Measure.euclideanHausdorffMeasure (m - 1)
    let D : ℝ := ∫ θ : sphere (0 : Domain m) 1, ‖u 0 θ - u 1 θ‖ ^ 2
      ∂Measure.euclideanHausdorffMeasure (m - 1)
    let CE : ℝ := R ^ (m - 2) / (m - 2)
    let CD : ℝ := R ^ m / m
    let K : ℝ≥0∞ := 4 * (Fintype.card J : ℝ≥0∞) * (Fintype.card J : ℝ≥0∞) *
      (6 * ((m + 1 : ℕ) : ℝ≥0∞)) ^ (m - 1)
    let BTube := ((2 : ℝ) ^ (m - 1) * (m.factorial : ℝ)) *
      ((4 * (Fintype.card J : ℝ)) * ε ^ ((1 : ℤ) - (m : ℤ)) * Real.sqrt (CE * A) * Real.sqrt (CD * D) +
        (4 * (Fintype.card J : ℝ)) * ε ^ (-(m : ℤ)) * (CD * D))
    let η := (Measure.volumeIoiPow (m - 1)).restrict
      {ρ : Ioi (0 : ℝ) | (1 / 4 : ℝ) < ρ.val ∧ ρ.val < (1 / 2 : ℝ)}
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := 1)
    let μ : Measure (unitCylinder m 0 ε) := Measure.euclideanHausdorffMeasure m
    ∃ r ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ),
      ∃ (W : Domain (m + 1) → Ambient q) (DW : Domain (m + 1) → Gradient (m + 1) q) (M : ℝ),
      let X := fun {a b : ℝ} (c : unitCylinder m a b) => e.symm (r • (e c.val).1, (e c.val).2)
      let F := fun y : Domain (m + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
      let C : OpenDomain (m + 1) :=
        ⟨{y | (1 / 2 < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)},
          (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      MemCylinderW12 (by omega : 2 ≤ m) (by norm_num : (-(1 / 4 : ℝ)) < (1 / 4 : ℝ))
        (fun c : unitCylinder m (-(1 / 4 : ℝ)) (1 / 4 : ℝ) => W (X c)) ∧
      MemW12 C (W ∘ F) (fun y i => ∑ j : Fin (m + 1),
        (fderiv ℝ F y (EuclideanSpace.single i 1)) j • DW (F y) j) ∧
      (0 ≤ M ∧ ∀ z ∈ N, ‖z‖ ≤ M) ∧
      (∀ c : unitCylinder m (-(1 / 4 : ℝ)) (1 / 4 : ℝ), (e c.val).2 0 < 0 →
        W (X c) = u 0 ⟨(e c.val).1, c.property.1⟩) ∧
      (∀ c : unitCylinder m (-(1 / 4 : ℝ)) (1 / 4 : ℝ), ε < (e c.val).2 0 →
        W (X c) = u 1 ⟨(e c.val).1, c.property.1⟩) ∧
      MemLp (fun c : unitCylinder m 0 ε => W (X c)) 2 μ ∧
      (∀ i : Fin (m + 1), MemLp (fun c : unitCylinder m 0 ε => DW (X c) i) 2 μ) ∧
      Integrable (fun c : unitCylinder m 0 ε => hsNormSq (DW (X c))) μ ∧
      (∀ᵐ c : unitCylinder m 0 ε ∂μ, ‖W (X c)‖ ≤ M ∧ (infDist (W (X c)) N) ^ 2 ≤ BTube) ∧
      ENNReal.ofReal (∫ c : unitCylinder m 0 ε, hsNormSq (DW (X c)) ∂μ) ≤
        ENNReal.ofReal ((η univ).toReal⁻¹) * K *
          (ENNReal.ofReal ε * ENNReal.ofReal (CE * A) +
            (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal (CD * D)) := by
  classical
  intro m R J A D CE CD K BTube η e μ
  obtain ⟨radial, Dradial, W, DW, M, Htime, _hSob, _hNr, hRays,
    hW, hM, hNorm, hEnergy, hTube, _hRaw, _hEnd₀, _hEnd₁, hExt0, hBall0, hPoint, hInnerE⟩ :=
    exists_sphere_pair_extended_prism_slab u hu N hN hTarget ε hε hεsmall
  let Waux := fun y : Domain (m + 1) => if (e y).2 0 < 0 then radial 0 (e y).1 else
    if (e y).2 0 < ε then W y else radial 1 (e y).1
  let Daux := fun (y : Domain (m + 1)) (i : Fin (m + 1)) =>
    if (e y).2 0 < 0 then Fin.lastCases (0 : Ambient q) (fun j => Dradial 0 (e y).1 j) i else
      if (e y).2 0 < ε then DW y i else Fin.lastCases (0 : Ambient q) (fun j => Dradial 1 (e y).1 j) i
  let U : OpenDomain m := ⟨⋂ j : Fin m, (EuclideanSpace.proj j) ⁻¹' Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ),
    isOpen_iInter_of_finite (fun j : Fin m => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
  let Rect := fun a b : ℝ => (⟨{y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo a b},
    (U.property.preimage (continuous_fst.comp e.continuous)).inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous)))⟩ : OpenDomain (m + 1))
  let Ann := fun a b : ℝ => (⟨{y | ((1 / 4 : ℝ) < ‖(e y).1‖ ∧ ‖(e y).1‖ < (1 / 2 : ℝ)) ∧ (e y).2 0 ∈ Ioo a b},
    (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous)))⟩ : OpenDomain (m + 1))
  have hExt : MemW12 (Rect (-1) 1) Waux Daux := by with_reducible exact hExt0
  have hBall : MemW12 (ballDomain (0 : Domain (m + 1)) (3 / 4 : ℝ)) Waux Daux := by with_reducible exact hBall0
  have hBandBall : (Ann (-(1 / 4 : ℝ)) (1 / 4 : ℝ)).val ⊆ ball (0 : Domain (m + 1)) (3 / 4 : ℝ) := by
    intro y hy
    have hTime : (e y).2 = EuclideanSpace.single (0 : Fin 1) ((e y).2 0) := by
      ext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp
    have hNormSq : ‖y‖ ^ 2 = ‖(e y).1‖ ^ 2 + ((e y).2 0) ^ 2 := by
      have hh := norm_sq_finAddEquivProd_symm (n := m) (m := 1) ((e y).1, (e y).2)
      rw [e.symm_apply_apply, hTime, PiLp.norm_single, Real.norm_eq_abs, sq_abs] at hh
      exact hh
    have hs := hy.1.2
    have ht := abs_lt.mpr hy.2
    have hS0 := norm_nonneg (e y).1
    rw [mem_ball_zero_iff]
    nlinarith [sq_abs ((e y).2 0), abs_nonneg ((e y).2 0), norm_nonneg y]
  have hAE := ae_memCylinderW12_of_original_ball (by omega : 2 ≤ m)
    (s := (1 / 4 : ℝ)) (R := (1 / 2 : ℝ)) (a := -(1 / 4 : ℝ)) (b := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 3 / 4)
    Waux Daux hBall hBandBall
  have hAnnSub : (Ann 0 ε).val ⊆ (Rect 0 ε).val := by
    intro y hy
    refine ⟨?_, hy.2⟩
    rw [mem_iInter]
    intro j
    have hj := PiLp.norm_apply_le (e y).1 j
    rw [Real.norm_eq_abs] at hj
    have ha := abs_le.mp hj
    change -(3 / 4 : ℝ) < (e y).1 j ∧ (e y).1 j < (3 / 4 : ℝ)
    constructor <;> linarith [ha.1, ha.2, hy.1.2]
  have hInnerSub : (Rect 0 ε).val ⊆ (Rect (-1) 1).val := by
    intro y hy
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2, hεsmall]⟩
  have hAnnExt : (Ann 0 ε).val ⊆ (Rect (-1) 1).val := hAnnSub.trans hInnerSub
  have hAnnW : MemW12 (Ann 0 ε) Waux Daux :=
    ⟨hExt.1.mono hAnnExt, hExt.2.1.mono_measure (Measure.restrict_mono_set volume hAnnExt),
      fun i => (hExt.2.2 i).mono_measure (Measure.restrict_mono_set volume hAnnExt)⟩
  have hP : ∀ᵐ y ∂volume.restrict (Ann 0 ε).val, ‖Waux y‖ ≤ M ∧ (infDist (Waux y) N) ^ 2 ≤ BTube := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAnnSub hNorm,
      ae_restrict_of_ae_restrict_of_subset hAnnSub hTube,
      ae_restrict_mem (Ann 0 ε).property.measurableSet] with y hn ht hy
    change (((1 / 4 : ℝ) < ‖(e y).1‖ ∧ ‖(e y).1‖ < (1 / 2 : ℝ)) ∧
      (e y).2 0 ∈ Ioo (0 : ℝ) ε) at hy
    have hEq : Waux y = W y := by with_reducible exact (hPoint y hy.2).1
    rw [hEq]
    exact ⟨hn, ht⟩
  let Q := fun r : ℝ =>
    let X := fun c : unitCylinder m (-(1 / 4 : ℝ)) (1 / 4 : ℝ) => e.symm (r • (e c.val).1, (e c.val).2)
    let F := fun y : Domain (m + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    let C : OpenDomain (m + 1) := ⟨{y | ((1 / 2 : ℝ) < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)},
      (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_snd.comp e.continuous)))⟩
    MemCylinderW12 (by omega : 2 ≤ m) (by norm_num : (-(1 / 4 : ℝ)) < (1 / 4 : ℝ)) (fun c => Waux (X c)) ∧
      MemW12 C (Waux ∘ F) (fun y i => ∑ j : Fin (m + 1),
        (fderiv ℝ F y (EuclideanSpace.single i 1)) j • Daux (F y) j)
  obtain ⟨r, hr, hQ, hLp, hCols, hInt, hPr, hEr⟩ :=
    exists_native_spatial_cylinder_good_radius_with_qualification (by omega : 0 < m)
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1 / 2) Waux Daux hAnnW
      (fun z => ‖z‖ ≤ M ∧ (infDist z N) ^ 2 ≤ BTube) hP Q hAE
  refine ⟨r, hr, Waux, Daux, M, ?_⟩
  intro X F C
  refine ⟨hQ.1, hQ.2, hM, ?_, ?_, hLp, hCols, hInt, hPr, ?_⟩
  · intro c ht
    dsimp only [Waux, X]
    rw [e.apply_symm_apply]
    simp only [if_pos ht]
    exact hRays 0 ⟨r, lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hr.1⟩ ⟨(e c.val).1, c.property.1⟩
  · intro c ht
    dsimp only [Waux, X]
    rw [e.apply_symm_apply]
    simp only [if_neg (not_lt.mpr (hε.trans ht).le), if_neg (not_lt.mpr ht.le)]
    exact hRays 1 ⟨r, lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hr.1⟩ ⟨(e c.val).1, c.property.1⟩
  · have hAnnEnergy : (∫ y in (Ann 0 ε).val, hsNormSq (Daux y)) ≤ ∫ y in (Rect 0 ε).val, hsNormSq (Daux y) :=
      setIntegral_mono_set (hExt.integrable_hsNormSq.mono_set hInnerSub)
        (Eventually.of_forall fun y => hsNormSq_nonneg (Daux y))
        (Eventually.of_forall fun y hy => hAnnSub hy)
    have hInnerEnergy : (∫ y in (Rect 0 ε).val, hsNormSq (Daux y)) = ∫ y in (Rect 0 ε).val, hsNormSq (DW y) := by
      with_reducible exact hInnerE
    have hE : ENNReal.ofReal (∫ y in (Ann 0 ε).val, hsNormSq (Daux y)) ≤
        K * (ENNReal.ofReal ε * ENNReal.ofReal (CE * A) + (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal (CD * D)) := by
      apply (ENNReal.ofReal_le_ofReal hAnnEnergy).trans
      rw [hInnerEnergy]
      exact hEnergy
    have hEr' := ENNReal.ofReal_le_ofReal hEr
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg)] at hEr'
    exact hEr'.trans (by simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal ((η univ).toReal⁻¹))) hE)

end StratificationTheory
