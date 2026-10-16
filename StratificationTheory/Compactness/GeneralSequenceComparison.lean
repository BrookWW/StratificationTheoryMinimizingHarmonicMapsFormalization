module

public import StratificationTheory.Compactness.GeneralTraceComparison
public import StratificationTheory.Compactness.PairAnnularRadiusWithProperty

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal NNReal

namespace StratificationTheory.Compactness

/-- Strong map convergence on a fixed surrounding annulus
and a uniform energy bound produce the actual minimizing comparison against
the given inner Sobolev map, at every positive energy tolerance. -/
theorem eventually_minimizer_energy_comparison {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
    (c : Domain n) {s t T : ℝ} (hs : 0 < s) (hst : s < t) (htT : t < T)
    (hclosed : closedBall c T ⊆ Ω.val)
    (hu : ∀ k, MemW12 (ballDomain c T) (u k) (Du k))
    (hv : MemW12 (ballDomain c T) v Dv)
    (huN : ∀ k, TakesValuesIn N (ballDomain c T) (u k))
    (hvN : TakesValuesIn N (ballDomain c T) v)
    (hmin : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (C : ℝ≥0) (hEnergy : ∀ k, dirichletEnergy (Du k) (ball c T) ≤ C)
    (hDiff : Tendsto (fun k => ∫ x in ball c t \ ball c s, ‖u k x - v x‖ ^ 2)
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ x in ball c s, hsNormSq (Du k x)) ≤
        (∫ x in ball c t, hsNormSq (Dv x)) + ε := by
  intro ε hε
  obtain ⟨ρ, L, hρ, hL, hop⟩ := exists_trace_comparison_radius hn N
  have ht : 0 < t := hs.trans hst
  have hT : 0 < T := ht.trans htT
  have hwidth : 0 < t - s := sub_pos.mpr hst
  let V := ∫ x in ball c T, hsNormSq (Dv x)
  let B := 2 * t * ((C : ℝ) + V) / (t - s)
  let BA := B / s ^ (n - 2)
  let M := 2 / (s ^ (n - 1) * (t - s))
  let e : ℕ → ℝ := fun k => ∫ x in ball c t \ ball c s, ‖u k x - v x‖ ^ 2
  have hV : 0 ≤ V := integral_nonneg fun _ => hsNormSq_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBA : 0 ≤ BA := by dsimp only [BA]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have he (k : ℕ) : 0 ≤ e k := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨z, hz, hsmallz⟩ := exists_pos_mul_lt (by linarith only [hε] : 0 < ε / 2) (8 * L * B + 1)
  let η := min z (1 / 16 : ℝ)
  have hη : 0 < η := lt_min hz (by norm_num)
  have hηsmall : η < 1 / 8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηB : 8 * L * η * B < ε / 2 := by
    have hηz : η ≤ z := min_le_left _ _
    have hle := mul_le_mul_of_nonneg_left hηz (by positivity : 0 ≤ 8 * L * B + 1)
    nlinarith only [hle, hsmallz, hη]
  have hMe : Tendsto (fun k => M * e k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hDiff.const_mul M
  have hTube : Tendsto (fun k =>
      L * η ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt BA * Real.sqrt (M * e k) +
        L * η ^ (-(n : ℤ)) * (M * e k)) atTop (𝓝 0) := by
    have h := (hMe.sqrt.const_mul (L * η ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt BA)).add
      (hMe.const_mul (L * η ^ (-(n : ℤ))))
    simpa only [Real.sqrt_zero, mul_zero, zero_add] using h
  have hErr : Tendsto (fun k => 8 * L * t ^ (n - 2) * η⁻¹ * (M * e k))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hMe.const_mul (8 * L * t ^ (n - 2) * η⁻¹)
  have hρsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  filter_upwards [hTube.eventually_lt_const hρsq,
    hErr.eventually_lt_const (by linarith only [hε] : 0 < ε / 2)] with k hTubeK hErrK
  let a := s / 4
  let b := (t + T) / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hab : a < b := by dsimp only [a, b]; linarith only [hs, hst, htT]
  have hbT : b < T := by dsimp only [b]; linarith only [htT]
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  obtain ⟨H, hH, _hHuniq⟩ := ambient_radial_trace_existsUnique hn
    (hu k).to_memW12Loc ha hab (closedBall_subset_ball hbT)
  obtain ⟨G, hG, _hGuniq⟩ := ambient_radial_trace_existsUnique hn
    hv.to_memW12Loc ha hab (closedBall_subset_ball hbT)
  let P : ℝ → Prop := fun r =>
    (∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => u k (c + r • θ.val)) 2 σ,
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => u k (c + r • θ.val))) ∧
    (∀ hr : r ∈ Ioo a b,
      ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)) 2 σ,
        G ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)))
  have hP : ∀ᵐ r ∂volume.restrict (Ioo s t), P r := ae_restrict_of_ae (hH.and hG)
  obtain ⟨r, hr, hPr, hvS, huS, hvSN, huSN, _hAI, _hDI, hAE, hDE⟩ :=
    exists_sphere_pair_annular_bounds_with_property hn
      hv.to_memW12Loc (hu k).to_memW12Loc hvN (huN k)
      (closedBall_subset_ball htT) hs hst P hP
  have hrpos : 0 < r := hs.trans hr.1
  have hrT : r < T := hr.2.trans htT
  have harhalf : a ≤ r / 2 := by dsimp only [a]; linarith only [hs, hr.1]
  have hmidb : (r + T) / 2 ≤ b := by dsimp only [b]; linarith only [hr.2]
  have hrab : r ∈ Ioo a b := by
    dsimp only [a, b]
    constructor <;> linarith only [hs, hr.1, hr.2, htT]
  obtain ⟨husr, hHr⟩ := hPr.1 hrab
  obtain ⟨hvsr, hGr⟩ := hPr.2 hrab
  let A := ∫ θ : sphere (0 : Domain n) 1,
    ∑ i : Fin n,
      (‖(sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)) hvS i) θ‖ ^ 2 +
        ‖(sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => u k (c + r • θ.val)) huS i) θ‖ ^ 2) ∂σ
  let D := ∫ θ : sphere (0 : Domain n) 1, ‖u k (c + r • θ.val) - v (c + r • θ.val)‖ ^ 2 ∂σ
  have hA0 : 0 ≤ A := integral_nonneg fun _ =>
    Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD0 : 0 ≤ D := integral_nonneg fun _ => sq_nonneg _
  have hAsum : (∫ θ : sphere (0 : Domain n) 1,
      hsNormSq (fun i => (sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => v (c + r • θ.val)) hvS i) θ) +
      hsNormSq (fun i => (sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => u k (c + r • θ.val)) huS i) θ)
        ∂Measure.euclideanHausdorffMeasure (n - 1)) = A := by
    apply integral_congr_ae
    exact Eventually.of_forall fun θ : sphere (0 : Domain n) 1 => (Finset.sum_add_distrib).symm
  rw [hAsum] at hAE
  have hEk : (∫ x in ball c T, hsNormSq (Du k x)) ≤ C := by
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top (hEnergy k)
    have hI : IntegrableOn (fun x => hsNormSq (Du k x)) (ball c T) := (hu k).integrable_hsNormSq
    simpa only [dirichletEnergy_toReal hI, ENNReal.coe_toReal] using h
  have hpairI : IntegrableOn (fun x => hsNormSq (Dv x) + hsNormSq (Du k x)) (ball c T) :=
    hv.integrable_hsNormSq.add (hu k).integrable_hsNormSq
  have hIV : IntegrableOn (fun x => hsNormSq (Dv x)) (ball c T) := hv.integrable_hsNormSq
  have hIU : IntegrableOn (fun x => hsNormSq (Du k x)) (ball c T) := (hu k).integrable_hsNormSq
  have hIbound : (∫ x in ball c t \ ball c s, hsNormSq (Dv x) + hsNormSq (Du k x)) ≤
      (C : ℝ) + V := by
    have hsub : ball c t \ ball c s ⊆ ball c T :=
      sdiff_subset.trans (ball_subset_ball htT.le)
    have h := setIntegral_mono_set (s := ball c t \ ball c s) hpairI
      (Eventually.of_forall fun x => add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _))
      (Eventually.of_forall hsub)
    rw [integral_add hIV hIU] at h
    dsimp only [V]
    linarith only [h, hEk]
  have hScale : r * r ^ ((n : ℤ) - 3) = r ^ (n - 2) := by
    have hInt : (1 : ℤ) + ((n : ℤ) - 3) = ((n - 2 : ℕ) : ℤ) := by omega
    calc
      r * r ^ ((n : ℤ) - 3) = r ^ ((1 : ℤ) + ((n : ℤ) - 3)) := by
        rw [zpow_add₀ hrpos.ne', zpow_one]
      _ = r ^ (((n - 2 : ℕ) : ℤ)) := by rw [hInt]
      _ = r ^ (n - 2) := by rw [zpow_natCast]
  have hAwle : r ^ (n - 2) * A ≤ B := by
    have hAr := mul_le_mul_of_nonneg_left hAE hrpos.le
    rw [← mul_assoc, hScale] at hAr
    calc
      r ^ (n - 2) * A ≤ r * (2 * (∫ x in ball c t \ ball c s,
          hsNormSq (Dv x) + hsNormSq (Du k x)) / (t - s)) := hAr
      _ ≤ t * (2 * ((C : ℝ) + V) / (t - s)) := by
        apply mul_le_mul hr.2.le
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hIbound (by norm_num)) hwidth.le)
          (div_nonneg (mul_nonneg (by norm_num)
            (integral_nonneg fun x => add_nonneg (hsNormSq_nonneg _) (hsNormSq_nonneg _)))
              hwidth.le) ht.le
      _ = B := by dsimp only [B]; ring
  have hAle : A ≤ BA := by
    have hPow : s ^ (n - 2) ≤ r ^ (n - 2) := pow_le_pow_left₀ hs.le hr.1.le _
    have h := (mul_le_mul_of_nonneg_right hPow hA0).trans hAwle
    exact (le_div_iff₀ (pow_pos hs _)).mpr (by simpa only [mul_comm] using h)
  have hDsum : (∫ θ : sphere (0 : Domain n) 1,
      ‖v (c + r • θ.val) - u k (c + r • θ.val)‖ ^ 2 ∂Measure.euclideanHausdorffMeasure (n - 1)) = D := by
    apply integral_congr_ae
    exact Eventually.of_forall fun θ : sphere (0 : Domain n) 1 => congrArg (fun z : ℝ => z ^ 2) (norm_sub_rev _ _)
  have hbulk : (∫ x in ball c t \ ball c s, ‖v x - u k x‖ ^ 2) = e k := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrArg (fun z : ℝ => z ^ 2) (norm_sub_rev _ _)
  rw [hDsum, hbulk] at hDE
  have hDle : D ≤ M * e k := by
    have hsD : s ^ (n - 1) * D ≤ 2 * e k / (t - s) :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hr.1.le _) hD0).trans hDE
    calc
      D ≤ (2 * e k / (t - s)) / s ^ (n - 1) := (le_div_iff₀ (pow_pos hs _)).mpr (by
        simpa only [mul_comm] using hsD)
      _ = M * e k := by simp only [M, div_eq_mul_inv, mul_inv_rev]; ring
  have htube : L * η ^ ((1 : ℤ) - (n : ℤ)) * Real.sqrt A * Real.sqrt D +
      L * η ^ (-(n : ℤ)) * D < ρ ^ 2 := by
    have hSqrt : Real.sqrt A * Real.sqrt D ≤ Real.sqrt BA * Real.sqrt (M * e k) :=
      mul_le_mul (Real.sqrt_le_sqrt hAle) (Real.sqrt_le_sqrt hDle)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hFirst := mul_le_mul_of_nonneg_left hSqrt
      (mul_nonneg hL.le (zpow_nonneg hη.le ((1 : ℤ) - (n : ℤ))))
    have hSecond := mul_le_mul_of_nonneg_left hDle
      (mul_nonneg hL.le (zpow_nonneg hη.le (-(n : ℤ))))
    nlinarith only [hFirst, hSecond, hTubeK]
  have hcmp := hop Ω c r T η a b hrpos hrT hη hηsmall harhalf hmidb hclosed
    (u k) v (Du k) Dv (hu k) hv (huN k) hvN (hmin k) huS hvS huSN hvSN
    H G hH hG hrab.1.le hrab.2.le hHr hGr htube
  have hinner : (∫ x in ball c s, hsNormSq (Du k x)) ≤
      ∫ x in ball c r, hsNormSq (Du k x) :=
    setIntegral_mono_set ((hu k).integrable_hsNormSq.mono_set (ball_subset_ball hrT.le))
      (Eventually.of_forall fun x => hsNormSq_nonneg _) (Eventually.of_forall (ball_subset_ball hr.1.le))
  have houter : (∫ x in ball c r, hsNormSq (Dv x)) ≤
      ∫ x in ball c t, hsNormSq (Dv x) :=
    setIntegral_mono_set (hv.integrable_hsNormSq.mono_set (ball_subset_ball htT.le))
      (Eventually.of_forall fun x => hsNormSq_nonneg _) (Eventually.of_forall (ball_subset_ball hr.2.le))
  have hCostA := mul_le_mul_of_nonneg_left hAwle
    (by positivity : 0 ≤ 8 * L * η)
  have hWeightedD : r ^ (n - 2) * D ≤ t ^ (n - 2) * (M * e k) :=
    mul_le_mul (pow_le_pow_left₀ hrpos.le hr.2.le _) hDle hD0 (pow_nonneg ht.le _)
  have hCostD := mul_le_mul_of_nonneg_left hWeightedD
    (by positivity : 0 ≤ 8 * L * η⁻¹)
  have hCost : 8 * L * r ^ (n - 2) * (η * A + η⁻¹ * D) ≤
      8 * L * η * B + 8 * L * t ^ (n - 2) * η⁻¹ * (M * e k) := by
    calc
      _ = (8 * L * η) * (r ^ (n - 2) * A) +
          (8 * L * η⁻¹) * (r ^ (n - 2) * D) := by ring
      _ ≤ (8 * L * η) * B + (8 * L * η⁻¹) * (t ^ (n - 2) * (M * e k)) :=
        add_le_add hCostA hCostD
      _ = _ := by ring
  linarith only [hinner, hcmp, houter, hCost, hηB, hErrK]

end StratificationTheory.Compactness
