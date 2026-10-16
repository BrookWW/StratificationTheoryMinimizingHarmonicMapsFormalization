module

public import StratificationTheory.Interpolation.SpherePairPrismSlab
public import StratificationTheory.Foundation.ConstantTimePrismExtension
public import StratificationTheory.Foundation.OriginalBallCenteredSpatialData
public import StratificationTheory.Foundation.FiniteCoordinateBoxVolume

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- An original sphere pair in every ambient dimension at least three
produces one quantitative weak prism map and its complete original time
trace classes. Its fixed time extension retains the original endpoint
maps outside the interpolation interval and every original raw ray. -/
theorem exists_sphere_pair_extended_prism_slab {n q : ℕ}
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
    let U : OpenDomain m :=
      ⟨⋂ j : Fin m, (EuclideanSpace.proj j) ⁻¹' Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ),
        isOpen_iInter_of_finite (fun j : Fin m => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := 1)
    let Ω : OpenDomain (m + 1) :=
      ⟨{x | (e x).1 ∈ U.val ∧ (e x).2 0 ∈ Ioo (0 : ℝ) ε},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let Ωext : OpenDomain (m + 1) :=
      ⟨{x | (e x).1 ∈ U.val ∧ (e x).2 0 ∈ Ioo (-1 : ℝ) 1},
        (U.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    ∃ (radial : Fin 2 → Domain m → Ambient q)
      (Dradial : Fin 2 → Domain m → Gradient m q)
      (W : Domain (m + 1) → Ambient q) (DW : Domain (m + 1) → Gradient (m + 1) q)
      (M : ℝ) (Htime : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U.val))),
      let Wext := fun x : Domain (m + 1) =>
        if (e x).2 0 < 0 then radial 0 (e x).1 else
          if (e x).2 0 < ε then W x else radial 1 (e x).1
      let Dext := fun (x : Domain (m + 1)) (i : Fin (m + 1)) =>
        if (e x).2 0 < 0 then Fin.lastCases (0 : Ambient q) (fun j => Dradial 0 (e x).1 j) i else
          if (e x).2 0 < ε then DW x i else
            Fin.lastCases (0 : Ambient q) (fun j => Dradial 1 (e x).1 j) i
      (∀ l, MemW12 (ballDomain (0 : Domain m) R) (radial l) (Dradial l)) ∧
      (∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain m) R), radial l x ∈ N) ∧
      (∀ (l : Fin 2) (r : PositiveRadius) (θ : sphere (0 : Domain m) 1),
        radial l (r.val • θ.val) = u l θ) ∧
      MemW12 Ω W DW ∧ (0 ≤ M ∧ ∀ z ∈ N, ‖z‖ ≤ M) ∧
      (∀ᵐ x ∂volume.restrict Ω.val, ‖W x‖ ≤ M) ∧
      ENNReal.ofReal (∫ x in Ω.val, hsNormSq (DW x)) ≤
        K * (ENNReal.ofReal ε * ENNReal.ofReal (CE * A) +
          (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal (CD * D)) ∧
      (∀ᵐ x ∂volume.restrict Ω.val, (infDist (W x) N) ^ 2 ≤ BTube) ∧
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
        ∃ hs : MemLp (fun x : Domain m =>
          W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
          Htime ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x =>
            W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      (∃ hw₀ : MemLp (radial 0) 2 (volume.restrict U.val),
        Htime ⟨0, le_rfl, hε.le⟩ = hw₀.toLp (radial 0)) ∧
      (∃ hw₁ : MemLp (radial 1) 2 (volume.restrict U.val),
        Htime ⟨ε, hε.le, le_rfl⟩ = hw₁.toLp (radial 1)) ∧
      MemW12 Ωext Wext Dext ∧
      MemW12 (ballDomain (0 : Domain (m + 1)) (3 / 4 : ℝ)) Wext Dext ∧
      (∀ x, (e x).2 0 ∈ Ioo (0 : ℝ) ε → Wext x = W x ∧ Dext x = DW x) ∧
      (∫ x in Ω.val, hsNormSq (Dext x)) = ∫ x in Ω.val, hsNormSq (DW x) := by
  classical
  intro m R J A D CE CD K BTube U e Ω Ωext
  obtain ⟨radial, Dradial, W, DW, M, Htime, hSob, hNr, hRays,
    hW, hM, hNorm, hEnergy, hTube, hRaw, hEnd₀, hEnd₁⟩ :=
    exists_sphere_pair_centered_prism_slab u hu N hN hTarget ε hε hεsmall
  refine ⟨radial, Dradial, W, DW, M, Htime, ?_⟩
  intro Wext Dext
  have hRadius : ((n + 1 : ℕ) : ℝ) + 3 = R := by dsimp only [R]; push_cast; ring
  have hSpatial := original_ball_centered_cube_data (n := n + 1) radial Dradial
    (fun l => by simpa only [hRadius] using hSob l) N
    (fun l => by simpa only [hRadius] using hNr l)
  letI : IsFiniteMeasure ((volume : Measure (Domain m)).restrict U.val) :=
    isFiniteMeasure_restrict.mpr (volume_finite_coordinate_box_ne_top m
      (fun _ => -(3 / 4 : ℝ)) (fun _ => (3 / 4 : ℝ)))
  have hAux := memW12_constant_time_prism_extension U radial Dradial hSpatial.1 hε
    (lt_trans hεsmall (by norm_num : (1 / 8 : ℝ) < 1)) W DW hW Htime hRaw hEnd₀ hEnd₁
  have hFull : MemW12 Ωext Wext Dext := by
    convert hAux.1 using 1 <;> rfl
  have hBallSub : ball (0 : Domain (m + 1)) (3 / 4 : ℝ) ⊆ Ωext.val := by
    intro x hx
    have hn : ‖x‖ < (3 / 4 : ℝ) := mem_ball_zero_iff.mp hx
    constructor
    · rw [mem_iInter]
      intro j
      have hj := PiLp.norm_apply_le x j.castSucc
      rw [Real.norm_eq_abs] at hj
      have ha := abs_le.mp hj
      change -(3 / 4 : ℝ) < x j.castSucc ∧ x j.castSucc < (3 / 4 : ℝ)
      constructor <;> linarith [ha.1, ha.2]
    · have hj := PiLp.norm_apply_le x (Fin.natAdd m (0 : Fin 1))
      rw [Real.norm_eq_abs] at hj
      have ha := abs_le.mp hj
      change (-1 : ℝ) < x (Fin.natAdd m (0 : Fin 1)) ∧ x (Fin.natAdd m (0 : Fin 1)) < 1
      constructor <;> linarith [ha.1, ha.2]
  have hBall : MemW12 (ballDomain (0 : Domain (m + 1)) (3 / 4 : ℝ)) Wext Dext :=
    ⟨hFull.1.mono hBallSub, hFull.2.1.mono_measure (Measure.restrict_mono_set volume hBallSub),
      fun i => (hFull.2.2 i).mono_measure (Measure.restrict_mono_set volume hBallSub)⟩
  refine ⟨hSob, hNr, hRays, hW, hM, hNorm, hEnergy, hTube, hRaw, hEnd₀, hEnd₁, hFull, hBall, ?_, ?_⟩
  · intro x hx
    constructor
    · simp only [Wext, if_neg (not_lt.mpr hx.1.le), if_pos hx.2]
    · funext i
      simp only [Dext, if_neg (not_lt.mpr hx.1.le), if_pos hx.2]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
    congr 1
    funext i
    simp only [Dext, if_neg (not_lt.mpr hx.2.1.le), if_pos hx.2.2]

end StratificationTheory
