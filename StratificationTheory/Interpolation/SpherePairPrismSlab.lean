module

public import StratificationTheory.Interpolation.OriginalCenteredPrismSlab
public import StratificationTheory.Foundation.JointRadialPairData

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- An original sphere pair in every ambient dimension at least three
produces one quantitative weak prism map and its complete original time
trace classes. The original endpoint extensions retain every raw ray. -/
theorem exists_sphere_pair_centered_prism_slab {n q : ℕ}
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
    ∃ (radial : Fin 2 → Domain m → Ambient q)
      (Dradial : Fin 2 → Domain m → Gradient m q)
      (W : Domain (m + 1) → Ambient q) (DW : Domain (m + 1) → Gradient (m + 1) q)
      (M : ℝ) (Htime : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U.val))),
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
        Htime ⟨ε, hε.le, le_rfl⟩ = hw₁.toLp (radial 1)) := by
  intro m R J A D CE CD K BTube U e Ω
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨radial, Dradial, hSob, hRays, _hGradient, hBallEnergy, hBallDifference, hValues⟩ :=
    exists_joint_radial_pair_ball_data (by omega : 3 ≤ n + 3) u hu hR
  have hGu : Integrable (fun θ : sphere (0 : Domain m) 1 =>
      hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ m) (u 0) (hu 0) i) θ))
        (Measure.euclideanHausdorffMeasure (m - 1)) :=
    by
      unfold hsNormSq
      exact integrable_finsetSum Finset.univ fun i _ =>
        (Lp.memLp (sphereGradient (by omega : 2 ≤ m) (u 0) (hu 0) i)).integrable_norm_pow
          (by decide : (2 : ℕ) ≠ 0)
  have hGv : Integrable (fun θ : sphere (0 : Domain m) 1 =>
      hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ m) (u 1) (hu 1) i) θ))
        (Measure.euclideanHausdorffMeasure (m - 1)) :=
    by
      unfold hsNormSq
      exact integrable_finsetSum Finset.univ fun i _ =>
        (Lp.memLp (sphereGradient (by omega : 2 ≤ m) (u 1) (hu 1) i)).integrable_norm_pow
          (by decide : (2 : ℕ) ≠ 0)
  have hSphereEnergy : (∫ θ : sphere (0 : Domain m) 1,
      hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ m) (u 0) (hu 0) i) θ)
        ∂Measure.euclideanHausdorffMeasure (m - 1)) +
      (∫ θ : sphere (0 : Domain m) 1,
        hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ m) (u 1) (hu 1) i) θ)
          ∂Measure.euclideanHausdorffMeasure (m - 1)) = A :=
    (integral_add hGu hGv).symm
  have hBallEnergy' : ((∫ x in ball (0 : Domain m) R, hsNormSq (Dradial 0 x)) +
      ∫ x in ball (0 : Domain m) R, hsNormSq (Dradial 1 x)) = CE * A := by
    rw [hBallEnergy, hSphereEnergy]
  have hBallDifference' : (∫ x in ball (0 : Domain m) R, ‖radial 0 x - radial 1 x‖ ^ 2) = CD * D :=
    hBallDifference
  have hRadius : ((n + 1 : ℕ) : ℝ) + 3 = R := by dsimp only [R]; push_cast; ring
  obtain ⟨W, DW, M, Htime, hW, hM, hNorm, hEnergy, hTube, hRaw, hEnd₀, hEnd₁⟩ :=
    exists_original_ball_centered_prism_slab_with_time_trace (n := n + 1)
      radial Dradial (by intro l; simpa only [hRadius] using hSob l)
      N hN (by intro l; simpa only [hRadius] using hValues l (fun z => z ∈ N) (hTarget l))
      ε hε hεsmall
  refine ⟨radial, Dradial, W, DW, M, Htime, hSob,
    (fun l => hValues l (fun z => z ∈ N) (hTarget l)), hRays,
    hW, hM, hNorm, ?_, ?_, hRaw, hEnd₀, hEnd₁⟩
  · simpa only [hRadius, hBallEnergy', hBallDifference', m, J, K, CE, CD, A, D, R,
      Ω, U, e, show n + 3 - 1 = n + 2 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel_right] using hEnergy
  · simpa only [hRadius, hBallEnergy', hBallDifference', m, J, BTube, CE, CD, A, D, R,
      Ω, U, e, show n + 3 - 1 = n + 2 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel_right] using hTube

end StratificationTheory
