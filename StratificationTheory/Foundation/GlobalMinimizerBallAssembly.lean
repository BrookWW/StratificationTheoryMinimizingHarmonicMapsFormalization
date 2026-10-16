module

public import StratificationTheory.Foundation.MinimizerAECongruence
public import HarmonicMaps.SobolevRestriction

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal

namespace StratificationTheory

private theorem compact_subset_nat_origin_ball {n : ℕ} {K : Set (Domain n)}
    (hK : IsCompact K) : ∃ j : ℕ, K ⊆ ball (0 : Domain n) ((j : ℝ) + 1) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Domain n)
  obtain ⟨j, hj⟩ := exists_nat_gt R
  exact ⟨j, hR.trans (ball_subset_ball (by linarith))⟩

private theorem localL2_locallyIntegrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {Ω : OpenDomain n} {f : Domain n → E}
    (hf : LocallyMemL2 Ω f) : LocallyIntegrableOn f Ω.val volume := by
  apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
  intro K hKΩ hK
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hf K hK hKΩ).integrable (by norm_num)

private theorem integral_smul_support {n q : ℕ} {ψ : Domain n → ℝ}
    {S : Set (Domain n)} (f : Domain n → Ambient q) (hs : tsupport ψ ⊆ S) :
    (∫ x in S, ψ x • f x) = ∫ x, ψ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_smul]

/-- Actual local minimizing graphs on expanding balls, identified almost
everywhere with one displayed pair on their closed cores, assemble that same
pair into a global locally Sobolev, target-valued local minimizer. -/
theorem global_minimizer_of_ae_expanding_ball_family {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
    (v : ℕ → Domain n → Ambient q) (Dv : ℕ → Domain n → Gradient n q)
    (hW : ∀ j : ℕ, MemW12Loc
      (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j) (Dv j))
    (hN : ∀ j : ℕ, TakesValuesIn N
      (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j))
    (hMin : ∀ j : ℕ, IsLocallyEnergyMinimizing N
      (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j) (Dv j))
    (hMap : ∀ j : ℕ, f =ᵐ[volume.restrict
      (closedBall (0 : Domain n) ((j : ℝ) + 1))] v j)
    (hGrad : ∀ j : ℕ, Df =ᵐ[volume.restrict
      (closedBall (0 : Domain n) ((j : ℝ) + 1))] Dv j) :
    MemW12Loc ⟨univ, isOpen_univ⟩ f Df ∧
      TakesValuesIn N ⟨univ, isOpen_univ⟩ f ∧
      IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ f Df := by
  have hSmall (j : ℕ) : ball (0 : Domain n) ((j : ℝ) + 1) ⊆
      (ballDomain (0 : Domain n) ((j : ℝ) + 2)).val :=
    ball_subset_ball (by linarith)
  have hMapSmall (j : ℕ) : (v j) =ᵐ[volume.restrict
      (ball (0 : Domain n) ((j : ℝ) + 1))] f :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall (hMap j).symm
  have hGradSmall (j : ℕ) : (Dv j) =ᵐ[volume.restrict
      (ball (0 : Domain n) ((j : ℝ) + 1))] Df :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall (hGrad j).symm
  have hFinite (c : Domain n) (r : ℝ) : MemW12 (ballDomain c r) f Df := by
    obtain ⟨j, hj⟩ := compact_subset_nat_origin_ball (isCompact_closedBall c r)
    have hWcr := (hW j).memW12_ball (hj.trans (hSmall j))
    exact hWcr.congr_ae
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hj) (hMapSmall j))
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hj) (hGradSmall j))
  have hFLp : LocallyMemL2 (⟨univ, isOpen_univ⟩ : OpenDomain n) f := by
    intro K hK _hKΩ
    obtain ⟨j, hj⟩ := compact_subset_nat_origin_ball hK
    exact ((hW j).2.1 K hK (hj.trans (hSmall j))).ae_eq
      (ae_restrict_of_ae_restrict_of_subset hj (hMapSmall j))
  have hDLp (i : Fin n) : LocallyMemL2
      (⟨univ, isOpen_univ⟩ : OpenDomain n) (fun x => Df x i) := by
    intro K hK _hKΩ
    obtain ⟨j, hj⟩ := compact_subset_nat_origin_ball hK
    exact ((hW j).2.2 i K hK (hj.trans (hSmall j))).ae_eq
      ((ae_restrict_of_ae_restrict_of_subset hj (hGradSmall j)).mono fun x hx => congrFun hx i)
  have hGlobalW : MemW12Loc (⟨univ, isOpen_univ⟩ : OpenDomain n) f Df := by
    refine ⟨⟨localL2_locallyIntegrable hFLp,
      (fun i => localL2_locallyIntegrable (hDLp i)), ?_⟩, hFLp, hDLp⟩
    intro i ψ hψ hcψ _hsψ
    obtain ⟨j, hj⟩ := compact_subset_nat_origin_ball hcψ
    have hIdentity := (hFinite 0 ((j : ℝ) + 1)).1.2.2 i ψ hψ hcψ hj
    change (∫ x in ball (0 : Domain n) ((j : ℝ) + 1), coordinateDerivative ψ hψ i x • f x) =
      -(∫ x in ball (0 : Domain n) ((j : ℝ) + 1), ψ x • Df x i) at hIdentity
    have hDerivative : tsupport (coordinateDerivative ψ hψ i) ⊆
        ball (0 : Domain n) ((j : ℝ) + 1) :=
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hj
    rw [integral_smul_support f hDerivative,
      integral_smul_support (fun x => Df x i) hj] at hIdentity
    simpa only [Measure.restrict_univ] using hIdentity
  have hCover : (⋃ j : ℕ, ball (0 : Domain n) ((j : ℝ) + 1)) = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < (j : ℝ) + 1 by linarith)
  have hGlobalN : TakesValuesIn N (⟨univ, isOpen_univ⟩ : OpenDomain n) f := by
    change ∀ᵐ x ∂volume.restrict (univ : Set (Domain n)), f x ∈ N.carrierSet
    rw [← hCover]
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro j
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hSmall j) (hN j), hMapSmall j]
      with x hxN hx
    rw [← hx]
    exact hxN
  refine ⟨hGlobalW, hGlobalN, ?_⟩
  intro c r hr _hclosed z Dz hz hzN hboundary
  obtain ⟨j, hj⟩ := compact_subset_nat_origin_ball (isCompact_closedBall c r)
  have hMinSmall : IsLocallyEnergyMinimizing N
      (ballDomain (0 : Domain n) ((j : ℝ) + 1)) (v j) (Dv j) := by
    intro a s hs hclosed w Dw hw hwN hb
    exact hMin j a s hs (hclosed.trans (hSmall j)) w Dw hw hwN hb
  have hMinNew := hMinSmall.congr_ae (hMapSmall j) (hGradSmall j)
  exact hMinNew c r hr hj z Dz hz hzN hboundary

end StratificationTheory
