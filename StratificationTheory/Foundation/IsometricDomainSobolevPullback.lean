module

public import StratificationTheory.Foundation.IsometricSobolevPullback
public import HarmonicMaps.SobolevLemmas
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Isometric pullback on finite open domains

An actual Euclidean isometry pulls the original weak pair back to the full
inverse-image domain. The same displayed columns preserve native HS energy
and arbitrary original a.e. value properties.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff BigOperators
namespace StratificationTheory

/-- A Euclidean source isometry pulls back the actual full weak graph on a
finite open domain to its actual inverse-image domain. -/
theorem memW12_isometric_preimage {n q : ℕ} {Ω : OpenDomain n}
    (hfinite : (volume : Measure (Domain n)) Ω.val ≠ ⊤)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (Q : Domain n ≃ₗᵢ[ℝ] Domain n) :
    let Ω' : OpenDomain n := ⟨Q ⁻¹' Ω.val, Ω.property.preimage Q.continuous⟩
    MemW12 Ω' (u ∘ Q)
      (fun x i => ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • Du (Q x) j) := by
  intro Ω'
  let D : Domain n → Gradient n q :=
    fun x i => ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • Du (Q x) j
  have hMP : MeasurePreserving Q (volume.restrict Ω'.val) (volume.restrict Ω.val) :=
    Q.measurePreserving.restrict_preimage Ω.property.measurableSet
  have hEmb : MeasurableEmbedding Q := Q.toHomeomorph.measurableEmbedding
  have hΩfinite : (volume : Measure (Domain n)) Ω'.val ≠ ⊤ := by
    change (volume : Measure (Domain n)) (Q ⁻¹' Ω.val) ≠ ⊤
    rw [Q.measurePreserving.measure_preimage Ω.property.measurableSet.nullMeasurableSet]
    exact hfinite
  letI : IsFiniteMeasure (volume.restrict Ω'.val) := isFiniteMeasure_restrict.mpr hΩfinite
  have huL : MemLp (u ∘ Q) 2 (volume.restrict Ω'.val) := hu.2.1.comp_measurePreserving hMP
  have hDL (i : Fin n) : MemLp (fun x => D x i) 2 (volume.restrict Ω'.val) := by
    exact memLp_finsetSum Finset.univ (fun j _ =>
      ((hu.2.2 j).comp_measurePreserving hMP).const_smul ((Q (EuclideanSpace.single i 1)) j))
  have huI : IntegrableOn (u ∘ Q) Ω'.val := huL.integrable (by norm_num)
  have hDI (i : Fin n) : IntegrableOn (fun x => D x i) Ω'.val := (hDL i).integrable (by norm_num)
  refine ⟨⟨huI.locallyIntegrableOn, fun i => (hDI i).locallyIntegrableOn, ?_⟩, huL, hDL⟩
  intro i φ hφ hcφ hsφ
  let ψ : Domain n → ℝ := φ ∘ Q.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp Q.symm.toContinuousLinearEquiv.contDiff
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph Q.symm.toHomeomorph
  have hsψ : tsupport ψ ⊆ Ω.val := by
    change tsupport (φ ∘ Q.symm.toHomeomorph) ⊆ Ω.val
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have h := hsφ hy
    change Q (Q.symm y) ∈ Ω.val at h
    simpa only [Q.apply_symm_apply] using h
  have hψQ (x : Domain n) : ψ (Q x) = φ x := by
    simp only [ψ, Function.comp_apply, Q.symm_apply_apply]
  have hbasis (v : Domain n) : ∑ j : Fin n, v j • EuclideanSpace.single j 1 = v := by
    ext k
    simp [Pi.single_apply]
  have hchain (x : Domain n) :
      (∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j * coordinateDerivative ψ hψ j (Q x)) =
        coordinateDerivative φ hφ i x := by
    have hder : fderiv ℝ ψ (Q x) = (fderiv ℝ φ x).comp
        Q.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
      have h := (hφ.differentiable (by simp) (Q.symm (Q x))).hasFDerivAt.comp (Q x)
        Q.symm.toContinuousLinearEquiv.hasFDerivAt
      simpa only [Q.symm_apply_apply, Function.comp_def, ψ,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h.fderiv
    calc
      _ = (fderiv ℝ ψ (Q x)) (∑ j : Fin n,
          (Q (EuclideanSpace.single i 1)) j • EuclideanSpace.single j 1) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul, coordinateDerivative]
      _ = (fderiv ℝ ψ (Q x)) (Q (EuclideanSpace.single i 1)) := congrArg _ (hbasis _)
      _ = _ := by
        rw [hder, ContinuousLinearMap.comp_apply]
        change (fderiv ℝ φ x) (Q.symm (Q (EuclideanSpace.single i 1))) = _
        rw [Q.symm_apply_apply]
        rfl
  have hA (j : Fin n) : IntegrableOn
      (fun x => coordinateDerivative ψ hψ j (Q x) • u (Q x)) Ω'.val :=
    hMP.integrable_comp_of_integrable (hu.1.integrable_test_derivative j hψ hcψ hsψ)
  have hB (j : Fin n) : IntegrableOn (fun x => ψ (Q x) • Du (Q x) j) Ω'.val :=
    hMP.integrable_comp_of_integrable (hu.1.integrable_test_gradient j hψ hcψ hsψ)
  have hsource (j : Fin n) :
      (∫ x in Ω'.val, coordinateDerivative ψ hψ j (Q x) • u (Q x)) =
        -(∫ x in Ω'.val, ψ (Q x) • Du (Q x) j) := by
    rw [hMP.integral_comp hEmb (fun y => coordinateDerivative ψ hψ j y • u y),
      hMP.integral_comp hEmb (fun y => ψ y • Du y j)]
    exact hu.1.2.2 j ψ hψ hcψ hsψ
  have hleft (x : Domain n) : coordinateDerivative φ hφ i x • u (Q x) =
      ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j •
        (coordinateDerivative ψ hψ j (Q x) • u (Q x)) := by
    rw [← hchain, Finset.sum_smul]
    simp only [mul_smul]
  have hright (x : Domain n) : φ x • D x i =
      ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • (ψ (Q x) • Du (Q x) j) := by
    dsimp only [D]
    rw [Finset.smul_sum]
    simp only [hψQ, smul_smul, mul_comm]
  change (∫ x in Ω'.val, coordinateDerivative φ hφ i x • u (Q x)) =
    -(∫ x in Ω'.val, φ x • D x i)
  simp_rw [hleft, hright]
  have hSumA :
      (∫ x in Ω'.val, ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j •
        (coordinateDerivative ψ hψ j (Q x) • u (Q x))) =
      ∑ j : Fin n, ∫ x in Ω'.val, (Q (EuclideanSpace.single i 1)) j •
        (coordinateDerivative ψ hψ j (Q x) • u (Q x)) :=
    integral_finsetSum Finset.univ (fun j _ => Integrable.smul ((Q (EuclideanSpace.single i 1)) j) (hA j))
  have hSumB :
      (∫ x in Ω'.val, ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j •
        (ψ (Q x) • Du (Q x) j)) =
      ∑ j : Fin n, ∫ x in Ω'.val, (Q (EuclideanSpace.single i 1)) j •
        (ψ (Q x) • Du (Q x) j) :=
    integral_finsetSum Finset.univ (fun j _ => Integrable.smul ((Q (EuclideanSpace.single i 1)) j) (hB j))
  rw [hSumA, hSumB]
  simp_rw [integral_smul, hsource, smul_neg]
  rw [Finset.sum_neg_distrib]

/-- The same open-domain isometric pullback retains exact native HS and
Dirichlet energies, as well as arbitrary original a.e. value properties. -/
theorem memW12_isometric_preimage_energy {n q : ℕ} {Ω : OpenDomain n}
    (hfinite : (volume : Measure (Domain n)) Ω.val ≠ ⊤)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (Q : Domain n ≃ₗᵢ[ℝ] Domain n) :
    let Ω' : OpenDomain n := ⟨Q ⁻¹' Ω.val, Ω.property.preimage Q.continuous⟩
    let D : Domain n → Gradient n q :=
      fun x i => ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • Du (Q x) j
    MemW12 Ω' (u ∘ Q) D ∧
      (∀ x, hsNormSq (D x) = hsNormSq (Du (Q x))) ∧
      (∫ x in Ω'.val, hsNormSq (D x)) = ∫ x in Ω.val, hsNormSq (Du x) ∧
      dirichletEnergy D Ω'.val = dirichletEnergy Du Ω.val ∧
      ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict Ω.val, P (u y)) →
        ∀ᵐ x ∂volume.restrict Ω'.val, P ((u ∘ Q) x) := by
  intro Ω' D
  have hW : MemW12 Ω' (u ∘ Q) D := memW12_isometric_preimage hfinite hu Q
  have hHS (x : Domain n) : hsNormSq (D x) = hsNormSq (Du (Q x)) :=
    hsNormSq_source_isometry Q (Du (Q x))
  have hMP : MeasurePreserving Q (volume.restrict Ω'.val) (volume.restrict Ω.val) :=
    Q.measurePreserving.restrict_preimage Ω.property.measurableSet
  have hE : (∫ x in Ω'.val, hsNormSq (D x)) = ∫ x in Ω.val, hsNormSq (Du x) := by
    calc
      _ = ∫ x in Ω'.val, hsNormSq (Du (Q x)) := integral_congr_ae (Eventually.of_forall hHS)
      _ = _ := hMP.integral_comp Q.toHomeomorph.measurableEmbedding (fun x => hsNormSq (Du x))
  refine ⟨hW, hHS, hE, ?_, ?_⟩
  · rw [dirichletEnergy_eq_ofReal_integral hW.integrable_hsNormSq,
      dirichletEnergy_eq_ofReal_integral hu.integrable_hsNormSq, hE]
  · intro P hP
    exact hMP.quasiMeasurePreserving.ae hP

end StratificationTheory
