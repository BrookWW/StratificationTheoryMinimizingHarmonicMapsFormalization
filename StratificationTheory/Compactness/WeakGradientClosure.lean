module

public import HarmonicMaps.SobolevLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import StratificationTheory.Compactness.L2PairingConvergence

/-!
# Weak-gradient closure

Strong L2 map convergence and weak L2 convergence of all displayed columns
preserve the distributional derivative identities. The local theorem works on
arbitrary open domains by restricting each smooth test to its compact support.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StratificationTheory.Compactness

private theorem scalar_test_memLp {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {ψ : α → ℝ} (hψ : MemLp ψ ∞ μ) (c : E) :
    MemLp (fun x => ψ x • c) 2 μ := by
  exact (memLp_const c : MemLp (fun _ : α => c) 2 μ).smul hψ

private theorem integral_pairing_scalar_test {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {ψ : α → ℝ} (hψ : MemLp ψ ∞ μ)
    {f : α → E} (hf : MemLp f 2 μ) (c : E) :
    (∫ x, inner ℝ (f x) ((scalar_test_memLp hψ c).toLp (fun y => ψ y • c) x) ∂μ) =
        inner ℝ c (∫ x, ψ x • f x ∂μ) := by
  have hi := integral_inner (𝕜 := ℝ) ((hf.integrable (by norm_num)).smul_of_top_right hψ) c
  simp only [Pi.smul_apply'] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [(scalar_test_memLp hψ c).coeFn_toLp] with x hx
  rw [hx, real_inner_smul_right, real_inner_smul_right, real_inner_comm (f x) c]

/-- Strong convergence of maps and weak L2 convergence of their displayed
columns preserve the weak Sobolev graph on a finite-measure open domain. -/
theorem memW12_of_strong_map_weak_gradient_limit {n q : ℕ} {Ω : OpenDomain n}
    [IsFiniteMeasure (volume.restrict Ω.val)]
    {f : ℕ → Domain n → Ambient q} {Df : ℕ → Domain n → Gradient n q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hf : ∀ k, MemW12 Ω (f k) (Df k))
    (hu : MemLp u 2 (volume.restrict Ω.val))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict Ω.val))
      atTop (𝓝 0))
    (hDconv : ∀ (i : Fin n) (v : Lp (Ambient q) 2 (volume.restrict Ω.val)),
      Tendsto (fun k => ∫ x in Ω.val, inner ℝ (Df k x i) (v x))
        atTop (𝓝 (∫ x in Ω.val, inner ℝ (Du x i) (v x)))) :
    MemW12 Ω u Du := by
  refine ⟨⟨IntegrableOn.locallyIntegrableOn (hu.integrable (by norm_num)),
    (fun i => IntegrableOn.locallyIntegrableOn ((hDu i).integrable (by norm_num))), ?_⟩,
    hu, hDu⟩
  intro i φ hφ hcompact hsupport
  apply ext_inner_left ℝ
  intro c
  have hφtop : MemLp φ ∞ (volume.restrict Ω.val) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcompact _
  have hδtop : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict Ω.val) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcompact.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have hl := tendsto_integral_inner_of_L2_convergence (fun k => (hf k).2.1) hu
    (scalar_test_memLp hδtop c) hconv
  have hl' : Tendsto (fun k => inner ℝ c
      (∫ x in Ω.val, coordinateDerivative φ hφ i x • f k x)) atTop
      (𝓝 (inner ℝ c (∫ x in Ω.val, coordinateDerivative φ hφ i x • u x))) := by
    have heq (g : Domain n → Ambient q) (hg : MemLp g 2 (volume.restrict Ω.val)) :
        (∫ x in Ω.val, inner ℝ (g x) (coordinateDerivative φ hφ i x • c)) =
          inner ℝ c (∫ x in Ω.val, coordinateDerivative φ hφ i x • g x) := by
      have hi := integral_inner (𝕜 := ℝ)
        ((hg.integrable (by norm_num)).smul_of_top_right hδtop) c
      simp only [Pi.smul_apply'] at hi
      rw [← hi]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm (g x) c]
    simpa only [heq _ ((hf _).2.1), heq u hu] using hl
  have hr := hDconv i ((scalar_test_memLp hφtop c).toLp (fun x => φ x • c))
  have hr' : Tendsto (fun k => inner ℝ c (-(∫ x in Ω.val, φ x • Df k x i)))
      atTop (𝓝 (inner ℝ c (-(∫ x in Ω.val, φ x • Du x i)))) := by
    have h := hr.neg
    simpa only [integral_pairing_scalar_test hφtop ((hf _).2.2 i) c,
      integral_pairing_scalar_test hφtop (hDu i) c, inner_neg_right] using h
  exact tendsto_nhds_unique hl'
    (hr'.congr fun k => congrArg (inner ℝ c) ((hf k).1.2.2 i φ hφ hcompact hsupport).symm)

private theorem setIntegral_smul_eq_integral {n q : ℕ}
    {ψ : Domain n → ℝ} {U : Set (Domain n)} (f : Domain n → Ambient q)
    (hsupport : tsupport ψ ⊆ U) :
    (∫ x in U, ψ x • f x) = ∫ x, ψ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hnot : x ∉ tsupport ψ := fun hmem => hx (hsupport hmem)
  simp only [image_eq_zero_of_notMem_tsupport hnot, zero_smul]

private theorem locallyIntegrableOn_of_localL2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {Ω : OpenDomain n} {f : Domain n → E}
    (hf : LocallyMemL2 Ω f) : LocallyIntegrableOn f Ω.val volume := by
  apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
  intro K hKΩ hK
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hf K hK hKΩ).integrable (by norm_num)

/-- Strong local map convergence and weak local convergence of the displayed
columns preserve their distributional derivative identities on an arbitrary
open domain. Every test is localized to its own compact support. -/
theorem memW12Loc_of_strong_map_weak_gradient_limit {n q : ℕ} {Ω : OpenDomain n}
    {f : ℕ → Domain n → Ambient q} {Df : ℕ → Domain n → Gradient n q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hf : ∀ k, MemW12Loc Ω (f k) (Df k))
    (hu : LocallyMemL2 Ω u)
    (hDu : ∀ i : Fin n, LocallyMemL2 Ω (fun x => Du x i))
    (hconv : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict K)) atTop (𝓝 0))
    (hDconv : ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
      ∀ (i : Fin n) (v : Lp (Ambient q) 2 (volume.restrict K)),
        Tendsto (fun k => ∫ x in K, inner ℝ (Df k x i) (v x))
          atTop (𝓝 (∫ x in K, inner ℝ (Du x i) (v x)))) :
    MemW12Loc Ω u Du := by
  refine ⟨⟨locallyIntegrableOn_of_localL2 hu,
    (fun i => locallyIntegrableOn_of_localL2 (hDu i)), ?_⟩, hu, hDu⟩
  intro i φ hφ hcompact hsupport
  let K := tsupport φ
  have hK : IsCompact K := hcompact
  have hKΩ : K ⊆ Ω.val := hsupport
  have hδK : tsupport (coordinateDerivative φ hφ i) ⊆ K :=
    tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
  have hδΩ := hδK.trans hKΩ
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  rw [setIntegral_smul_eq_integral u hδΩ,
    setIntegral_smul_eq_integral (fun x => Du x i) hsupport]
  apply ext_inner_left ℝ
  intro c
  have hφtop : MemLp φ ∞ (volume.restrict K) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcompact _
  have hδtop : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict K) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcompact.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have hl := tendsto_integral_inner_of_L2_convergence
    (fun k => (hf k).2.1 K hK hKΩ) (hu K hK hKΩ)
    (scalar_test_memLp hδtop c) (hconv K hK hKΩ)
  have heq (g : Domain n → Ambient q) (hg : MemLp g 2 (volume.restrict K)) :
      (∫ x in K, inner ℝ (g x) (coordinateDerivative φ hφ i x • c)) =
        inner ℝ c (∫ x, coordinateDerivative φ hφ i x • g x) := by
    have hi := integral_inner (𝕜 := ℝ)
      ((hg.integrable (by norm_num)).smul_of_top_right hδtop) c
    simp only [Pi.smul_apply'] at hi
    rw [setIntegral_smul_eq_integral g hδK] at hi
    rw [← hi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm (g x) c]
  have hl' : Tendsto (fun k => inner ℝ c
      (∫ x, coordinateDerivative φ hφ i x • f k x)) atTop
      (𝓝 (inner ℝ c (∫ x, coordinateDerivative φ hφ i x • u x))) := by
    simpa only [heq _ ((hf _).2.1 K hK hKΩ), heq u (hu K hK hKΩ)] using hl
  have hr := hDconv K hK hKΩ i ((scalar_test_memLp hφtop c).toLp (fun x => φ x • c))
  have hr' : Tendsto (fun k => inner ℝ c (-(∫ x, φ x • Df k x i)))
      atTop (𝓝 (inner ℝ c (-(∫ x, φ x • Du x i)))) := by
    have h := hr.neg
    simpa only [integral_pairing_scalar_test hφtop ((hf _).2.2 i K hK hKΩ) c,
      integral_pairing_scalar_test hφtop (hDu i K hK hKΩ) c,
      setIntegral_smul_eq_integral (fun x => Df _ x i) (Subset.refl K),
      setIntegral_smul_eq_integral (fun x => Du x i) (Subset.refl K), inner_neg_right] using h
  apply tendsto_nhds_unique hl'
  apply hr'.congr
  intro k
  have hidentity := (hf k).1.2.2 i φ hφ hcompact hsupport
  rw [setIntegral_smul_eq_integral (f k) hδΩ,
    setIntegral_smul_eq_integral (fun x => Df k x i) hsupport] at hidentity
  exact congrArg (inner ℝ c) hidentity.symm

end StratificationTheory.Compactness
