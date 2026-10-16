module

public import HarmonicMaps.Analysis.AffineBallMeasure
public import HarmonicMaps.EnergyLemmas
public import HarmonicMaps.Analysis.AffineEnergyScaling

/-!
# Positive affine transport on finite open domains

The original finite Sobolev graph is transported to the complete inverse
image domain. The same affine map and derivative multiplier have the exact
native volume and dimensionally scaled energy formulas.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff ENNReal
namespace StratificationTheory

private theorem affine_test_setIntegral {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : Set (Domain n)} {φ : Domain n → ℝ}
    (hs : tsupport φ ⊆ S) (f : Domain n → E) :
    (∫ x in S, φ x • f x) = ∫ x, φ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_smul]

/-- Positive similarities pull back the original full weak pair to the whole
inverse-image open domain with the actual derivative multiplier. -/
theorem memW12_affine_preimage {n q : ℕ} {Ω : OpenDomain n}
    (hfinite : (volume : Measure (Domain n)) Ω.val ≠ ⊤)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (a b : Domain n) {r : ℝ} (hr : 0 < r) :
    let G : Domain n → Domain n := fun x => a + r • (x - b)
    let Ω' : OpenDomain n := ⟨G ⁻¹' Ω.val, Ω.property.preimage (affineBall_contDiff a b r).continuous⟩
    MemW12 Ω' (u ∘ G) (fun x i => r • Du (G x) i) := by
  intro G Ω'
  have hGEmb : MeasurableEmbedding G := affineBall_measurableEmbedding a b hr.ne'
  have hmap : Measure.map G (volume.restrict Ω'.val) =
      ENNReal.ofReal ((r ^ n)⁻¹) • volume.restrict Ω.val := by
    change Measure.map G (volume.restrict (G ⁻¹' Ω.val)) = _
    rw [← hGEmb.restrict_map, affineBall_map_volume a b hr, Measure.restrict_smul]
  have hvol : (volume : Measure (Domain n)) Ω'.val =
      ENNReal.ofReal ((r ^ n)⁻¹) * (volume : Measure (Domain n)) Ω.val := by
    change (volume : Measure (Domain n)) (G ⁻¹' Ω.val) = _
    rw [← Measure.map_apply hGEmb.measurable Ω.property.measurableSet,
      affineBall_map_volume a b hr, Measure.smul_apply, smul_eq_mul]
  letI : IsFiniteMeasure (volume.restrict Ω'.val) := isFiniteMeasure_restrict.mpr (by
    rw [hvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
  have hcomp (f : Domain n → Ambient q) (hf : MemLp f 2 (volume.restrict Ω.val)) :
      MemLp (fun x => f (G x)) 2 (volume.restrict Ω'.val) := by
    have h := hf.smul_measure (c := ENNReal.ofReal ((r ^ n)⁻¹)) ENNReal.ofReal_ne_top
    rw [← hmap] at h
    exact h.comp_of_map hGEmb.measurable.aemeasurable
  have huL : MemLp (u ∘ G) 2 (volume.restrict Ω'.val) := hcomp u hu.2.1
  have hDL (i : Fin n) : MemLp (fun x => r • Du (G x) i) 2 (volume.restrict Ω'.val) :=
    (hcomp (fun x => Du x i) (hu.2.2 i)).const_smul r
  have huI : IntegrableOn (u ∘ G) Ω'.val := huL.integrable (by norm_num)
  have hDI (i : Fin n) : IntegrableOn (fun x => r • Du (G x) i) Ω'.val :=
    (hDL i).integrable (by norm_num)
  refine ⟨⟨huI.locallyIntegrableOn, fun i => (hDI i).locallyIntegrableOn, ?_⟩, huL, hDL⟩
  intro i φ hφ hcφ hsφ
  let ψ : Domain n → ℝ := fun y => φ (b + r⁻¹ • (y - a))
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (affineBall_contDiff b a r⁻¹)
  have hcψ : HasCompactSupport ψ := affineBallTest_hasCompactSupport hcφ b a (inv_ne_zero hr.ne')
  have hsψ : tsupport ψ ⊆ Ω.val := by
    intro y hy
    have hp := tsupport_comp_subset_preimage φ (affineBall_contDiff b a r⁻¹).continuous hy
    have h := hsφ hp
    change a + r • ((b + r⁻¹ • (y - a)) - b) ∈ Ω.val at h
    simpa only [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
      add_sub_cancel] using h
  have hInv (x : Domain n) : b + r⁻¹ • (G x - a) = x := affineBall_inverse a b hr.ne' x
  have hψG (x : Domain n) : ψ (G x) = φ x := by dsimp only [ψ]; rw [hInv]
  have hder (x : Domain n) : r * coordinateDerivative ψ hψ i (G x) = coordinateDerivative φ hφ i x := by
    have h := affineBallTest_coordinateDerivative hφ b a r⁻¹ i (G x)
    change coordinateDerivative ψ hψ i (G x) = r⁻¹ * coordinateDerivative φ hφ i
      (b + r⁻¹ • (G x - a)) at h
    rw [hInv] at h
    rw [h]
    field_simp
  have hIntegral (f : Domain n → Ambient q) : (∫ x, f (G x)) = (r ^ n)⁻¹ • ∫ x, f x := by
    calc
      _ = ∫ x, f (a + r • x) := integral_sub_right_eq_self (fun x => f (a + r • x)) b
      _ = (r ^ n)⁻¹ • ∫ x, f (a + x) := by
        simpa only [finrank_euclideanSpace_fin] using
          Measure.integral_comp_smul_of_nonneg volume (fun x => f (a + x)) r (hR := hr.le)
      _ = _ := by rw [integral_add_left_eq_self]
  have hIBP := hu.1.2.2 i ψ hψ hcψ hsψ
  rw [affine_test_setIntegral (φ := coordinateDerivative ψ hψ i)
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsψ) u,
    affine_test_setIntegral hsψ (fun y => Du y i)] at hIBP
  change (∫ x in Ω'.val, coordinateDerivative φ hφ i x • u (G x)) =
    -(∫ x in Ω'.val, φ x • (r • Du (G x) i))
  rw [affine_test_setIntegral (φ := coordinateDerivative φ hφ i)
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ) (fun x => u (G x)),
    affine_test_setIntegral hsφ (fun x => r • Du (G x) i)]
  have hleft : (∫ x, coordinateDerivative φ hφ i x • u (G x)) =
      (r ^ n)⁻¹ • (r • ∫ y, coordinateDerivative ψ hψ i y • u y) := by
    calc
      _ = ∫ x, r • (coordinateDerivative ψ hψ i (G x) • u (G x)) := by
        congr 1
        funext x
        rw [← hder, mul_smul]
      _ = (r ^ n)⁻¹ • ∫ y, r • (coordinateDerivative ψ hψ i y • u y) :=
        hIntegral (fun y => r • (coordinateDerivative ψ hψ i y • u y))
      _ = _ := by rw [integral_smul]
  have hright : (∫ x, φ x • (r • Du (G x) i)) =
      (r ^ n)⁻¹ • (r • ∫ y, ψ y • Du y i) := by
    calc
      _ = ∫ x, r • (ψ (G x) • Du (G x) i) := by
        congr 1
        funext x
        rw [hψG, smul_comm]
      _ = (r ^ n)⁻¹ • ∫ y, r • (ψ y • Du y i) := hIntegral (fun y => r • (ψ y • Du y i))
      _ = _ := by rw [integral_smul]
  rw [hleft, hright, hIBP]
  simp only [smul_neg]

/-- The same positive similarity retains the original a.e. values and has
the exact native value integral and dimensionally scaled HS energy. -/
theorem memW12_affine_preimage_energy {n q : ℕ} {Ω : OpenDomain n}
    (hfinite : (volume : Measure (Domain n)) Ω.val ≠ ⊤)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (a b : Domain n) {r : ℝ} (hr : 0 < r) :
    let G : Domain n → Domain n := fun x => a + r • (x - b)
    let Ω' : OpenDomain n := ⟨G ⁻¹' Ω.val, Ω.property.preimage (affineBall_contDiff a b r).continuous⟩
    let D : Domain n → Gradient n q := fun x i => r • Du (G x) i
    MemW12 Ω' (u ∘ G) D ∧
      (∫ x in Ω'.val, ‖u (G x)‖ ^ 2) = (r ^ n)⁻¹ * ∫ x in Ω.val, ‖u x‖ ^ 2 ∧
      (∫ x in Ω'.val, hsNormSq (D x)) =
        r ^ (2 - (n : ℤ)) * ∫ x in Ω.val, hsNormSq (Du x) ∧
      dirichletEnergy D Ω'.val = ENNReal.ofReal (r ^ (2 - (n : ℤ))) * dirichletEnergy Du Ω.val ∧
      ∀ P : Ambient q → Prop, (∀ᵐ y ∂volume.restrict Ω.val, P (u y)) →
        ∀ᵐ x ∂volume.restrict Ω'.val, P ((u ∘ G) x) := by
  intro G Ω' D
  have hW : MemW12 Ω' (u ∘ G) D := memW12_affine_preimage hfinite hu a b hr
  have hEmb : MeasurableEmbedding G := affineBall_measurableEmbedding a b hr.ne'
  have hmap : Measure.map G (volume.restrict Ω'.val) =
      ENNReal.ofReal ((r ^ n)⁻¹) • volume.restrict Ω.val := by
    change Measure.map G (volume.restrict (G ⁻¹' Ω.val)) = _
    rw [← hEmb.restrict_map, affineBall_map_volume a b hr, Measure.restrict_smul]
  have hIntegral (f : Domain n → ℝ) : (∫ x in Ω'.val, f (G x)) =
      (r ^ n)⁻¹ * ∫ x in Ω.val, f x := by
    rw [← hEmb.integral_map, hmap, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have hfactor : r ^ 2 * (r ^ n)⁻¹ = r ^ (2 - (n : ℤ)) := by
    rw [zpow_sub₀ hr.ne', zpow_ofNat, zpow_natCast]
    rfl
  have hE : (∫ x in Ω'.val, hsNormSq (D x)) =
      r ^ (2 - (n : ℤ)) * ∫ x in Ω.val, hsNormSq (Du x) := by
    dsimp only [D]
    simp_rw [hsNormSq_const_smul]
    rw [integral_const_mul, hIntegral (fun x => hsNormSq (Du x)), ← mul_assoc, hfactor]
  refine ⟨hW, hIntegral (fun x => ‖u x‖ ^ 2), hE, ?_, ?_⟩
  · rw [dirichletEnergy_eq_ofReal_integral hW.integrable_hsNormSq,
      dirichletEnergy_eq_ofReal_integral hu.integrable_hsNormSq, hE,
      ENNReal.ofReal_mul (zpow_nonneg hr.le _)]
  · intro P hP
    have hQ : Measure.QuasiMeasurePreserving G (volume.restrict Ω'.val) (volume.restrict Ω.val) :=
      ⟨hEmb.measurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
    exact hQ.ae hP

end StratificationTheory
