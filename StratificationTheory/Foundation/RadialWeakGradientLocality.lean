module

public import StratificationTheory.Foundation.RadialL2Transfer
public import HarmonicMaps.Analysis.AffineBallSobolev
public import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Weak gradients of homogeneous radial data on the punctured domain

Actual angular L2 data and their ray formulas give local Euclidean L2 data.
Finite Sobolev membership on the fixed collar transfers by positive
similarities to neighborhoods of all nonzero points. A finite smooth
partition of unity combines the local weak identities.
-/

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff Manifold

namespace StratificationTheory

private theorem radial_pairing_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : OpenDomain n} {f : Domain n → E} {φ : Domain n → ℝ}
    (hf : LocallyIntegrableOn f Ω.val volume) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω.val) :
    Integrable (fun x => φ x • f x) volume := by
  have hfK : IntegrableOn f (tsupport φ) volume := hf.integrableOn_compact_subset hs hc
  have hφK := hφ.memLp_top_of_hasCompactSupport hc (volume.restrict (tsupport φ))
  have hpair := hfK.smul_of_top_right hφK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hpair
  intro x hx
  by_contra hnot
  have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  change φ x • f x ≠ 0 at hx
  exact hx (by rw [hz, zero_smul])

private theorem radial_setIntegral_eq_integral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (Domain n)} {φ : Domain n → ℝ} (f : Domain n → E)
    (hs : tsupport φ ⊆ s) :
    (∫ x in s, φ x • f x) = ∫ x, φ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  simp only [hz, zero_smul]

private theorem weakGradient_of_local_balls {n q : ℕ} {Ω : OpenDomain n}
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    (hwI : LocallyIntegrableOn w Ω.val volume)
    (hDI : ∀ i : Fin n, LocallyIntegrableOn (fun x => D x i) Ω.val volume)
    (hlocal : ∀ x ∈ Ω.val, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω.val ∧
      MemW12 (ballDomain x r) w D) : HasWeakGradient Ω w D := by
  classical
  refine ⟨hwI, hDI, ?_⟩
  intro i φ hφ hcφ hsφ
  have hballs (x : tsupport φ) : ∃ r : ℝ, 0 < r ∧ ball x.val r ⊆ Ω.val ∧
      MemW12 (ballDomain x.val r) w D := hlocal x.val (hsφ x.property)
  choose r hr hsubset hW using hballs
  obtain ⟨t, ht⟩ := hcφ.elim_finite_subcover
    (fun x : tsupport φ => ball x.val (r x)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (mem_ball_self (hr ⟨x, hx⟩)))
  let U : t → Set (Domain n) := fun j => ball j.val.val (r j.val)
  have hcover : tsupport φ ⊆ ⋃ j : t, U j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion_of_mem ⟨j, hj⟩ hxj
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Domain n) (isClosed_tsupport φ) U (fun _ => isOpen_ball) hcover
  let ψ : t → Domain n → ℝ := fun j x => φ x * ρ j x
  have hψ (j : t) : ContDiff ℝ ∞ (ψ j) := hφ.mul (ρ j).contMDiff.contDiff
  have hcψ (j : t) : HasCompactSupport (ψ j) := hcφ.mul_right
  have hsψ (j : t) : tsupport (ψ j) ⊆ U j := tsupport_mul_subset_right.trans (hρ j)
  have hsψΩ (j : t) : tsupport (ψ j) ⊆ Ω.val := (hsψ j).trans (hsubset j.val)
  have hsum : (∑ j : t, ψ j) = φ := by
    funext x
    simp only [Finset.sum_apply, ψ]
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ tsupport φ
    · have H := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at H
      rw [H, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hDsum (x : Domain n) :
      (∑ j : t, coordinateDerivative (ψ j) (hψ j) i x) = coordinateDerivative φ hφ i x := by
    have H := fderiv_sum (u := Finset.univ) (A := ψ) (x := x)
      (fun j _ => (hψ j).differentiable (by simp) x)
    rw [hsum] at H
    simp only [coordinateDerivative, H, sum_apply]
  have hidentity (j : t) :
      (∫ x, coordinateDerivative (ψ j) (hψ j) i x • w x) =
        -(∫ x, ψ j x • D x i) := by
    have H := (hW j.val).1.2.2 i (ψ j) (hψ j) (hcψ j) (hsψ j)
    change (∫ x in U j, coordinateDerivative (ψ j) (hψ j) i x • w x) =
      -(∫ x in U j, ψ j x • D x i) at H
    rw [radial_setIntegral_eq_integral (φ := coordinateDerivative (ψ j) (hψ j) i) w
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hsψ j)),
      radial_setIntegral_eq_integral (fun x => D x i) (hsψ j)] at H
    exact H
  have hleft (j : t) : Integrable
      (fun x => coordinateDerivative (ψ j) (hψ j) i x • w x) volume :=
    radial_pairing_integrable hwI
      ((hψ j).continuous_fderiv (by simp) |>.clm_apply continuous_const)
      ((hcψ j).fderiv_apply ℝ (EuclideanSpace.single i 1))
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hsψΩ j))
  have hright (j : t) : Integrable (fun x => ψ j x • D x i) volume :=
    radial_pairing_integrable (hDI i) (hψ j).continuous (hcψ j) (hsψΩ j)
  change (∫ x in Ω.val, coordinateDerivative φ hφ i x • w x) =
    -(∫ x in Ω.val, φ x • D x i)
  rw [radial_setIntegral_eq_integral (φ := coordinateDerivative φ hφ i) w
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ),
    radial_setIntegral_eq_integral (fun x => D x i) hsφ]
  calc
    (∫ x, coordinateDerivative φ hφ i x • w x) =
        ∫ x, ∑ j : t, coordinateDerivative (ψ j) (hψ j) i x • w x := by
      congr 1
      funext x
      rw [← Finset.sum_smul, hDsum x]
    _ = ∑ j : t, ∫ x, coordinateDerivative (ψ j) (hψ j) i x • w x :=
      integral_finsetSum _ (fun j _ => hleft j)
    _ = ∑ j : t, -(∫ x, ψ j x • D x i) := Finset.sum_congr rfl (fun j _ => hidentity j)
    _ = -(∫ x, ∑ j : t, ψ j x • D x i) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun j _ => hright j)]
    _ = -(∫ x, φ x • D x i) := by
      congr 1
      congr 1
      funext x
      rw [← Finset.sum_smul]
      have H := congrFun hsum x
      simpa only [Finset.sum_apply] using congrArg (fun c : ℝ => c • D x i) H

private theorem radial_smul_formulas {n q : ℕ}
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    {v : sphere (0 : Domain n) 1 → Ambient q}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hw : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      w (ρ.val • θ.val) = v θ)
    (hD : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i)
    {s : ℝ} (hs : 0 < s) {x : Domain n} (hx : x ≠ 0) :
    w (s • x) = w x ∧ ∀ i : Fin n, s • D (s • x) i = D x i := by
  let θ : sphere (0 : Domain n) 1 :=
    ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxRay : ‖x‖ • θ.val = x := NormedSpace.norm_smul_normalize x
  have hsRay : (s * ‖x‖) • θ.val = s • x := by rw [mul_smul, hxRay]
  constructor
  · rw [← hsRay, hw ⟨s * ‖x‖, mul_pos hs hp⟩ θ,
      ← hxRay, hw ⟨‖x‖, hp⟩ θ]
  · intro i
    have hDs := hD ⟨s * ‖x‖, mul_pos hs hp⟩ θ i
    have hDx := hD ⟨‖x‖, hp⟩ θ i
    change D ((s * ‖x‖) • θ.val) i = (s * ‖x‖)⁻¹ • A θ i at hDs
    change D (‖x‖ • θ.val) i = ‖x‖⁻¹ • A θ i at hDx
    rw [hsRay] at hDs
    rw [hxRay] at hDx
    rw [hDs, hDx, smul_smul]
    congr 1
    field_simp

private theorem radial_memW12_neighborhood {n q : ℕ}
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    {v : sphere (0 : Domain n) 1 → Ambient q}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hw : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      w (ρ.val • θ.val) = v θ)
    (hD : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i)
    (hcollar : MemW12 ⟨{x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩ w D)
    {x : Domain n} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ ({0}ᶜ : Set (Domain n)) ∧
      MemW12 (ballDomain x r) w D := by
  let y := NormedSpace.normalize x
  have hy : ‖y‖ = 1 := NormedSpace.norm_normalize hx
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let C : OpenDomain n := ⟨{z : Domain n | (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2},
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)⟩
  have hyC : y ∈ C.val := by change (1 / 2 : ℝ) < ‖y‖ ∧ ‖y‖ < 2; rw [hy]; norm_num
  obtain ⟨ε, hε, hεC⟩ := isOpen_iff.mp C.property y hyC
  have hW : MemW12 (ballDomain y ε) w D := by
    refine ⟨hcollar.1.mono hεC, hcollar.2.1.mono_measure
      (Measure.restrict_mono_set volume hεC), ?_⟩
    intro i
    exact (hcollar.2.2 i).mono_measure (Measure.restrict_mono_set volume hεC)
  have ht : 0 < ‖x‖⁻¹ := inv_pos.mpr hp
  have hsim (z : Domain n) : y + ‖x‖⁻¹ • (z - x) = ‖x‖⁻¹ • z := by
    change ‖x‖⁻¹ • x + ‖x‖⁻¹ • (z - x) = ‖x‖⁻¹ • z
    rw [smul_sub]
    abel
  have hback := hW.affineBall_pullback x ht
  simp_rw [hsim] at hback
  have hsub : ball x (ε / ‖x‖⁻¹) ⊆ ({0}ᶜ : Set (Domain n)) := by
    intro z hz
    have hzin : ‖x‖⁻¹ • z ∈ C.val := by
      apply hεC
      have H := (affineBall_mem_ball_iff y x ht ε z).mpr hz
      simpa only [hsim] using H
    have hzn : z ≠ 0 := by
      intro hzero
      change (1 / 2 : ℝ) < ‖‖x‖⁻¹ • z‖ ∧ ‖‖x‖⁻¹ • z‖ < 2 at hzin
      rw [hzero, smul_zero, norm_zero] at hzin
      norm_num at hzin
    simpa only [mem_compl_iff, mem_singleton_iff] using hzn
  refine ⟨ε / ‖x‖⁻¹, div_pos hε ht, hsub, ?_⟩
  apply hback.congr_ae
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (radial_smul_formulas hw hD ht (by simpa using hsub hz)).1
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    funext i
    exact (radial_smul_formulas hw hD ht (by simpa using hsub hz)).2 i


private theorem compact_subset_radial_collar {n : ℕ} {K : Set (Domain n)}
    (hK : IsCompact K) (hne : K.Nonempty) (hs : K ⊆ ({0}ᶜ : Set (Domain n))) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧ K ⊆ {x : Domain n | ε < ‖x‖ ∧ ‖x‖ < R} := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have ha0 : a ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hs ha
  have hap : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  refine ⟨‖a‖ / 2, ‖b‖ + 1, by positivity, by positivity, ?_⟩
  intro x hx
  exact ⟨lt_of_lt_of_le (by linarith only [hap]) (hmin hx),
    lt_of_le_of_lt (hmax hx) (by linarith only [])⟩

private theorem radial_locallyMemL2_punctured {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E]
    {v : sphere (0 : Domain n) 1 → E}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    {w : Domain n → E}
    (hRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      w (ρ.val • θ.val) = v θ) :
    LocallyMemL2 ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w := by
  intro K hK hs
  by_cases hne : K.Nonempty
  · obtain ⟨ε, R, hε, hR, hsub⟩ := compact_subset_radial_collar hK hne hs
    exact (memLp_two_radial_collar_and_norm hn hv hRay ε hR).1.mono_measure
      (Measure.restrict_mono_set volume hsub)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Measure.restrict_empty]
    exact memLp_measure_zero

private theorem weighted_radial_locallyMemL2_punctured {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : sphere (0 : Domain n) 1 → E}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    {W : Domain n → E}
    (hRay : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      W (ρ.val • θ.val) = ρ.val⁻¹ • v θ) :
    LocallyMemL2 ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ W := by
  intro K hK hs
  by_cases hne : K.Nonempty
  · obtain ⟨ε, R, hε, hR, hsub⟩ := compact_subset_radial_collar hK hne hs
    have h := memLp_two_weighted_radial_collar_and_norm hn hv 1
      (fun ρ θ => by simpa only [one_div] using hRay ρ θ) hε hR
    exact h.1.mono_measure (Measure.restrict_mono_set volume hsub)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Measure.restrict_empty]
    exact memLp_measure_zero

/-- Actual angular L2 radial data with the reciprocal-radius column formula
are locally Sobolev on the whole punctured Euclidean domain whenever their
actual weak-gradient graph is Sobolev on the fixed open collar. -/
theorem memW12Loc_punctured_of_radial_collar {n q : ℕ} (hn : 0 < n)
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    {v : sphere (0 : Domain n) 1 → Ambient q}
    {A : sphere (0 : Domain n) 1 → Gradient n q}
    (hv : MemLp v 2 (volume : Measure (Domain n)).toSphere)
    (hA : ∀ i : Fin n, MemLp (fun θ => A θ i) 2
      (volume : Measure (Domain n)).toSphere)
    (hw : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      w (ρ.val • θ.val) = v θ)
    (hD : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
      D (ρ.val • θ.val) i = ρ.val⁻¹ • A θ i)
    (hcollar : MemW12 ⟨{x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩ w D) :
    MemW12Loc ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩ w D := by
  let Ω : OpenDomain n := ⟨({0}ᶜ : Set (Domain n)), isOpen_compl_singleton⟩
  have hwL : LocallyMemL2 Ω w := radial_locallyMemL2_punctured hn hv hw
  have hDL (i : Fin n) : LocallyMemL2 Ω (fun x => D x i) :=
    weighted_radial_locallyMemL2_punctured hn (hA i) (fun ρ θ => hD ρ θ i)
  have hwI : LocallyIntegrableOn w Ω.val volume := by
    apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
    intro K hs hK
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (hwL K hK hs).integrable (by norm_num)
  have hDI (i : Fin n) : LocallyIntegrableOn (fun x => D x i) Ω.val volume := by
    apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
    intro K hs hK
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (hDL i K hK hs).integrable (by norm_num)
  refine ⟨weakGradient_of_local_balls hwI hDI ?_, hwL, hDL⟩
  intro x hx
  exact radial_memW12_neighborhood hw hD hcollar (by simpa using hx)

end StratificationTheory
