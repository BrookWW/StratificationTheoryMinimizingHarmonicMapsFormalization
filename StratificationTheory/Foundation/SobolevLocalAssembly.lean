module

public import StratificationTheory.Foundation.LinearKernelRemoval
public import HarmonicMaps.SobolevRestriction
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local assembly of the same original Sobolev pair

A smooth finite partition on each test support combines original local weak
graphs without changing the map or any column. Bounded maps can then be
assembled across a finite family of affine codimension-two exceptional flats.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff Manifold
namespace StratificationTheory

private theorem pairing_integrable_local_graph {n : ℕ} {E : Type*}
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

private theorem setIntegral_eq_integral_local_graph {n : ℕ} {E : Type*}
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
    rw [setIntegral_eq_integral_local_graph (φ := coordinateDerivative (ψ j) (hψ j) i) w
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hsψ j)),
      setIntegral_eq_integral_local_graph (fun x => D x i) (hsψ j)] at H
    exact H
  have hleft (j : t) : Integrable
      (fun x => coordinateDerivative (ψ j) (hψ j) i x • w x) volume :=
    pairing_integrable_local_graph hwI
      ((hψ j).continuous_fderiv (by simp) |>.clm_apply continuous_const)
      ((hcψ j).fderiv_apply ℝ (EuclideanSpace.single i 1))
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hsψΩ j))
  have hright (j : t) : Integrable (fun x => ψ j x • D x i) volume :=
    pairing_integrable_local_graph (hDI i) (hψ j).continuous (hcψ j) (hsψΩ j)
  change (∫ x in Ω.val, coordinateDerivative φ hφ i x • w x) =
    -(∫ x in Ω.val, φ x • D x i)
  rw [setIntegral_eq_integral_local_graph (φ := coordinateDerivative φ hφ i) w
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ),
    setIntegral_eq_integral_local_graph (fun x => D x i) hsφ]
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

private theorem locallyIntegrableOn_of_restricted_memLp {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {Ω : OpenDomain n} {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict Ω.val)) : LocallyIntegrableOn f Ω.val volume := by
  apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
  intro K hKΩ hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hf.mono_measure (Measure.restrict_mono_set volume hKΩ)).integrable (by norm_num)

/-- Original full L2 data and genuine local weak graphs of the same pair
produce the original weak graph on the entire open set. -/
theorem memW12_of_local_sobolev_pair {n q : ℕ} {Ω : OpenDomain n}
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    (hw : MemLp w 2 (volume.restrict Ω.val))
    (hD : ∀ i : Fin n, MemLp (fun x => D x i) 2 (volume.restrict Ω.val))
    (hlocal : ∀ x ∈ Ω.val, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω.val ∧
      MemW12 (ballDomain x r) w D) : MemW12 Ω w D :=
  ⟨weakGradient_of_local_balls (locallyIntegrableOn_of_restricted_memLp hw)
      (fun i => locallyIntegrableOn_of_restricted_memLp (hD i)) hlocal, hw, hD⟩

/-- Full original weak graphs on an arbitrary open cover combine with global
L2 data to give the same original Sobolev pair on the covered open domain. -/
theorem memW12_of_open_cover_sobolev_pair {n q : ℕ} {ι : Type*} {Ω : OpenDomain n}
    {w : Domain n → Ambient q} {D : Domain n → Gradient n q}
    (hw : MemLp w 2 (volume.restrict Ω.val))
    (hD : ∀ i : Fin n, MemLp (fun x => D x i) 2 (volume.restrict Ω.val))
    (U : ι → OpenDomain n) (hcover : ∀ x ∈ Ω.val, ∃ j : ι, x ∈ (U j).val)
    (hU : ∀ j, MemW12 (U j) w D) : MemW12 Ω w D := by
  apply memW12_of_local_sobolev_pair hw hD
  intro x hx
  obtain ⟨j, hxj⟩ := hcover x hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (Ω.property.inter (U j).property) x ⟨hx, hxj⟩
  have hΩsub : ball x r ⊆ Ω.val := fun y hy => (hsub hy).1
  have hUsub : ball x r ⊆ (U j).val := fun y hy => (hsub hy).2
  refine ⟨r, hr, hΩsub, ?_⟩
  exact ⟨(hU j).1.mono hUsub,
    (hU j).2.1.mono_measure (Measure.restrict_mono_set volume hUsub),
    fun i => ((hU j).2.2 i).mono_measure (Measure.restrict_mono_set volume hUsub)⟩

/-- Local actual graphs off a finite exceptional flat family, original L2
data and the original value bound produce the same full global Sobolev pair. -/
theorem memW12_of_bounded_local_sobolev_off_finite_affine_flats {n q : ℕ} {ι : Type*}
    (s : Finset ι) (Q : ι → Domain (n + 2) ≃ₗᵢ[ℝ] Domain (n + 2))
    (c : ι → Domain (n + 2)) {Ω : OpenDomain (n + 2)} (hΩ : Bornology.IsBounded Ω.val)
    {w : Domain (n + 2) → Ambient q} {D : Domain (n + 2) → Gradient (n + 2) q}
    (hw : MemLp w 2 (volume.restrict Ω.val))
    (hD : ∀ i : Fin (n + 2), MemLp (fun x => D x i) 2 (volume.restrict Ω.val))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ ≤ B) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 2)
    let P : ι → Domain (n + 2) →L[ℝ] Domain 2 := fun j =>
      (ContinuousLinearMap.snd ℝ (Domain n) (Domain 2)).comp
        (e.toContinuousLinearMap.comp (Q j).toContinuousLinearEquiv.toContinuousLinearMap)
    let Z : ι → Set (Domain (n + 2)) := fun j => (fun x => P j (x - c j)) ⁻¹' {(0 : Domain 2)}
    let V : OpenDomain (n + 2) :=
      ⟨Ω.val ∩ (⋃ j ∈ s, Z j)ᶜ,
        Ω.property.inter (isClosed_biUnion_finset (fun j _ =>
          isClosed_singleton.preimage ((P j).continuous.comp
            (continuous_id.sub continuous_const)))).isOpen_compl⟩
    (∀ x ∈ V.val, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ V.val ∧
      MemW12 (ballDomain x r) w D) → MemW12 Ω w D := by
  intro e P Z V hlocal
  have hsub : V.val ⊆ Ω.val := inter_subset_left
  have hwV : MemLp w 2 (volume.restrict V.val) :=
    hw.mono_measure (Measure.restrict_mono_set volume hsub)
  have hDV (i : Fin (n + 2)) : MemLp (fun x => D x i) 2 (volume.restrict V.val) :=
    (hD i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hWV : MemW12 V w D := memW12_of_local_sobolev_pair hwV hDV hlocal
  exact memW12_of_bounded_off_finite_affine_coordinate_flats s Q c hΩ hw hD hB hWV.1

end StratificationTheory
