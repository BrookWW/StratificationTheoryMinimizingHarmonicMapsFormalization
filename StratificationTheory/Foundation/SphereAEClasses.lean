module

public import StratificationTheory.Frozen.SphereSobolev
public import StratificationTheory.Frozen.SphereTargetValues
public import StratificationTheory.Foundation.AngularL2Membership
public import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.MeasureTheory.Measure.Prod

public section
open HarmonicMaps MeasureTheory Metric Set

namespace StratificationTheory

/-- An arbitrary angular a.e. property pulls back to the punctured Euclidean
 domain under the actual polar homeomorphism. -/
theorem ae_polar_angle_of_ae_sphere {n : ℕ}
    {P : sphere (0 : Domain n) 1 → Prop}
    (hP : ∀ᵐ θ ∂(volume : Measure (Domain n)).toSphere, P θ) :
    ∀ᵐ x : ({(0 : Domain n)}ᶜ : Set (Domain n))
      ∂Measure.comap (Subtype.val : ({(0 : Domain n)}ᶜ : Set (Domain n)) → Domain n)
        volume,
      P ((homeomorphUnitSphereProd (Domain n) x).1) := by
  have hp : ∀ᵐ p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ)
      ∂(volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1)),
      P p.1 := Measure.quasiMeasurePreserving_fst.ae hP
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hm
  exact hm.quasiMeasurePreserving.ae hp

/-- The complete radial-extension sphere Sobolev predicate depends only on
 the native surface-a.e. map class. -/
theorem memSphereW12_congr_ae {n q : ℕ} (hn : 2 ≤ n)
    {v v' : sphere (0 : Domain n) 1 → Ambient q}
    (h : MemSphereW12 hn v)
    (hvv' : v =ᵐ[Measure.euclideanHausdorffMeasure (n - 1)] v') :
    MemSphereW12 hn v' := by
  classical
  obtain ⟨hLp, U, hS, h0, w, Dw, hW, hRay⟩ := h
  have hae : v =ᵐ[(volume : Measure (Domain n)).toSphere] v' := by
    rwa [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega)] at hvv'
  let w' : Domain n → Ambient q := fun x =>
    if hx : x ≠ 0 then
      v' ((homeomorphUnitSphereProd (Domain n)
        ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1)
    else 0
  have hangle := ae_polar_angle_of_ae_sphere hae
  have hangle' : ∀ᵐ x ∂volume.restrict ({(0 : Domain n)}ᶜ),
      ∀ hx : x ≠ 0,
        v ((homeomorphUnitSphereProd (Domain n)
          ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1) =
        v' ((homeomorphUnitSphereProd (Domain n)
          ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1) := by
    apply (ae_restrict_iff_subtype (measurableSet_singleton (0 : Domain n)).compl).mpr
    filter_upwards [hangle] with x hx
    intro _
    exact hx
  have hsub : U.val ⊆ ({(0 : Domain n)}ᶜ : Set (Domain n)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hz
    exact h0 (hz ▸ hx)
  have hww' : w =ᵐ[volume.restrict U.val] w' := by
    filter_upwards [hangle'.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub)),
      ae_restrict_mem U.property.measurableSet] with x hx hU
    have hx0 : x ≠ 0 := by intro hz; exact h0 (hz ▸ hU)
    let sx : ({(0 : Domain n)}ᶜ : Set (Domain n)) := ⟨x, hsub hU⟩
    let p := homeomorphUnitSphereProd (Domain n) sx
    have hp : p.2.val • p.1.val = x := by
      have he := congrArg (fun z : ({(0 : Domain n)}ᶜ : Set (Domain n)) => z.val)
        ((homeomorphUnitSphereProd (Domain n)).symm_apply_apply sx)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using he
    have hw : w x = v p.1 := by
      have hv := hRay ⟨p.2.val, p.2.property⟩ p.1 (hp ▸ hU)
      simpa only [hp] using hv
    rw [hw]
    simpa only [w', dif_pos hx0, p, sx] using hx hx0
  refine ⟨hLp.ae_eq hvv', U, hS, h0, w', Dw,
    hW.congr_ae hww' (Filter.EventuallyEq.refl _ _), ?_⟩
  intro r θ _hmem
  have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
  have hx0 : r.val • θ.val ≠ 0 := by
    intro hz
    have hnrm := congrArg norm hz
    rw [norm_smul, Real.norm_of_nonneg r.property.le, hθ, mul_one, norm_zero] at hnrm
    exact r.property.ne' hnrm
  let p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) := (θ, ⟨r.val, r.property⟩)
  have hs : (⟨r.val • θ.val,
      by simpa only [mem_compl_iff, mem_singleton_iff] using hx0⟩ :
      ({(0 : Domain n)}ᶜ : Set (Domain n))) =
      (homeomorphUnitSphereProd (Domain n)).symm p := by
    apply Subtype.ext
    simp only [homeomorphUnitSphereProd_symm_apply_coe, p]
  simp only [w', dif_pos hx0, hs, Homeomorph.apply_symm_apply, p]

/-- The full sphere Sobolev predicate is invariant under native surface-a.e.
 equality, in both directions. -/
theorem memSphereW12_congr_ae_iff {n q : ℕ} (hn : 2 ≤ n)
    {v v' : sphere (0 : Domain n) 1 → Ambient q}
    (hvv' : v =ᵐ[Measure.euclideanHausdorffMeasure (n - 1)] v') :
    MemSphereW12 hn v ↔ MemSphereW12 hn v' :=
  ⟨fun h => memSphereW12_congr_ae hn h hvv',
    fun h => memSphereW12_congr_ae hn h hvv'.symm⟩

/-- Actual sphere target-valuedness depends only on the same native
 surface-a.e. map class. -/
theorem takesSphereValuesIn_congr_ae_iff {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q)
    {v v' : sphere (0 : Domain n) 1 → Ambient q}
    (hvv' : v =ᵐ[Measure.euclideanHausdorffMeasure (n - 1)] v') :
    TakesSphereValuesIn hn N v ↔ TakesSphereValuesIn hn N v' := by
  constructor
  · intro h
    filter_upwards [h, hvv'] with θ hθ heq
    exact heq ▸ hθ
  · intro h
    filter_upwards [h, hvv'] with θ hθ heq
    exact heq.symm ▸ hθ

end StratificationTheory
