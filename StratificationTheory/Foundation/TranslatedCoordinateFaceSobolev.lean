module

public import StratificationTheory.Foundation.CoordinateBallFiberSobolev
public import StratificationTheory.Foundation.AffineDomainSobolevPullback

/-!
# Native weak graphs on translated coordinate faces

The original full weak graph is retained in the physical translated-face
parameterization. A face and its open tangential parameter domain may be
chosen after its origin; only actual inclusion in the original ball is used.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Almost every origin qualifies all original translated coordinate faces,
in their native tangential coordinates. All corresponding weak columns are
the original ambient columns, without a tangential translation multiplier. -/
theorem ae_memW12_all_translated_coordinate_faces_of_memW12_ball
    {N q : ℕ} {ι : Type*} [Countable ι]
    {z : Domain N} {R : ℝ} (hR : 0 < R)
    {u : Domain N → Ambient q} {Du : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z R) u Du)
    (m k : ι → ℕ) (p : ∀ i, Fin (m i + k i) ≃ Fin N) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)
    let A := fun i (y : Domain N) (t : Domain (k i)) =>
      y + Q i ((e i).symm (0, t))
    ∀ᵐ y ∂(volume : Measure (Domain N)), ∀ (i : ι) (U : OpenDomain (k i)),
      (∀ t ∈ U.val, A i y t ∈ ball z R) →
      MemW12 U (fun t => u (A i y t))
        (fun t j => Du (A i y t) (p i (Fin.natAdd (m i) j))) := by
  intro Q e A
  have hfaces := ae_memW12_all_coordinate_faces_of_memW12_ball hR hu m k p
  filter_upwards [hfaces] with y hy
  intro i U hU
  let β := (e i ((Q i).symm y)).1
  let τ := (e i ((Q i).symm y)).2
  let F : Domain (k i) → Domain N := fun t => Q i ((e i).symm (β, t))
  have hid (t : Domain (k i)) : F (τ + t) = A i y t := by
    have hys : Q i ((e i).symm (β, τ)) = y := by
      change Q i ((e i).symm ((e i) ((Q i).symm y))) = y
      rw [(e i).symm_apply_apply, (Q i).apply_symm_apply]
    have hpair : (β, τ + t) = (β, τ) + (0, t) :=
      Prod.ext (add_zero β).symm rfl
    calc
      F (τ + t) = Q i ((e i).symm ((β, τ) + (0, t))) := by
        change Q i ((e i).symm (β, τ + t)) = _
        rw [hpair]
      _ = Q i ((e i).symm (β, τ)) + Q i ((e i).symm (0, t)) := by
        rw [map_add, map_add]
      _ = A i y t := by rw [hys]
  let V : OpenDomain (k i) :=
    ⟨(fun t : Domain (k i) => t - τ) ⁻¹' U.val,
      U.property.preimage (continuous_id.sub continuous_const)⟩
  have hVcontain : ∀ t ∈ V.val, F t ∈ ball z R := by
    intro t ht
    have h := hU (t - τ) ht
    have hcancel : τ + (t - τ) = t := by abel
    rw [← hid, hcancel] at h
    exact h
  have hV := hy i V hVcontain
  have hVfinite : (volume : Measure (Domain (k i))) V.val ≠ ⊤ := by
    let L : Domain N →L[ℝ] Domain (k i) :=
      ((ContinuousLinearMap.snd ℝ (Domain (m i)) (Domain (k i))).comp
        (e i).toContinuousLinearMap).comp (Q i).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hb := L.lipschitz.isBounded_image (isBounded_ball (x := z) (r := R))
    apply (hb.subset ?_).measure_lt_top.ne
    intro t ht
    refine ⟨F t, hVcontain t ht, ?_⟩
    change (e i ((Q i).symm (Q i ((e i).symm (β, t))))).2 = t
    rw [(Q i).symm_apply_apply, (e i).apply_symm_apply]
  have htrans := memW12_affine_preimage hVfinite hV τ 0 (r := 1) zero_lt_one
  dsimp only at htrans
  simp only [one_smul, sub_zero] at htrans
  have hpre : (fun t : Domain (k i) => τ + t) ⁻¹' V.val = U.val := by
    ext t
    change τ + t - τ ∈ U.val ↔ t ∈ U.val
    simp only [add_sub_cancel_left]
  have hdomain : (⟨(fun t : Domain (k i) => τ + t) ⁻¹' V.val,
      V.property.preimage (continuous_const.add continuous_id)⟩ : OpenDomain (k i)) = U :=
    Subtype.ext hpre
  change MemW12
    ⟨(fun t : Domain (k i) => τ + t) ⁻¹' V.val,
      V.property.preimage (continuous_const.add continuous_id)⟩
    (fun t => u (F (τ + t)))
    (fun t j => Du (F (τ + t)) (p i (Fin.natAdd (m i) j))) at htrans
  rw [hdomain] at htrans
  simpa only [hid] using htrans

end StratificationTheory
