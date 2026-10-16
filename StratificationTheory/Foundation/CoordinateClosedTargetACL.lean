module

public import StratificationTheory.Foundation.ClosedTargetACLInheritance
public import StratificationTheory.Foundation.CoordinateGridCompatibility

/-!
# Closed targets on actual coordinate Sobolev representatives

The original ball-a.e. target constraint pulls back under the actual
coordinate product measure. Fubini and the absolutely continuous line
representatives then give pointwise closed-target membership on whole lines.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Ball Sobolev data with a closed target produce the same canonical
coordinate representatives, their original raw slice classes, whole-line
closed-target membership and the original weak derivative increments. -/
theorem coordinatePermACLRepresentative_closed_target_of_memW12_ball {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u : Domain (n + 1) → Ambient q} {Du : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du)
    {N : Set (Ambient q)} (hN : IsClosed N)
    (huN : ∀ᵐ y ∂volume.restrict (ball z R), u y ∈ N)
    (p : Equiv.Perm (Fin (n + 1)))
    {S : Set (Domain n)} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b)
    (hrect : ∀ x ∈ S, ∀ t ∈ Ioo a b,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p)
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := {y : Domain (n + 1) | (e (Q.symm y)).1 ∈ S ∧ (e (Q.symm y)).2 0 ∈ Ioo a b}
    let W := coordinatePermACLRepresentative p a b u Du
    AEStronglyMeasurable W (volume.restrict Ω) ∧ W =ᵐ[volume.restrict Ω] u ∧
    ∀ᵐ x ∂volume.restrict S,
      AbsolutelyContinuousOnInterval
        (fun t => W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) a b ∧
      (fun t => W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) =ᵐ[
        volume.restrict (Ioo a b)]
        (fun t => u (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      (∀ t ∈ Icc a b, W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) ∈ N) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) -
          W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) s))) =
          ∫ r in s..t, Du (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)))
            (p (Fin.natAdd n (0 : Fin 1))) := by
  intro Q e Ω W
  have hrep := coordinatePermACLRepresentative_of_memW12_ball hR hu p hS hab hrect
  have hΩ : MeasurableSet Ω :=
    (hS.preimage (continuous_fst.comp (e.continuous.comp Q.symm.continuous)).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp (e.continuous.comp Q.symm.continuous))).measurable)
  have hΩsub : Ω ⊆ ball z R := by
    intro y hy
    have h := hrect (e (Q.symm y)).1 hy.1 ((e (Q.symm y)).2 0) hy.2
    rw [cylinder_coordinates_inverse_left n (Q.symm y), Q.apply_symm_apply] at h
    exact h
  have hNΩ : ∀ᵐ y ∂volume.restrict Ω, u y ∈ N :=
    huN.filter_mono (ae_mono (Measure.restrict_mono_set volume hΩsub))
  let H : Domain n × ℝ → Domain (n + 1) := fun p =>
    Q (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  have hHraw := Q.measurePreserving.comp (measurePreserving_cylinder_coordinates_inverse n)
  have hH := hHraw.restrict_preimage hΩ
  have hpre : H ⁻¹' Ω = S ×ˢ Ioo a b := by
    ext p
    simp only [H, Ω, mem_preimage, mem_setOf_eq, Q.symm_apply_apply,
      e.apply_symm_apply, PiLp.single_apply, ↓reduceIte, mem_prod]
  change MeasurePreserving H
    ((volume.prod volume).restrict (H ⁻¹' Ω)) (volume.restrict Ω) at hH
  rw [hpre, ← Measure.prod_restrict] at hH
  have hEq : (fun p => W (H p)) =ᵐ[(volume.restrict S).prod (volume.restrict (Ioo a b))]
      (fun p => u (H p)) := hH.quasiMeasurePreserving.ae hrep.2.1
  have hTarget : ∀ᵐ p ∂(volume.restrict S).prod (volume.restrict (Ioo a b)),
      u (H p) ∈ N := hH.quasiMeasurePreserving.ae hNΩ
  have hClosed := ae_fiber_interval_mem_closed_of_ae hab hEq
    (hrep.2.2.mono fun _ hx => hx.1) hN hTarget
  have hRecovery := Measure.ae_ae_of_ae_prod hEq
  refine ⟨hrep.1, hrep.2.1, ?_⟩
  filter_upwards [hrep.2.2, hRecovery, hClosed] with x hx hxEq hxN
  exact ⟨hx.1, hxEq, hxN, hx.2⟩

end StratificationTheory
