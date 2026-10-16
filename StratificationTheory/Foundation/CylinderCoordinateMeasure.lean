module

public import StratificationTheory.Foundation.AngularL2Membership
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Actual Euclidean volume in cylinder coordinates

The canonical linear coordinate split preserves actual Euclidean volume as
the product of spatial and temporal volumes. The product uses its ordinary
maximum norm; volume preservation follows through the Euclidean product
model and does not assert an isometry to that maximum norm.
-/

public section

open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal

namespace StratificationTheory

/-- The canonical finite-coordinate split has volume Jacobian exactly one. -/
theorem measurePreserving_finAddEquivProd (n m : ℕ) :
    MeasurePreserving (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m))
      (volume : Measure (Domain (n + m)))
      ((volume : Measure (Domain n)).prod (volume : Measure (Domain m))) := by
  have hfirst := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv (m := n) (n := m)).symm).measurePreserving
  have hsecond := (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
    (fun _ : Fin n ⊕ Fin m => ℝ)).measurePreserving
  exact (WithLp.volume_preserving_ofLp (Domain n) (Domain m)).comp
    (hsecond.comp hfirst)

/-- The inverse canonical split preserves the same actual product volume. -/
theorem measurePreserving_finAddEquivProd_symm (n m : ℕ) :
    MeasurePreserving (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
      ((volume : Measure (Domain n)).prod (volume : Measure (Domain m)))
      (volume : Measure (Domain (n + m))) := by
  exact (measurePreserving_finAddEquivProd n m).symm
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).toHomeomorph.toMeasurableEquiv

/-- Evaluation at the sole coordinate is an actual isometry from the
one-dimensional Euclidean model to the real line. -/
theorem isometry_domainOne_eval : Isometry (fun x : Domain 1 => x 0) := by
  let e := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have hnorm (x : Domain 1) : ‖e x‖ = ‖x‖ := by
    have hx : EuclideanSpace.single (0 : Fin 1) (x 0) = x := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp
    change ‖x 0‖ = ‖x‖
    calc
      ‖x 0‖ = ‖EuclideanSpace.single (0 : Fin 1) (x 0)‖ :=
        (PiLp.norm_single 2 (fun _ : Fin 1 => ℝ) 0 (x 0)).symm
      _ = ‖x‖ := congrArg norm hx
  let l : Domain 1 ≃ₗᵢ[ℝ] ℝ := { e.toLinearEquiv with norm_map' := hnorm }
  exact l.isometry

/-- Evaluation at the sole coordinate preserves actual Euclidean volume. -/
theorem measurePreserving_domainOne_eval :
    MeasurePreserving (fun x : Domain 1 => x 0)
      (volume : Measure (Domain 1)) (volume : Measure ℝ) := by
  exact (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).comp
    (PiLp.volume_preserving_ofLp (Fin 1))

/-- The inverse temporal coordinate map preserves actual real-line volume. -/
theorem measurePreserving_domainOne_single :
    MeasurePreserving (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t)
      (volume : Measure ℝ) (volume : Measure (Domain 1)) := by
  have h := measurePreserving_domainOne_eval.symm
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph.toMeasurableEquiv
  have heq : (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) =
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph.toMeasurableEquiv.symm := by
    funext t
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [PiLp.equivOfUnique]
  rw [← heq] at h
  exact h

/-- The spatial coordinates and the last real coordinate preserve actual
Euclidean volume as the product spatial-time volume. -/
theorem measurePreserving_cylinder_coordinates (n : ℕ) :
    MeasurePreserving
      (fun y : Domain (n + 1) =>
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1,
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0))
      (volume : Measure (Domain (n + 1)))
      ((volume : Measure (Domain n)).prod (volume : Measure ℝ)) := by
  exact ((MeasurePreserving.id (volume : Measure (Domain n))).prod
    measurePreserving_domainOne_eval).comp (measurePreserving_finAddEquivProd n 1)

/-- The actual inverse cylinder-coordinate map preserves the same product volume. -/
theorem measurePreserving_cylinder_coordinates_inverse (n : ℕ) :
    MeasurePreserving
      (fun p : Domain n × ℝ =>
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
      ((volume : Measure (Domain n)).prod (volume : Measure ℝ))
      (volume : Measure (Domain (n + 1))) := by
  exact (measurePreserving_finAddEquivProd_symm n 1).comp
    ((MeasurePreserving.id (volume : Measure (Domain n))).prod measurePreserving_domainOne_single)

/-- Restricting to the actual spatial puncture gives the actual product of
the spatial subtype volume and the unchanged real-time volume. -/
theorem measurePreserving_punctured_cylinder_coordinates (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let V := {y : Domain (n + 1) | (e y).1 ≠ 0}
    MeasurePreserving
      (fun y : V =>
        ((⟨(e y.val).1, by change (e y.val).1 ≠ 0; exact y.property⟩ :
          ({(0 : Domain n)}ᶜ : Set (Domain n))), (e y.val).2 0))
      ((volume : Measure (Domain (n + 1))).comap (Subtype.val : V → Domain (n + 1)))
      (((volume : Measure (Domain n)).comap
        (Subtype.val : ({(0 : Domain n)}ᶜ : Set (Domain n)) → Domain n)).prod
          (volume : Measure ℝ)) := by
  dsimp only
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let X := ({(0 : Domain n)}ᶜ : Set (Domain n))
  let V := {y : Domain (n + 1) | (e y).1 ≠ 0}
  let c : Domain (n + 1) → Domain n × ℝ := fun y => ((e y).1, (e y).2 0)
  let S : Set (Domain n × ℝ) := X ×ˢ univ
  let f : V → X × ℝ := fun y =>
    (⟨(e y.val).1, by change (e y.val).1 ≠ 0; exact y.property⟩,
      (e y.val).2 0)
  let g : X × ℝ → Domain n × ℝ := fun p => (p.1.val, p.2)
  have hX : MeasurableSet X := (measurableSet_singleton (0 : Domain n)).compl
  letI : SigmaFinite ((volume : Measure (Domain n)).comap (Subtype.val : X → Domain n)) :=
    (measurePreserving_subtype_coe hX (μa := (volume : Measure (Domain n)))).sigmaFinite
  have hV : MeasurableSet V :=
    (e.continuous.fst.measurable (measurableSet_singleton (0 : Domain n))).compl
  have hpre : c ⁻¹' S = V := by
    ext y
    simp only [c, S, X, V, mem_preimage, mem_prod, mem_compl_iff,
      mem_singleton_iff, mem_univ, and_true, mem_setOf_eq]
  have hc := (measurePreserving_cylinder_coordinates n).restrict_preimage
    (hX.prod MeasurableSet.univ)
  rw [hpre] at hc
  have hsub := measurePreserving_subtype_coe hV (μa := (volume : Measure (Domain (n + 1))))
  have hcomp : MeasurePreserving (g ∘ f)
      ((volume : Measure (Domain (n + 1))).comap (Subtype.val : V → Domain (n + 1)))
      (((volume : Measure (Domain n)).prod (volume : Measure ℝ)).restrict S) :=
    hc.comp hsub
  have hg : MeasurableEmbedding g :=
    (MeasurableEmbedding.subtype_coe hX).prodMap MeasurableEmbedding.id
  have hgMP : MeasurePreserving g
      (((volume : Measure (Domain n)).comap (Subtype.val : X → Domain n)).prod
        (volume : Measure ℝ))
      (((volume : Measure (Domain n)).prod (volume : Measure ℝ)).restrict S) := by
    have h := (measurePreserving_subtype_coe hX (μa := (volume : Measure (Domain n)))).prod
      (MeasurePreserving.id (volume : Measure ℝ))
    have hprod : ((volume : Measure (Domain n)).restrict X).prod (volume : Measure ℝ) =
        (((volume : Measure (Domain n)).prod (volume : Measure ℝ)).restrict S) := by
      simpa only [Measure.restrict_univ] using
        (Measure.prod_restrict (μ := (volume : Measure (Domain n)))
          (ν := (volume : Measure ℝ)) X univ)
    exact ⟨h.measurable, h.map_eq.trans hprod⟩
  have hf : Measurable f := by
    have he : Continuous (fun y : V => e y.val) := e.continuous.comp continuous_subtype_val
    exact (he.fst.measurable.subtype_mk).prodMk
      ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp he.snd).measurable
  refine ⟨hf, ?_⟩
  apply hg.map_injective
  rw [Measure.map_map hg.measurable hf, hcomp.map_eq, hgMP.map_eq]

/-- Actual spatial polar coordinates and unchanged time send the spatially
punctured Euclidean cylinder volume to the native sphere-radius-time product. -/
theorem measurePreserving_native_polar_cylinder_coordinates {n : ℕ} (hn : 0 < n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let V := {y : Domain (n + 1) | (e y).1 ≠ 0}
    MeasurePreserving
      (fun y : V =>
        let x : ({(0 : Domain n)}ᶜ : Set (Domain n)) :=
          ⟨(e y.val).1, by change (e y.val).1 ≠ 0; exact y.property⟩
        ((homeomorphUnitSphereProd (Domain n) x).1,
          ((homeomorphUnitSphereProd (Domain n) x).2, (e y.val).2 0)))
      ((volume : Measure (Domain (n + 1))).comap (Subtype.val : V → Domain (n + 1)))
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        ((Measure.volumeIoiPow (n - 1)).prod (volume : Measure ℝ))) := by
  dsimp only
  have hp := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hp
  letI : SigmaFinite ((volume : Measure (Domain n)).comap
      (Subtype.val : ({(0 : Domain n)}ᶜ : Set (Domain n)) → Domain n)) := hp.sigmaFinite
  have ht := (hp.prod (MeasurePreserving.id (volume : Measure ℝ))).comp
    (measurePreserving_punctured_cylinder_coordinates n)
  have ha := (measurePreserving_prodAssoc (volume : Measure (Domain n)).toSphere
    (Measure.volumeIoiPow (n - 1)) (volume : Measure ℝ)).comp ht
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere hn] at ha
  exact ha

/-- The displayed inverse cylinder map recovers every actual ambient point. -/
theorem cylinder_coordinates_inverse_left (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∀ y : Domain (n + 1),
      e.symm ((e y).1, EuclideanSpace.single (0 : Fin 1) ((e y).2 0)) = y := by
  intro e y
  have ht : EuclideanSpace.single (0 : Fin 1) ((e y).2 0) = (e y).2 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [ht, Prod.mk.eta, e.symm_apply_apply]

/-- Splitting the displayed inverse cylinder map recovers the actual
spatial point and real-time coordinate. -/
theorem cylinder_coordinates_inverse_right (n : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    ∀ p : Domain n × ℝ,
      ((e (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))).1,
        (e (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))).2 0) = p := by
  intro e p
  rw [e.apply_symm_apply]
  simp

/-- The actual volume of the inverse image of a measurable spatial-time
rectangle is the product of its actual spatial and temporal measures. -/
theorem volume_cylinder_coordinates_rectangle (n : ℕ)
    {S : Set (Domain n)} {T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (volume : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈ S ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ T} =
      (volume : Measure (Domain n)) S * (volume : Measure ℝ) T := by
  have h := (measurePreserving_cylinder_coordinates n).measure_preimage
    (hS.prod hT).nullMeasurableSet
  exact h.trans (Measure.prod_prod S T)

/-- A positive-radius spatial ball and a nonempty bounded open time interval
form an actual positive-volume cylinder in every spatial dimension. -/
theorem volume_cylinder_coordinates_ball_interval_pos (n : ℕ)
    {R a b : ℝ} (hR : 0 < R) (hab : a < b) :
    0 < (volume : Measure (Domain (n + 1)))
      {y | (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ∈
          ball (0 : Domain n) R ∧
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b} := by
  rw [volume_cylinder_coordinates_rectangle n measurableSet_ball measurableSet_Ioo,
    Real.volume_Ioo]
  exact ENNReal.mul_pos
    ((isOpen_ball.measure_pos (volume : Measure (Domain n))
      ⟨0, mem_ball_self hR⟩).ne')
    ((ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne')

end StratificationTheory
