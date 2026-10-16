module

public import StratificationTheory.Foundation.CubicalConeNativeMeasure
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bochner integration in native positive cone coordinates

Actual native integrability supplies Fubini before the fixed spatial
dilation transforms each slice. No transformed integrability is assumed.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Module
open scoped Topology ENNReal
namespace StratificationTheory

/-- The exact native Bochner integral over a positive dilated face. -/
theorem integral_inverse_smul_face {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {r : ℝ} (hr : 0 < r)
    {S : Set (Domain n)} (hS : MeasurableSet S) (f : Domain n → E) :
    (∫ x in {x | r⁻¹ • x ∈ S}, f x) = r ^ n • ∫ x in S, f (r • x) := by
  have hpre : MeasurableSet {x : Domain n | r⁻¹ • x ∈ S} :=
    hS.preimage (continuous_const_smul r⁻¹).measurable
  have hEq (x : Domain n) : ({x : Domain n | r⁻¹ • x ∈ S}.indicator f) x =
      (S.indicator (fun y => f (r • y))) (r⁻¹ • x) := by
    by_cases hx : r⁻¹ • x ∈ S
    · rw [Set.indicator_of_mem (show x ∈ {x : Domain n | r⁻¹ • x ∈ S} from hx),
        Set.indicator_of_mem hx, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Domain n | r⁻¹ • x ∈ S} from hx),
        Set.indicator_of_notMem hx]
  rw [← integral_indicator hpre]
  simp_rw [hEq]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume _ hr.le, integral_indicator hS]
  simp only [Domain, finrank_euclideanSpace, Fintype.card_fin]

/-- Fubini and actual fixed-dilation change of variables give the native
Bochner face-cone formula for every originally integrable cone field. -/
theorem integral_native_positive_cone {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (Domain n)} (hS : MeasurableSet S) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJpos : ∀ t ∈ J, 0 < t) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let C := {y : Domain (n + 1) | (e y).2 0 ∈ J ∧ ((e y).2 0)⁻¹ • (e y).1 ∈ S}
    ∀ {f : Domain (n + 1) → E}, IntegrableOn f C volume →
      (∫ y in C, f y) =
        ∫ t in J, t ^ n • ∫ x in S,
          f (e.symm (t • x, EuclideanSpace.single (0 : Fin 1) t)) := by
  intro e C f hf
  let P : Domain n × ℝ → Domain (n + 1) := fun p =>
    e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  let V := {p : Domain n × ℝ | p.2 ∈ J ∧ p.2⁻¹ • p.1 ∈ S}
  have hV : MeasurableSet V :=
    (hJ.preimage measurable_snd).inter (hS.preimage (measurable_snd.inv.smul measurable_fst))
  have hC : MeasurableSet C := hV.preimage (measurePreserving_cylinder_coordinates n).measurable
  have hMP := (measurePreserving_cylinder_coordinates_inverse n).restrict_preimage hC
  have hpre : P ⁻¹' C = V := by
    ext p
    simp only [P, C, V, mem_preimage, mem_setOf_eq, e.apply_symm_apply,
      PiLp.single_apply, ite_true]
  change MeasurePreserving P (((volume : Measure (Domain n)).prod volume).restrict
    (P ⁻¹' C)) (volume.restrict C) at hMP
  rw [hpre] at hMP
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let A := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Domain n))
    τ.symm).trans e.symm
  have hsingle (t : ℝ) : τ.symm t = EuclideanSpace.single (0 : Fin 1) t := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  have hAP : (A : Domain n × ℝ → Domain (n + 1)) = P := by
    funext p
    change e.symm (p.1, τ.symm p.2) = e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
    rw [hsingle]
  have hPe : MeasurableEmbedding P := by
    rw [← hAP]
    exact A.toHomeomorph.measurableEmbedding
  have hfp : IntegrableOn (f ∘ P) V ((volume : Measure (Domain n)).prod volume) :=
    (hMP.integrable_comp_emb hPe).mpr hf
  have hfi : Integrable (V.indicator (f ∘ P)) ((volume : Measure (Domain n)).prod volume) :=
    hfp.integrable_indicator hV
  have hN := hMP.integral_comp hPe f
  rw [← hN, ← integral_indicator hV]
  change (∫ p, V.indicator (f ∘ P) p ∂((volume : Measure (Domain n)).prod volume)) = _
  rw [integral_prod_symm _ hfi, ← integral_indicator hJ]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  by_cases ht : t ∈ J
  · rw [Set.indicator_of_mem ht]
    have hpreS : MeasurableSet {x : Domain n | t⁻¹ • x ∈ S} :=
      hS.preimage (continuous_const_smul t⁻¹).measurable
    calc
      _ = ∫ x in {x : Domain n | t⁻¹ • x ∈ S}, (f ∘ P) (x, t) := by
        rw [← integral_indicator hpreS]
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        change V.indicator (f ∘ P) (x, t) =
          {x : Domain n | t⁻¹ • x ∈ S}.indicator (fun x => (f ∘ P) (x, t)) x
        by_cases hx : t⁻¹ • x ∈ S
        · rw [Set.indicator_of_mem (show (x, t) ∈ V from ⟨ht, hx⟩),
            Set.indicator_of_mem (show x ∈ {x : Domain n | t⁻¹ • x ∈ S} from hx)]
        · rw [Set.indicator_of_notMem (show (x, t) ∉ V from fun h => hx h.2),
            Set.indicator_of_notMem (show x ∉ {x : Domain n | t⁻¹ • x ∈ S} from hx)]
      _ = _ := integral_inverse_smul_face (hJpos t ht) hS (fun x => (f ∘ P) (x, t))
  · rw [Set.indicator_of_notMem ht]
    have hz : (fun x : Domain n => V.indicator (f ∘ P) (x, t)) = 0 := by
      funext x
      exact Set.indicator_of_notMem (show (x, t) ∉ V from fun h => ht h.1) (f ∘ P)
    change (∫ x : Domain n, V.indicator (f ∘ P) (x, t)) = 0
    rw [hz]
    exact integral_zero _ _

end StratificationTheory
