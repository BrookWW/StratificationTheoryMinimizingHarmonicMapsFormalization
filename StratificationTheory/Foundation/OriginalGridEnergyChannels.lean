module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Original ball energy and discrepancy channels for grid selection

The two scalar channels are the literal ball indicators of the original
Hilbert--Schmidt energy sum and original squared map discrepancy. Their
measurability, finiteness and exact native integral identities follow from
the original finite Sobolev pair.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original finite Sobolev ball data internally supply both native scalar
channels, with the exact original energy and discrepancy integrals. -/
theorem original_pair_ball_energy_discrepancy_channels {n q : ℕ}
    {z : Domain n} {R : ℝ}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain z R) u Du) (hv : MemW12 (ballDomain z R) v Dv) :
    let E := (ball z R).indicator (fun x => ENNReal.ofReal (hsNormSq (Du x) + hsNormSq (Dv x)))
    let D := (ball z R).indicator (fun x => ENNReal.ofReal (‖u x - v x‖ ^ 2))
    AEMeasurable E volume ∧ AEMeasurable D volume ∧
      (∫⁻ x, E x) ≠ ⊤ ∧ (∫⁻ x, D x) ≠ ⊤ ∧
      (∫⁻ x, E x) = dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R) ∧
      (∫⁻ x, D x) = ENNReal.ofReal (∫ x in ball z R, ‖u x - v x‖ ^ 2) ∧
      (∫⁻ x, E x) = ENNReal.ofReal
        ((∫ x in ball z R, hsNormSq (Du x)) + (∫ x in ball z R, hsNormSq (Dv x))) := by
  intro E D
  have hEI := hu.integrable_hsNormSq.add hv.integrable_hsNormSq
  have hDI := (hu.2.1.sub hv.2.1).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hE : AEMeasurable E volume :=
    (aemeasurable_indicator_iff measurableSet_ball).mpr hEI.aemeasurable.ennreal_ofReal
  have hD : AEMeasurable D volume :=
    (aemeasurable_indicator_iff measurableSet_ball).mpr hDI.aemeasurable.ennreal_ofReal
  have henergy : (∫⁻ x, E x) =
      dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R) := by
    rw [lintegral_indicator measurableSet_ball]
    simp_rw [ENNReal.ofReal_add (hsNormSq_nonneg (Du _)) (hsNormSq_nonneg (Dv _))]
    exact lintegral_add_left' hu.integrable_hsNormSq.aemeasurable.ennreal_ofReal _
  have hdiscrepancy : (∫⁻ x, D x) = ENNReal.ofReal (∫ x in ball z R, ‖u x - v x‖ ^ 2) := by
    rw [lintegral_indicator measurableSet_ball]
    exact (ofReal_integral_eq_lintegral_ofReal hDI
      (Eventually.of_forall fun _ => sq_nonneg _)).symm
  have henergyReal : (∫⁻ x, E x) = ENNReal.ofReal
      ((∫ x in ball z R, hsNormSq (Du x)) + (∫ x in ball z R, hsNormSq (Dv x))) := by
    rw [lintegral_indicator measurableSet_ball]
    calc
      _ = ENNReal.ofReal (∫ x in ball z R, hsNormSq (Du x) + hsNormSq (Dv x)) :=
        (ofReal_integral_eq_lintegral_ofReal hEI
          (Eventually.of_forall fun x =>
            add_nonneg (hsNormSq_nonneg (Du x)) (hsNormSq_nonneg (Dv x)))).symm
      _ = _ := congrArg ENNReal.ofReal (integral_add hu.integrable_hsNormSq hv.integrable_hsNormSq)
  refine ⟨hE, hD, ?_, ?_, henergy, hdiscrepancy, henergyReal⟩
  · rw [henergy]
    exact ENNReal.add_ne_top.mpr ⟨hu.dirichletEnergy_ne_top, hv.dirichletEnergy_ne_top⟩
  · rw [hdiscrepancy]
    exact ENNReal.ofReal_ne_top

end StratificationTheory
