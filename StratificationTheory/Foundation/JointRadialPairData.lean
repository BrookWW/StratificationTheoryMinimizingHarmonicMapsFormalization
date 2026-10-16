module

public import StratificationTheory.Foundation.RadialPairExtensionIntegration

/-!
# Joint original radial pair data with all raw value constraints

The same two degree-zero extensions retain their original rays, original
named gradients, exact paired energy and discrepancy, and every original
native a.e. value constraint. In particular, extending to a larger ball
retains the original target values without a cutoff.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- One original radial pair retains both quantitative channels and every
source a.e. value constraint on the same actual finite Sobolev extensions. -/
theorem exists_joint_radial_pair_ball_data {n q : ℕ} (hn : 3 ≤ n)
    (u : Fin 2 → sphere (0 : Domain n) 1 → Ambient q)
    (hu : ∀ l, MemSphereW12 (by omega : 2 ≤ n) (u l))
    {R : ℝ} (hR : 0 < R) :
    ∃ (W : Fin 2 → Domain n → Ambient q) (DW : Fin 2 → Domain n → Gradient n q),
      (∀ l, MemW12 (ballDomain 0 R) (W l) (DW l)) ∧
      (∀ (l : Fin 2) (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
        W l (ρ.val • θ.val) = u l θ) ∧
      (∀ (l : Fin 2) (ρ : PositiveRadius) (i : Fin n),
        (fun θ : sphere (0 : Domain n) 1 => ρ.val • DW l (ρ.val • θ.val) i) =ᵐ[
          Measure.euclideanHausdorffMeasure (n - 1)]
            (fun θ => (sphereGradient (by omega : 2 ≤ n) (u l) (hu l) i) θ)) ∧
      ((∫ x in ball (0 : Domain n) R, hsNormSq (DW 0 x)) +
        (∫ x in ball (0 : Domain n) R, hsNormSq (DW 1 x))) =
          (R ^ (n - 2) / (n - 2)) *
            ((∫ θ : sphere (0 : Domain n) 1,
              hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ n) (u 0) (hu 0) i) θ)
                ∂Measure.euclideanHausdorffMeasure (n - 1)) +
             (∫ θ : sphere (0 : Domain n) 1,
              hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ n) (u 1) (hu 1) i) θ)
                ∂Measure.euclideanHausdorffMeasure (n - 1))) ∧
      (∫ x in ball (0 : Domain n) R, ‖W 0 x - W 1 x‖ ^ 2) =
        (R ^ n / n) * ∫ θ : sphere (0 : Domain n) 1, ‖u 0 θ - u 1 θ‖ ^ 2
          ∂Measure.euclideanHausdorffMeasure (n - 1) ∧
      ∀ (l : Fin 2) (P : Ambient q → Prop),
        (∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n - 1) :
          Measure (sphere (0 : Domain n) 1)), P (u l θ)) →
        ∀ᵐ x ∂volume.restrict (ball (0 : Domain n) R), P (W l x) := by
  choose W DW hW hraw hgradient _hintegrable henergy hvalues using
    fun l : Fin 2 => exists_radial_ball_sobolev_extension hn (u l) (hu l) hR
  refine ⟨W, DW, hW, hraw, hgradient, ?_, ?_, hvalues⟩
  · rw [henergy 0, henergy 1, mul_add]
  · exact (radial_pair_discrepancy_identity (by omega) (hu 0).1 (hu 1).1
      (hraw 0) (hraw 1) hR).2

end StratificationTheory
