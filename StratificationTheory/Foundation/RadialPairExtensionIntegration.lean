module
public import StratificationTheory.Frozen.SphereRadialBallExtension
public import StratificationTheory.Foundation.RadialL2Transfer
public import HarmonicMaps.Analysis.VariableMollificationL2
public section
open HarmonicMaps StratificationTheory MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory
noncomputable section
/-- The same two raw radial extensions have the exact native ball discrepancy
for the original sphere pair. The origin value is unrestricted. -/
theorem radial_pair_discrepancy_identity {n q : ℕ} (hn : 0 < n)
    {u v : sphere (0 : Domain n) 1 → Ambient q}
    (hu : MemLp u 2 (Measure.euclideanHausdorffMeasure (n-1)))
    (hv : MemLp v 2 (Measure.euclideanHausdorffMeasure (n-1)))
    {U V : Domain n → Ambient q}
    (hU : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), U (ρ.val • θ.val) = u θ)
    (hV : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), V (ρ.val • θ.val) = v θ)
    {R : ℝ} (hR : 0 < R) :
    MemLp (U - V) 2 (volume.restrict (ball (0 : Domain n) R)) ∧
    (∫ x in ball (0 : Domain n) R, ‖U x - V x‖ ^ 2) =
      (R ^ n / n) * ∫ θ : sphere (0 : Domain n) 1, ‖u θ - v θ‖ ^ 2
        ∂Measure.euclideanHausdorffMeasure (n-1) := by
  have hσ := euclideanHausdorffMeasure_unitSphere_eq_toSphere (n:=n) hn
  have hd : MemLp (u-v) 2 (volume : Measure (Domain n)).toSphere := by
    rw [← hσ]
    exact hu.sub hv
  have hray : ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1),
      (U-V) (ρ.val • θ.val) = (u-v) θ := by
    intro ρ θ
    simp only [Pi.sub_apply,hU,hV]
  obtain ⟨hLp,hnorm⟩ := memLp_two_radial_ball_and_norm hn hd hray hR
  refine ⟨hLp,?_⟩
  have hnonneg : 0 ≤ R ^ n / (n:ℝ) := div_nonneg (pow_nonneg hR.le n) (Nat.cast_nonneg n)
  have hfactor : ((ENNReal.ofReal (R ^ n / (n:ℝ))) ^ (1/2:ℝ)).toReal ^ 2 = R ^ n / n := by
    rw [← ENNReal.toReal_rpow,ENNReal.toReal_ofReal hnonneg]
    have ht := Real.rpow_inv_natCast_pow (n:=2) hnonneg (by decide)
    convert ht using 1
    norm_num
  have hleft := integral_norm_sq_eq_eLpNorm_two_toReal_sq hLp
  have hright := integral_norm_sq_eq_eLpNorm_two_toReal_sq hd
  change (∫ x in ball (0 : Domain n) R, ‖U x-V x‖^2) = _ at hleft
  rw [hleft,hnorm,ENNReal.toReal_mul,mul_pow,hfactor]
  rw [← hright]
  rw [← hσ]
  rfl

/-- Original sphere Sobolev data in dimension at least three produce one pair
of actual radial weak extensions, their named-gradient energy sum and the
exact discrepancy identity for those same extensions. -/
theorem exists_joint_radial_ball_extensions {n q : ℕ} (hn : 3 ≤ n)
    (u v : sphere (0 : Domain n) 1 → Ambient q)
    (hu : MemSphereW12 (by omega : 2 ≤ n) u)
    (hv : MemSphereW12 (by omega : 2 ≤ n) v) {R : ℝ} (hR : 0 < R) :
    ∃ (U : Domain n → Ambient q) (DU : Domain n → Gradient n q)
      (V : Domain n → Ambient q) (DV : Domain n → Gradient n q),
      MemW12 (ballDomain 0 R) U DU ∧ MemW12 (ballDomain 0 R) V DV ∧
      (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), U (ρ.val • θ.val) = u θ) ∧
      (∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1), V (ρ.val • θ.val) = v θ) ∧
      (∀ (ρ : PositiveRadius) (i : Fin n),
        (fun θ : sphere (0 : Domain n) 1 => ρ.val • DU (ρ.val • θ.val) i) =ᵐ[
          Measure.euclideanHausdorffMeasure (n-1)]
            (fun θ => (sphereGradient (by omega : 2 ≤ n) u hu i) θ)) ∧
      (∀ (ρ : PositiveRadius) (i : Fin n),
        (fun θ : sphere (0 : Domain n) 1 => ρ.val • DV (ρ.val • θ.val) i) =ᵐ[
          Measure.euclideanHausdorffMeasure (n-1)]
            (fun θ => (sphereGradient (by omega : 2 ≤ n) v hv i) θ)) ∧
      (∫ x in ball (0 : Domain n) R, hsNormSq (DU x)) +
        (∫ x in ball (0 : Domain n) R, hsNormSq (DV x)) =
          (R ^ (n-2) / (n-2)) *
            ((∫ θ : sphere (0 : Domain n) 1, hsNormSq
              (fun i => (sphereGradient (by omega : 2 ≤ n) u hu i) θ)
              ∂Measure.euclideanHausdorffMeasure (n-1)) +
             (∫ θ : sphere (0 : Domain n) 1, hsNormSq
              (fun i => (sphereGradient (by omega : 2 ≤ n) v hv i) θ)
              ∂Measure.euclideanHausdorffMeasure (n-1))) ∧
      (∫ x in ball (0 : Domain n) R, ‖U x - V x‖ ^ 2) =
        (R ^ n / n) * ∫ θ : sphere (0 : Domain n) 1, ‖u θ - v θ‖ ^ 2
          ∂Measure.euclideanHausdorffMeasure (n-1) := by
  obtain ⟨U,DU,hUW,hUraw,hUG,hUI,hUE,hUP⟩ := exists_radial_ball_sobolev_extension hn u hu hR
  obtain ⟨V,DV,hVW,hVraw,hVG,hVI,hVE,hVP⟩ := exists_radial_ball_sobolev_extension hn v hv hR
  refine ⟨U,DU,V,DV,hUW,hVW,hUraw,hVraw,hUG,hVG,?_,?_⟩
  · rw [hUE,hVE,mul_add]
  · exact (radial_pair_discrepancy_identity (by omega) hu.1 hv.1 hUraw hVraw hR).2
end
end StratificationTheory
