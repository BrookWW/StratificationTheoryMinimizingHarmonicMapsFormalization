module

public import HarmonicMaps.Sobolev
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Time cutoffs for actual compact annular tests

A compact annular test determines a compact set of radial time coordinates.
One smooth compact time cutoff equals one on a neighborhood of that set,
so it preserves the original values and coordinate derivatives and removes
the extra time-cutoff term from the annular distributional identity.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ContDiff
namespace StratificationTheory

private theorem exists_interval_cutoff_one_on_compact {a b : ℝ} (hab : a < b)
    {K : Set ℝ} (hK : IsCompact K) (hKab : K ⊆ Ioo a b) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Ioo a b ∧ ∀ t ∈ K, ζ t = 1 ∧ deriv ζ t = 0 := by
  let m := (a + b) / 2
  let R := (b - a) / 2
  have hR : 0 < R := by dsimp [R]; linarith only [hab]
  have hdist (t : ℝ) (ht : t ∈ K) : dist t m < R := by
    rw [Real.dist_eq, abs_lt]
    have htI := hKab ht
    constructor <;> dsimp only [m, R] <;> linarith only [htI.1, htI.2]
  have hdistC : Continuous (fun t : ℝ => dist t m) := continuous_id.dist continuous_const
  obtain ⟨d, hd, hdK⟩ := hK.exists_forall_le'
    hdistC.neg.continuousOn
      (a := -R) (fun t ht => neg_lt_neg (hdist t ht))
  let r₀ := max (-d) (R / 2)
  have hr₀ : 0 < r₀ := (half_pos hR).trans_le (le_max_right _ _)
  have hr₀R : r₀ < R := max_lt (by linarith only [hd]) (half_lt_self hR)
  let rin := (r₀ + R) / 2
  let rout := (rin + R) / 2
  have hrin : 0 < rin := by dsimp only [rin]; linarith only [hr₀, hR]
  have hr₀rin : r₀ < rin := by dsimp only [rin]; linarith only [hr₀R]
  have hrinR : rin < R := by dsimp only [rin]; linarith only [hr₀R]
  have hrinrout : rin < rout := by dsimp only [rout]; linarith only [hrinR]
  have hroutR : rout < R := by dsimp only [rout]; linarith only [hrinR]
  let χ : ContDiffBump m := ⟨rin, rout, hrin, hrinrout⟩
  have hsχ : tsupport (χ : ℝ → ℝ) ⊆ Ioo a b := by
    rw [χ.tsupport_eq]
    intro t ht
    have htD : |t - m| ≤ rout := by simpa only [mem_closedBall, Real.dist_eq] using ht
    have htB := abs_le.mp htD
    constructor <;> dsimp only [m, R] at * <;> linarith only [htB.1, htB.2, hroutR]
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, hsχ, ?_⟩
  intro t ht
  have htD : dist t m < χ.rIn := by
    have hdt := hdK t ht
    change d ≤ -dist t m at hdt
    have hbound : dist t m ≤ r₀ := (by linarith only [hdt] : dist t m ≤ -d).trans (le_max_left _ _)
    exact hbound.trans_lt hr₀rin
  have hEq := χ.eventuallyEq_one_of_mem_ball htD
  refine ⟨χ.one_of_mem_closedBall htD.le, ?_⟩
  exact ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hEq).deriv

/-- Every actual compact annular test admits one compact time cutoff that
preserves both its original coordinate derivatives and its original values,
while its time derivative vanishes on those values. -/
theorem exists_annular_time_test_cutoff {n : ℕ} {a b s : ℝ}
    (hab : a < b) (ha : -1 < a) (hs : 0 < s)
    {ψ : Domain n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Ioo a b ∧
      ∀ (θ : sphere (0 : Domain n) 1) (t : ℝ), t ∈ Ioo a b →
        ζ t * ψ ((s * (1 + t)) • θ.val) = ψ ((s * (1 + t)) • θ.val) ∧
        deriv ζ t * ψ ((s * (1 + t)) • θ.val) = 0 ∧
        ∀ i : Fin n, ζ t * coordinateDerivative ψ hψ i ((s * (1 + t)) • θ.val) =
          coordinateDerivative ψ hψ i ((s * (1 + t)) • θ.val) := by
  let T : Domain n → ℝ := fun x => ‖x‖ / s - 1
  let K := T '' tsupport ψ
  have hT : Continuous T := (continuous_norm.div_const s).sub continuous_const
  have hK : IsCompact K := hcψ.image hT
  have hKab : K ⊆ Ioo a b := by
    rintro t ⟨x, hx, rfl⟩
    have hxs := hsψ hx
    have hlow : a + 1 < ‖x‖ / s := (lt_div_iff₀ hs).mpr (by nlinarith only [hxs.1])
    have hhigh : ‖x‖ / s < b + 1 := (div_lt_iff₀ hs).mpr (by nlinarith only [hxs.2])
    constructor <;> dsimp only [T] <;> linarith only [hlow, hhigh]
  obtain ⟨ζ, hζ, hcζ, hsζ, hζK⟩ := exists_interval_cutoff_one_on_compact hab hK hKab
  refine ⟨ζ, hζ, hcζ, hsζ, ?_⟩
  intro θ t ht
  let z := (s * (1 + t)) • θ.val
  have hnorm : ‖z‖ = s * (1 + t) := by
    dsimp only [z]
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hs.le (by linarith only [ha, ht.1])),
      mem_sphere_zero_iff_norm.mp θ.property, mul_one]
  have hTz : T z = t := by
    dsimp only [T]
    rw [hnorm]
    field_simp
    ring
  by_cases hz : z ∈ tsupport ψ
  · have htK : t ∈ K := ⟨z, hz, hTz⟩
    obtain ⟨hζt, hDζt⟩ := hζK t htK
    refine ⟨?_, ?_, fun i => ?_⟩
    · rw [hζt, one_mul]
    · rw [hDζt, zero_mul]
    · rw [hζt, one_mul]
  · have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
    have hDψz (i : Fin n) : coordinateDerivative ψ hψ i z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hz ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)) h))
    change ζ t * ψ z = ψ z ∧ deriv ζ t * ψ z = 0 ∧
      ∀ i : Fin n, ζ t * coordinateDerivative ψ hψ i z = coordinateDerivative ψ hψ i z
    refine ⟨?_, ?_, fun i => ?_⟩
    · rw [hψz, mul_zero]
    · rw [hψz, mul_zero]
    · rw [hDψz, mul_zero]

end StratificationTheory
