module

public import StratificationTheory.Stratification.StratumDimension
public import StratificationTheory.Stratification.SingularIsolation
public import StratificationTheory.Stratification.SpineConcentration

public section
open HarmonicMaps MeasureTheory MeasureTheory.Measure Metric Set Filter Module
open scoped Topology ENNReal
namespace StratificationTheory

/-- The universal actual-tangent strata are monotone, have the stated top
strata, concentrate their high-density points near planes, and satisfy the
stratified Hausdorff bounds. In dimension three the full singular set has
no accumulation inside the original open domain. -/
theorem stratification_complete {n q : ℕ} (hn : 3 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du) :
    let hn₂ : 2 ≤ n := Nat.le_of_succ_le hn
    (∀ i j : ℕ, i ≤ j →
      singularStratum hn₂ N Ω u Du hu hTarget hMinimizer i ⊆
        singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j) ∧
    singularStratum hn₂ N Ω u Du hu hTarget hMinimizer (n - 3) = singularSet Ω u ∧
    singularStratum hn₂ N Ω u Du hu hTarget hMinimizer (n - 2) = singularSet Ω u ∧
    singularStratum hn₂ N Ω u Du hu hTarget hMinimizer (n - 1) = singularSet Ω u ∧
    (∀ (j : ℕ), j ≤ n →
      ∀ a ∈ singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j,
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
        ∀ ρ : PositiveRadius, ρ.val ≤ ε → closedBall a.val ρ.val ⊆ Ω.val →
          ∃ L : Subspace ℝ (Domain n), finrank ℝ L = j ∧
            ∀ x : Ω.val, x.val ∈ ball a.val ρ.val →
              density hn₂ hMinimizer hu hTarget a - ε ≤ density hn₂ hMinimizer hu hTarget x →
              infDist (ρ.val⁻¹ • (x.val - a.val)) (L : Set (Domain n)) < δ) ∧
    (∀ j : ℕ, j ≤ n - 3 →
      (∀ s : ℝ, (j : ℝ) < s →
        μH[s] (Subtype.val '' singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j) = 0) ∧
      dimH (Subtype.val '' singularStratum hn₂ N Ω u Du hu hTarget hMinimizer j) ≤ (j : ℝ≥0∞)) ∧
    dimH (Subtype.val '' singularSet Ω u) ≤ ((n - 3 : ℕ) : ℝ≥0∞) ∧
    (∀ s : ℝ, (n : ℝ) - 3 < s → μH[s] (Subtype.val '' singularSet Ω u) = 0) ∧
    (n = 3 → ∀ a : Ω.val, ∃ r : ℝ, 0 < r ∧
      ∀ x : Ω.val, x ∈ singularSet Ω u → dist x.val a.val < r → x = a) := by
  intro hn₂
  have hTop (j : ℕ) (hj : n - 3 ≤ j) :=
    singularStratum_eq_singularSet_of_index_ge hn N Ω u Du hu hTarget hMinimizer j hj
  have hBounds (j : ℕ) (hj : j ≤ n - 3) :=
    singularStratum_hausdorff_bounds hn₂ N Ω u Du hu hTarget hMinimizer j (by omega : j ≤ n)
  refine ⟨fun i j hij => singularStratum_mono hn₂ N Ω u Du hu hTarget hMinimizer hij,
    hTop (n - 3) le_rfl, hTop (n - 2) (by omega), hTop (n - 1) (by omega),
    ?_, hBounds, ?_, ?_, ?_⟩
  · intro j hj a ha δ hδ
    have hMember := (mem_singularStratum_iff hn₂ N Ω u Du hu hTarget hMinimizer j a).mp ha
    exact exists_spine_concentration_at_stratum_point hn₂ N Ω u Du hu hTarget hMinimizer
      a hMember.1 j hj hMember.2 δ hδ
  · have h := (hBounds (n - 3) le_rfl).2
    rw [hTop (n - 3) le_rfl] at h
    exact h
  · intro s hs
    have hjs : ((n - 3 : ℕ) : ℝ) < s := by
      rw [Nat.cast_sub hn, Nat.cast_ofNat]
      exact hs
    have h := (hBounds (n - 3) le_rfl).1 s hjs
    rw [hTop (n - 3) le_rfl] at h
    exact h
  · intro hThree
    subst n
    exact fun a => singularSet_no_accumulation_three N Ω u Du hu hTarget hMinimizer a

end StratificationTheory
