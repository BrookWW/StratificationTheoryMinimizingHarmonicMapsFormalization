module

public import StratificationTheory.TangentMaps.RescaledDomains
public import StratificationTheory.Foundation.RescaledEnergyBounds
public import StratificationTheory.Compactness.LocalStrongCompactness

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal NNReal

namespace StratificationTheory

/-- Every prescribed positive shrinking scale sequence has an actual strong
minimizing subsequential limit on a fixed positive origin ball. The tail
qualifications and energy bounds are produced from the original local map. -/
theorem exists_rescaled_fixed_ball_strong_subsequence {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hTarget : TakesValuesIn N Ω u)
    (hMinimizer : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ))) (L : PositiveRadius) :
    let U : ℕ → Domain n → Ambient q := fun k x => u (a.val + (ρ k).val • x)
    let D : ℕ → Domain n → Gradient n q := fun k x i => (ρ k).val • Du (a.val + (ρ k).val • x) i
    ∃ (tail : ℕ) (κ : ℕ → ℕ) (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      (∀ j, tail ≤ j →
        MemW12 (ballDomain (0 : Domain n) L.val) (U j) (D j) ∧
        TakesValuesIn N (ballDomain (0 : Domain n) L.val) (U j) ∧
        IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L.val) (U j) (D j)) ∧
      StrictMono κ ∧ (∀ k, tail ≤ κ k) ∧
      MemW12Loc (ballDomain (0 : Domain n) L.val) v Dv ∧
      TakesValuesIn N (ballDomain (0 : Domain n) L.val) v ∧
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L.val) v Dv ∧
      ∀ K : Set (Domain n), IsCompact K → K ⊆ (ballDomain (0 : Domain n) L.val).val →
        Tendsto (fun k => eLpNorm (U (κ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D (κ k) x i - Dv x i)
          2 (volume.restrict K)) atTop (𝓝 0) := by
  intro U D
  obtain ⟨r₀, hr₀, hClosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.property.mem_nhds a.property)
  let r : PositiveRadius := ⟨r₀, hr₀⟩
  have hQual := eventually_rescaled_minimizer_on_ball N Ω a.property u Du hu hTarget hMinimizer
    (centers := fun _ : ℕ => a.val) (scales := ρ) tendsto_const_nhds hρ L
  have hBound := hMinimizer.rescaled_sequence_eventually_energy_bound hn hu hTarget a.val r L hClosed ρ hρ
  obtain ⟨tail, hTail⟩ := eventually_atTop.mp (hQual.and hBound)
  let C : ℝ≥0 := ⟨L.val ^ ((n : ℤ) - 2) * (normalizedEnergy Du a.val r).toReal,
    mul_nonneg (zpow_nonneg L.property.le _) ENNReal.toReal_nonneg⟩
  have hActual (j : ℕ) (hj : tail ≤ j) :
      MemW12 (ballDomain (0 : Domain n) L.val) (U j) (D j) ∧
      TakesValuesIn N (ballDomain (0 : Domain n) L.val) (U j) ∧
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L.val) (U j) (D j) := (hTail j hj).1
  have hTotal (j : ℕ) (hj : tail ≤ j) : dirichletEnergy (D j) (ball (0 : Domain n) L.val) ≤ C := by
    apply (ENNReal.toReal_le_toReal (hTail j hj).2.1 ENNReal.coe_ne_top).mp
    rw [ENNReal.coe_toReal]
    change (dirichletEnergy (D j) (ball (0 : Domain n) L.val)).toReal ≤
      L.val ^ ((n : ℤ) - 2) * (normalizedEnergy Du a.val r).toReal
    exact (hTail j hj).2.2
  let Utail : ℕ → Domain n → Ambient q := fun k => U (tail + k)
  let Dtail : ℕ → Domain n → Gradient n q := fun k => D (tail + k)
  have hSobTail : ∀ k, MemW12Loc (ballDomain (0 : Domain n) L.val) (Utail k) (Dtail k) := by
    intro k
    exact (hActual (tail + k) (by omega)).1.to_memW12Loc
  have hTargetTail : ∀ k, TakesValuesIn N (ballDomain (0 : Domain n) L.val) (Utail k) := by
    intro k
    exact (hActual (tail + k) (by omega)).2.1
  have hMinTail : ∀ k, IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) L.val) (Utail k) (Dtail k) := by
    intro k
    exact (hActual (tail + k) (by omega)).2.2
  have hEnergyTail : ∀ (c : Domain n) (s : ℝ), 0 < s →
      closedBall c s ⊆ (ballDomain (0 : Domain n) L.val).val →
      ∃ B : ℝ≥0, ∀ k, dirichletEnergy (Dtail k) (ball c s) ≤ B := by
    intro c s _hs hsL
    refine ⟨C, fun k => ?_⟩
    exact (dirichletEnergy_le_of_subset (Dtail k) (ball_subset_closedBall.trans hsL)).trans
      (hTotal (tail + k) (by omega))
  obtain ⟨κ₀, v, Dv, hκ₀, hv, hvN, hMinV, hStrong⟩ :=
    strongCompactness_of_local_sobolev hn N (ballDomain (0 : Domain n) L.val)
      Utail Dtail hSobTail hTargetTail hMinTail hEnergyTail
  let κ : ℕ → ℕ := fun k => tail + κ₀ k
  have hκ : StrictMono κ := fun _ _ hij => Nat.add_lt_add_left (hκ₀ hij) tail
  refine ⟨tail, κ, v, Dv, hActual, hκ, (fun _ => by dsimp only [κ]; omega), hv, hvN, hMinV, ?_⟩
  intro K hK hKL
  exact hStrong K hK hKL

end StratificationTheory
