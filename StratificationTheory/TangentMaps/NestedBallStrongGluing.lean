module

public import StratificationTheory.Foundation.NestedNaturalSubsequences
public import StratificationTheory.Compactness.AELocalGluing
public import HarmonicMaps.Analysis.SobolevAECongruence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.MetricSpace.Bounded

public section
open HarmonicMaps MeasureTheory Metric Filter Set
open scoped Topology ENNReal
namespace StratificationTheory

private theorem ae_eq_of_two_strong_limits {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f : ℕ → α → E} {g h : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hfg : Tendsto (fun k => eLpNorm (f k - g) 2 μ) atTop (𝓝 0))
    (hfh : Tendsto (fun k => eLpNorm (f k - h) 2 μ) atTop (𝓝 0)) : g =ᵐ[μ] h := by
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hf k).aestronglyMeasurable) hg.aestronglyMeasurable hfg)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hf k).aestronglyMeasurable) hh.aestronglyMeasurable hfh)

private theorem closed_nat_ball_subset {n i j : ℕ} (hij : i ≤ j) :
    closedBall (0 : Domain n) ((i : ℝ) + 1) ⊆ ball 0 ((j : ℝ) + 2) := by
  apply closedBall_subset_ball
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- Actual nested strong limits of the original maps and columns agree
almost everywhere on every earlier closed ball. -/
theorem nested_ball_limits_ae_consistent {n q : ℕ}
    (σ η : ℕ → (ℕ ↪o ℕ)) (hStep : ∀ j k, σ (j + 1) k = σ j (η j k))
    (U : ℕ → Domain n → Ambient q) (D : ℕ → Domain n → Gradient n q)
    (v : ℕ → Domain n → Ambient q) (Dv : ℕ → Domain n → Gradient n q)
    (hSource : ∀ (j k : ℕ), MemW12 (ballDomain (0 : Domain n) ((j : ℝ) + 2))
      (U (σ (j + 1) k)) (D (σ (j + 1) k)))
    (hLocal : ∀ j : ℕ, MemW12Loc (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j) (Dv j))
    (hStrong : ∀ (j : ℕ) K, IsCompact K → K ⊆ (ballDomain (0 : Domain n) ((j : ℝ) + 2)).val →
      Tendsto (fun k => eLpNorm (U (σ (j + 1) k) - v j) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D (σ (j + 1) k) x i - Dv j x i)
        2 (volume.restrict K)) atTop (𝓝 0)) :
    ∀ (i j : ℕ), i ≤ j →
      v i =ᵐ[volume.restrict (closedBall 0 ((i : ℝ) + 1))] v j ∧
      Dv i =ᵐ[volume.restrict (closedBall 0 ((i : ℝ) + 1))] Dv j := by
  intro i j hij
  let K := closedBall (0 : Domain n) ((i : ℝ) + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKi : K ⊆ (ballDomain (0 : Domain n) ((i : ℝ) + 2)).val := closed_nat_ball_subset le_rfl
  have hKj : K ⊆ (ballDomain (0 : Domain n) ((j : ℝ) + 2)).val := closed_nat_ball_subset hij
  obtain ⟨τ, hτ⟩ := nested_natural_subsequence_factor σ η hStep (Nat.add_le_add_right hij 1)
  have hMapI : Tendsto (fun k => eLpNorm (U (σ (j + 1) k) - v i) 2 (volume.restrict K)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hτ] using
      ((hStrong i K hK hKi).1.comp τ.strictMono.tendsto_atTop)
  have hMapJ := (hStrong j K hK hKj).1
  have hMap : v i =ᵐ[volume.restrict K] v j :=
    ae_eq_of_two_strong_limits
      (fun k => (hSource j k).2.1.mono_measure (Measure.restrict_mono_set volume hKj))
      ((hLocal i).2.1 K hK hKi) ((hLocal j).2.1 K hK hKj) hMapI hMapJ
  have hCols (s : Fin n) : (fun x => Dv i x s) =ᵐ[volume.restrict K] (fun x => Dv j x s) := by
    have hLeft : Tendsto (fun k => eLpNorm (fun x => D (σ (j + 1) k) x s - Dv i x s)
        2 (volume.restrict K)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hτ] using
        ((hStrong i K hK hKi).2 s).comp τ.strictMono.tendsto_atTop
    exact ae_eq_of_two_strong_limits
      (fun k => ((hSource j k).2.2 s).mono_measure (Measure.restrict_mono_set volume hKj))
      ((hLocal i).2.2 s K hK hKi) ((hLocal j).2.2 s K hK hKj)
      hLeft ((hStrong j K hK hKj).2 s)
  refine ⟨hMap, ?_⟩
  filter_upwards [ae_all_iff.mpr hCols] with x hx
  exact funext hx

/-- A genuine nested family of actual strong local weak-graph limits has
one diagonal original-index subsequence and one AE-consistent global pair.
Every compact region has genuine eventual source L2 data and strong limits. -/
theorem exists_nested_ball_strong_gluing {n q : ℕ}
    (σ η : ℕ → (ℕ ↪o ℕ)) (hStep : ∀ j k, σ (j + 1) k = σ j (η j k))
    (U : ℕ → Domain n → Ambient q) (D : ℕ → Domain n → Gradient n q)
    (v : ℕ → Domain n → Ambient q) (Dv : ℕ → Domain n → Gradient n q)
    (hSource : ∀ (j k : ℕ), MemW12 (ballDomain (0 : Domain n) ((j : ℝ) + 2))
      (U (σ (j + 1) k)) (D (σ (j + 1) k)))
    (hLocal : ∀ j : ℕ, MemW12Loc (ballDomain (0 : Domain n) ((j : ℝ) + 2)) (v j) (Dv j))
    (hStrong : ∀ (j : ℕ) K, IsCompact K → K ⊆ (ballDomain (0 : Domain n) ((j : ℝ) + 2)).val →
      Tendsto (fun k => eLpNorm (U (σ (j + 1) k) - v j) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D (σ (j + 1) k) x i - Dv j x i)
        2 (volume.restrict K)) atTop (𝓝 0)) :
    ∃ (κ : ℕ → ℕ) (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
      StrictMono κ ∧
      (∀ j : ℕ, φ =ᵐ[volume.restrict (closedBall 0 ((j : ℝ) + 1))] v j) ∧
      (∀ j : ℕ, Dφ =ᵐ[volume.restrict (closedBall 0 ((j : ℝ) + 1))] Dv j) ∧
      ∀ K : Set (Domain n), IsCompact K →
        (∀ᶠ k in atTop, MemLp (U (κ k)) 2 (volume.restrict K) ∧
          ∀ i : Fin n, MemLp (fun x => D (κ k) x i) 2 (volume.restrict K)) ∧
        Tendsto (fun k => eLpNorm (U (κ k) - φ) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D (κ k) x i - Dφ x i)
          2 (volume.restrict K)) atTop (𝓝 0) := by
  have hCons := nested_ball_limits_ae_consistent σ η hStep U D v Dv hSource hLocal hStrong
  let K : ℕ → Set (Domain n) := fun j => closedBall 0 ((j : ℝ) + 1)
  obtain ⟨φ, hφ⟩ := Compactness.exists_ae_glue_countable_regions volume K
    (fun _ => measurableSet_closedBall) v (fun i j hij => (hCons i j hij).1)
  obtain ⟨Dφ, hDφ⟩ := Compactness.exists_ae_glue_countable_regions volume K
    (fun _ => measurableSet_closedBall) Dv (fun i j hij => (hCons i j hij).2)
  obtain ⟨κ, hκ, hDiag⟩ := exists_nested_natural_subsequence_diagonal σ η hStep
  refine ⟨κ, φ, Dφ, hκ, hφ, hDφ, ?_⟩
  intro T hT
  obtain ⟨R, hTR⟩ := hT.isBounded.subset_closedBall (0 : Domain n)
  obtain ⟨j, hj⟩ := exists_nat_gt R
  have hTK : T ⊆ K j := hTR.trans (closedBall_subset_closedBall (by linarith))
  have hTL : T ⊆ (ballDomain (0 : Domain n) ((j : ℝ) + 2)).val :=
    hTK.trans (closed_nat_ball_subset le_rfl)
  have hφT : φ =ᵐ[volume.restrict T] v j := ae_restrict_of_ae_restrict_of_subset hTK (hφ j)
  have hDφT : Dφ =ᵐ[volume.restrict T] Dv j := ae_restrict_of_ae_restrict_of_subset hTK (hDφ j)
  obtain ⟨τ, hτ⟩ := hDiag (j + 1)
  have hSourceShift (k : ℕ) : MemLp (U (κ (k + (j + 1)))) 2 (volume.restrict T) ∧
      ∀ s : Fin n, MemLp (fun x => D (κ (k + (j + 1))) x s) 2 (volume.restrict T) := by
    rw [hτ k]
    exact ⟨(hSource j (τ k)).2.1.mono_measure (Measure.restrict_mono_set volume hTL),
      fun s => ((hSource j (τ k)).2.2 s).mono_measure (Measure.restrict_mono_set volume hTL)⟩
  have hEvent : ∀ᶠ k in atTop, MemLp (U (κ k)) 2 (volume.restrict T) ∧
      ∀ s : Fin n, MemLp (fun x => D (κ k) x s) 2 (volume.restrict T) := by
    apply eventually_atTop.2
    refine ⟨j + 1, ?_⟩
    intro k hk
    simpa only [Nat.sub_add_cancel hk] using hSourceShift (k - (j + 1))
  have hMapShift : Tendsto (fun k => eLpNorm (U (κ (k + (j + 1))) - v j) 2 (volume.restrict T))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, hτ] using
      ((hStrong j T hT hTL).1.comp τ.strictMono.tendsto_atTop)
  have hMap : Tendsto (fun k => eLpNorm (U (κ k) - v j) 2 (volume.restrict T)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun k => eLpNorm (U (κ k) - v j) 2 (volume.restrict T)) (j + 1)).mp hMapShift
  refine ⟨hEvent, ?_, ?_⟩
  · apply hMap.congr
    intro k
    exact eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub hφT.symm)
  · intro s
    have hColShift : Tendsto (fun k => eLpNorm (fun x => D (κ (k + (j + 1))) x s - Dv j x s)
        2 (volume.restrict T)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hτ] using
        (((hStrong j T hT hTL).2 s).comp τ.strictMono.tendsto_atTop)
    have hCol : Tendsto (fun k => eLpNorm (fun x => D (κ k) x s - Dv j x s) 2 (volume.restrict T)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat (f := fun k => eLpNorm (fun x => D (κ k) x s - Dv j x s) 2 (volume.restrict T)) (j + 1)).mp hColShift
    apply hCol.congr
    intro k
    exact eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub
      (hDφT.symm.mono fun x hx => congrFun hx s))

end StratificationTheory
