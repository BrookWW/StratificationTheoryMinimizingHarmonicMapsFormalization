module

public import StratificationTheory.Compactness.TotallyBoundedTransfer
public import HarmonicMaps.Analysis.VariableMollificationL2

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace StratificationTheory.Compactness

/-- A finite measurable-region cover transfers L2 total boundedness from its
individual regions to every covered region. The functions are the same actual
ambient functions on all pieces. -/
theorem L2_totallyBounded_of_finite_cover {α E ι J : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [CompleteSpace E] [Fintype J]
    (μ : Measure α) (K : Set α) (U : J → Set α) (hcover : K ⊆ ⋃ j, U j)
    (u : ι → α → E)
    (hK : ∀ k, MemLp (u k) 2 (μ.restrict K))
    (hU : ∀ j k, MemLp (u k) 2 (μ.restrict (U j)))
    (hTB : ∀ j, TotallyBounded (range (fun k => (hU j k).toLp (u k)))) :
    TotallyBounded (range (fun k => (hK k).toLp (u k))) := by
  let H (j : J) : Type _ := Lp E 2 (μ.restrict (U j))
  let f (j : J) (k : ι) : H j := (hU j k).toLp (u k)
  let P (k : ι) : PiLp 2 H := WithLp.toLp 2 (fun j => f j k)
  let C (j : J) : Set (H j) := closure (range (f j))
  have hC (j : J) : IsCompact (C j) := (hTB j).closure.isCompact_of_isClosed isClosed_closure
  have hprod : IsCompact (WithLp.toLp 2 '' {x : (j : J) → H j | ∀ j, x j ∈ C j}) :=
    (isCompact_pi_infinite hC).image (PiLp.continuous_toLp 2 H)
  have hPTB : TotallyBounded (range P) := hprod.totallyBounded.subset (by
    rintro _ ⟨k, rfl⟩
    refine ⟨(fun j => f j k), ?_, rfl⟩
    exact fun j => subset_closure (mem_range_self k))
  have hμ : μ.restrict K ≤ ∑ j : J, μ.restrict (U j) := by
    calc
      μ.restrict K ≤ μ.restrict (⋃ j : J, U j) := Measure.restrict_mono_set μ hcover
      _ ≤ Measure.sum (fun j : J => μ.restrict (U j)) := Measure.restrict_iUnion_le
      _ = ∑ j : J, μ.restrict (U j) := Measure.sum_fintype _
  apply totallyBounded_range_of_dist_control P _ hPTB 1 (by norm_num)
  intro k l
  have hDiff (j : J) : Integrable (fun x => ‖u k x - u l x‖ ^ 2) (μ.restrict (U j)) :=
    ((hU j k).sub (hU j l)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hDiffSum : Integrable (fun x => ‖u k x - u l x‖ ^ 2) (∑ j : J, μ.restrict (U j)) :=
    integrable_finsetSum_measure.mpr (fun j _ => hDiff j)
  have hIntegral : (∫ x in K, ‖u k x - u l x‖ ^ 2 ∂μ) ≤
      ∑ j : J, ∫ x in U j, ‖u k x - u l x‖ ^ 2 ∂μ := by
    calc
      (∫ x in K, ‖u k x - u l x‖ ^ 2 ∂μ) ≤
          ∫ x, ‖u k x - u l x‖ ^ 2 ∂∑ j : J, μ.restrict (U j) :=
        integral_mono_measure hμ (Eventually.of_forall fun x => sq_nonneg _) hDiffSum
      _ = ∑ j : J, ∫ x in U j, ‖u k x - u l x‖ ^ 2 ∂μ :=
        integral_finsetSum_measure (fun j _ => hDiff j)
  have hKsq : dist ((hK k).toLp (u k)) ((hK l).toLp (u l)) ^ 2 =
      ∫ x in K, ‖u k x - u l x‖ ^ 2 ∂μ := by
    rw [dist_eq_norm, ← (hK k).toLp_sub (hK l), Lp.norm_toLp,
      ← integral_norm_sq_eq_eLpNorm_two_toReal_sq ((hK k).sub (hK l))]
    rfl
  have hPsq : dist (P k) (P l) ^ 2 =
      ∑ j : J, ∫ x in U j, ‖u k x - u l x‖ ^ 2 ∂μ := by
    rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [P, f, PiLp.sub_apply, PiLp.toLp_apply]
    rw [← (hU j k).toLp_sub (hU j l), Lp.norm_toLp,
      ← integral_norm_sq_eq_eLpNorm_two_toReal_sq ((hU j k).sub (hU j l))]
    rfl
  have hdist : dist ((hK k).toLp (u k)) ((hK l).toLp (u l)) ≤ dist (P k) (P l) := by
    apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
    simpa only [hKsq, hPsq] using hIntegral
  simpa only [one_mul] using hdist

end StratificationTheory.Compactness
