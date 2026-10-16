module

public import StratificationTheory.Foundation.AllRankGridEnergyBudget
public import StratificationTheory.Foundation.OriginalCoordinateLineChannels

/-! # Actual original face energies in the common all-rank grid budget -/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Actual paired real energies of the displayed original face columns are
bounded by the same native ambient channel. This inequality does not assert
integrability; source weak graphs supply that separate fact. -/
theorem original_coordinate_face_real_pair_energy_le_native_channel {N k q : ℕ}
    {z₀ : Domain N} {R : ℝ} (face : Fin k ↪ Fin N) (A : Domain k → Domain N)
    {U V : Set (Domain k)} (hU : MeasurableSet U) (hUV : U ⊆ V)
    (hImage : ∀ t ∈ U, A t ∈ ball z₀ R) (Du Dv : Domain N → Gradient N q) :
    ENNReal.ofReal ((∫ t in U, hsNormSq (fun j : Fin k => Du (A t) (face j))) +
      ∫ t in U, hsNormSq (fun j : Fin k => Dv (A t) (face j))) ≤
      ∫⁻ t in V, (ball z₀ R).indicator
        (fun x => ENNReal.ofReal (hsNormSq (Du x) + hsNormSq (Dv x))) (A t) := by
  rw [ENNReal.ofReal_add (integral_nonneg fun _ => hsNormSq_nonneg _)
    (integral_nonneg fun _ => hsNormSq_nonneg _)]
  calc
    _ ≤ dirichletEnergy (fun t j => Du (A t) (face j)) U +
        dirichletEnergy (fun t j => Dv (A t) (face j)) U :=
      add_le_add (ofReal_nonnegative_integral_le_lintegral _ (fun _ => hsNormSq_nonneg _))
        (ofReal_nonnegative_integral_le_lintegral _ (fun _ => hsNormSq_nonneg _))
    _ ≤ _ := original_coordinate_face_energy_le_native_channel face A hU hUV hImage Du Dv

/-- Every original face rank of a finite actual cell family is controlled
jointly by the original selected channels. Local incidence counts are
finite; the number of parent cells is handled by the whole lattice sum. -/
theorem all_rank_actual_original_face_energy_budget {m q : ℕ} {G I J : Type*}
    [AddGroup G] [Fintype I] {ε : ℝ} (hε : 0 < ε)
    {z₀ : Domain m} {R : ℝ} (rank : J → ℕ)
    (face : ∀ j, Fin (rank j) ↪ Fin m) (origin : G → Domain m)
    (Dw : Fin 2 → Domain m → Gradient m q) (count : ℕ)
    (index : I → J) (shift : I → G) (parents : Finset G) :
    let U := fun j : J => ⋂ k : Fin (rank j), (EuclideanSpace.proj k) ⁻¹' Ioo (0 : ℝ) ε
    let V := fun j : J => ⋂ k : Fin (rank j), (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let A := fun (j : J) (z : G) (t : Domain (rank j)) =>
      origin z + ∑ k : Fin (rank j), t k • EuclideanSpace.single (face j k) (1 : ℝ)
    let Eraw := (ball z₀ R).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let channel := fun j z => ∫⁻ t in V j, Eraw (A j z t)
    let A₀ := ENNReal.ofReal ((∫ x in ball z₀ R, hsNormSq (Dw 0 x)) +
      ∫ x in ball z₀ R, hsNormSq (Dw 1 x))
    (∀ j, (∑' z : G, channel j z) ≤ 2 * (ENNReal.ofReal (ε ^ m))⁻¹ *
      ((count : ℝ≥0∞) * ENNReal.ofReal (ε ^ rank j)) * A₀) →
    (∀ z ∈ parents, ∀ i : I, ∀ t ∈ U (index i), A (index i) (z + shift i) t ∈ ball z₀ R) →
    (∑ z ∈ parents, ∑ i : I, ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) *
      ENNReal.ofReal
        ((∫ t in U (index i), hsNormSq
          (fun k : Fin (rank (index i)) => Dw 0 (A (index i) (z + shift i) t) (face (index i) k))) +
          ∫ t in U (index i), hsNormSq
            (fun k : Fin (rank (index i)) => Dw 1 (A (index i) (z + shift i) t) (face (index i) k)))) ≤
      2 * (count : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞) * ENNReal.ofReal ε * A₀ := by
  intro U V A Eraw channel A₀ hSelect hContained
  have hRank (j : J) : rank j ≤ m := by
    have h := Fintype.card_le_of_injective (face j) (face j).injective
    simpa only [Fintype.card_fin] using h
  have hNative (z : G) (hz : z ∈ parents) (i : I) :=
    original_coordinate_face_real_pair_energy_le_native_channel (U := U (index i)) (V := V (index i))
      (face (index i)) (A (index i) (z + shift i))
      (MeasurableSet.iInter fun k : Fin (rank (index i)) =>
        measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable)
      (by
        intro t ht
        exact mem_iInter.mpr fun k => ⟨(mem_iInter.mp ht k).1.le, (mem_iInter.mp ht k).2⟩)
      (hContained z hz i) (Dw 0) (Dw 1)
  calc
    _ ≤ ∑ z ∈ parents, ∑ i : I,
        ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) * channel (index i) (z + shift i) := by
      apply Finset.sum_le_sum
      intro z hz
      exact Finset.sum_le_sum fun i _ => mul_le_mul_right (hNative z hz i) _
    _ ≤ ∑' z : G, ∑ i : I,
        ENNReal.ofReal (ε ^ (m - rank (index i) + 1)) * channel (index i) (z + shift i) :=
      ENNReal.sum_le_tsum parents
    _ ≤ _ := all_rank_finite_grid_energy_budget hε rank hRank index shift channel count A₀ hSelect

/-- Actual original real edge discrepancies of finite parent cells obey the
same reciprocal-width budget, with the entire parent count handled by the
translated lattice sums. -/
theorem edge_actual_original_discrepancy_budget {n q : ℕ} {G I J : Type*}
    [AddGroup G] [Fintype I] {ε : ℝ} (hε : 0 < ε)
    {z₀ : Domain (n + 2)} {R : ℝ} (direction : J → Fin (n + 2))
    (origin : G → Domain (n + 2)) (w : Fin 2 → Domain (n + 2) → Ambient q)
    (count : ℕ) (index : I → J) (shift : I → G) (parents : Finset G) :
    let Draw := (ball z₀ R).indicator (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let C := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let A := fun (j : J) (z : G) (s : ℝ) => origin z + s • EuclideanSpace.single (direction j) (1 : ℝ)
    let channel := fun j z => ∫⁻ t in C, Draw (A j z (t 0))
    let D₀ := ENNReal.ofReal (∫ x in ball z₀ R, ‖w 0 x - w 1 x‖ ^ 2)
    (∀ j, (∑' z : G, channel j z) ≤ 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
      ((count : ℝ≥0∞) * ENNReal.ofReal ε) * D₀) →
    (∀ z ∈ parents, ∀ i : I, ∀ s ∈ Ioo (0 : ℝ) ε, A (index i) (z + shift i) s ∈ ball z₀ R) →
    (∑ z ∈ parents, ∑ i : I, ENNReal.ofReal (ε ^ n) * ENNReal.ofReal
      (∫ s in Ioo (0 : ℝ) ε, ‖w 0 (A (index i) (z + shift i) s) -
        w 1 (A (index i) (z + shift i) s)‖ ^ 2)) ≤
      2 * (count : ℝ≥0∞) * (Fintype.card I : ℝ≥0∞) * (ENNReal.ofReal ε)⁻¹ * D₀ := by
  intro Draw C A channel D₀ hSelect hContained
  have hNative (z : G) (hz : z ∈ parents) (i : I) : ENNReal.ofReal
      (∫ s in Ioo (0 : ℝ) ε, ‖w 0 (A (index i) (z + shift i) s) -
        w 1 (A (index i) (z + shift i) s)‖ ^ 2) ≤ channel (index i) (z + shift i) := by
    calc
      _ ≤ ∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal
          (‖w 0 (A (index i) (z + shift i) s) - w 1 (A (index i) (z + shift i) s)‖ ^ 2) :=
        ofReal_nonnegative_integral_le_lintegral _ (fun _ => sq_nonneg _)
      _ ≤ _ := lintegral_real_edge_le_native_channel (origin (z + shift i)) (direction (index i)) Draw _ (by
        intro s hs
        dsimp only [Draw, A]
        rw [Set.indicator_of_mem (hContained z hz i s hs)])
  calc
    _ ≤ ∑ z ∈ parents, ∑ i : I,
        ENNReal.ofReal (ε ^ n) * channel (index i) (z + shift i) := by
      apply Finset.sum_le_sum
      intro z hz
      exact Finset.sum_le_sum fun i _ => mul_le_mul_right (hNative z hz i) _
    _ ≤ ∑' z : G, ∑ i : I,
        ENNReal.ofReal (ε ^ n) * channel (index i) (z + shift i) := ENNReal.sum_le_tsum parents
    _ ≤ _ := edge_finite_grid_discrepancy_budget hε index shift channel count D₀ hSelect

end StratificationTheory
