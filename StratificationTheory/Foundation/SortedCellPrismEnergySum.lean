module
public import StratificationTheory.Foundation.SortedCellFacetEnergyIncidence

/-!
# Summed physical energy recursion on actual sorted cells

The actual cellwise energy inequality sums over the full original cell
family. Facet incidence introduces only twice the ambient dimension and
preserves every original horizontal energy term.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- A genuine physical real energy inequality converts to its nonnegative
extended-real form with the same finite original facet terms. -/
theorem ofReal_finite_prism_energy_bound {I : Type*} [Fintype I]
    {E C H : ℝ} (lower : I → ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hLower : ∀ i, 0 ≤ lower i) (hE : E ≤ C * (H + ∑ i, lower i)) :
    ENNReal.ofReal E ≤ ENNReal.ofReal C *
      (ENNReal.ofReal H + ∑ i, ENNReal.ofReal (lower i)) := by
  apply (ENNReal.ofReal_le_ofReal hE).trans_eq
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add hH (Finset.sum_nonneg fun i _ => hLower i),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hLower i)]

/-- The genuine cellwise prism energy recursion has a global summed
recursion with the actual finite ambient incidence and every horizontal term. -/
theorem tsum_sorted_physical_prism_energy_recurrence {k N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ) (ε : ℝ) :
    let Cell := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (p.val.1 : Fin r → Fin N)}
    ∀ child : Cell (k + 1) → Fin (k + 1) → Bool → Cell k,
    (∀ p i side, (child p i side).val.val.1 = i.succAboveEmb.trans p.val.val.1) →
    (∀ p i side, (child p i side).val.val.2 =
      p.val.val.2 + (if side then ε else 0) • EuclideanSpace.single (p.val.val.1 i) (1 : ℝ)) →
    ∀ (E H : Cell (k + 1) → ℝ≥0∞) (lower : Cell k → ℝ≥0∞) (C : ℝ≥0∞),
      (∀ p, E p ≤ C * (H p + ∑ i : Fin (k + 1), ∑ side : Bool, lower (child p i side))) →
      (∑' p : Cell (k + 1), E p) ≤ C *
        ((∑' p : Cell (k + 1), H p) + (2 * (N : ℝ≥0∞)) * ∑' p : Cell k, lower p) := by
  intro Cell child hAxes hOrigin E H lower C hStep
  have hInc := tsum_sorted_physical_cell_facet_energy_le grid offset ε child hAxes hOrigin lower
  calc
    _ ≤ ∑' p : Cell (k + 1), C * (H p + ∑ i : Fin (k + 1), ∑ side : Bool, lower (child p i side)) :=
      ENNReal.tsum_le_tsum hStep
    _ = C * ((∑' p : Cell (k + 1), H p) +
        ∑' p : Cell (k + 1), ∑ i : Fin (k + 1), ∑ side : Bool, lower (child p i side)) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ _ := by gcongr

/-- A cone factor at most three and the actual twice-ambient incidence
fit one dimension-only scalar recurrence coefficient. -/
theorem uniform_prism_total_energy_branch_bound {N : ℕ} {f h H P : ℝ}
    (hf : f ≤ 3) (hh : 0 ≤ h) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    f * h * (H + 2 * (N : ℝ) * P) ≤
      (6 * ((N : ℝ) + 1)) * h * (H + P) := by
  have hNonneg : 0 ≤ h * (H + 2 * (N : ℝ) * P) := by positivity
  have hFactor := mul_le_mul_of_nonneg_right hf hNonneg
  have hDifference : 0 ≤ (6 * (N : ℝ) + 3) * h * H + 6 * h * P := by positivity
  nlinarith

end StratificationTheory
