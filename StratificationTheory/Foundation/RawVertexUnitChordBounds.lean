module
public import StratificationTheory.Foundation.RawVertexUnitChordData

/-!
# Bounds for the actual raw vertex chord

The original endpoint norms bound the whole chord. A target-valued original
endpoint controls its actual distance to the target on the closed interval.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- A bound for both original values bounds every closed unit-time value. -/
theorem rawVertexUnitChord_norm_le {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m) {M : ℝ}
    (hM : ∀ l, ‖u l y‖ ≤ M) (x : Domain 1) (hx : x 0 ∈ Icc (-1 : ℝ) 1) :
    ‖rawVertexUnitChord u y x‖ ≤ M := by
  have ha : 0 ≤ (x 0 + 1) / 2 := by linarith [hx.1]
  have hb : (x 0 + 1) / 2 ≤ 1 := by linarith [hx.2]
  calc
    ‖rawVertexUnitChord u y x‖ ≤ ‖(1 - (x 0 + 1) / 2) • u 0 y‖ +
        ‖((x 0 + 1) / 2) • u 1 y‖ := norm_add_le _ _
    _ = (1 - (x 0 + 1) / 2) * ‖u 0 y‖ + ((x 0 + 1) / 2) * ‖u 1 y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg ha]
    _ ≤ (1 - (x 0 + 1) / 2) * M + ((x 0 + 1) / 2) * M :=
      add_le_add (mul_le_mul_of_nonneg_left (hM 0) (sub_nonneg.mpr hb))
        (mul_le_mul_of_nonneg_left (hM 1) ha)
    _ = M := by ring

/-- The actual chord inherits a squared target-distance bound from its
original first target-valued endpoint. -/
theorem rawVertexUnitChord_infDist_sq_le {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m)
    {N : Set (Ambient q)} (h₀ : u 0 y ∈ N)
    (x : Domain 1) (hx : x 0 ∈ Icc (-1 : ℝ) 1) :
    (infDist (rawVertexUnitChord u y x) N) ^ 2 ≤ ‖u 0 y - u 1 y‖ ^ 2 := by
  have ha : 0 ≤ (x 0 + 1) / 2 := by linarith [hx.1]
  have hb : (x 0 + 1) / 2 ≤ 1 := by linarith [hx.2]
  have hdiff : rawVertexUnitChord u y x - u 0 y =
      ((x 0 + 1) / 2) • (u 1 y - u 0 y) := by
    unfold rawVertexUnitChord
    module
  have hle : infDist (rawVertexUnitChord u y x) N ≤ ‖u 1 y - u 0 y‖ := by
    calc
      _ ≤ dist (rawVertexUnitChord u y x) (u 0 y) := infDist_le_dist_of_mem h₀
      _ = ((x 0 + 1) / 2) * ‖u 1 y - u 0 y‖ := by
        rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      _ ≤ ‖u 1 y - u 0 y‖ := by
        nlinarith [norm_nonneg (u 1 y - u 0 y)]
  rw [norm_sub_rev (u 0 y) (u 1 y)]
  nlinarith [infDist_nonneg (x := rawVertexUnitChord u y x) (s := N), norm_nonneg (u 1 y - u 0 y)]

end StratificationTheory
