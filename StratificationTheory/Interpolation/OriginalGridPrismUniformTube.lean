module
public import StratificationTheory.Interpolation.OriginalGridUniformEdgeTube
public import StratificationTheory.Foundation.PrismTubeUniformRecurrence
public import StratificationTheory.Foundation.OriginalGridFrozenTubePowers
public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier
public import StratificationTheory.Foundation.GridCubeBallContainment

/-!
# Frozen tube powers for actual original physical prism cells

One selected original grid controls every positive-rank tube supplied by
the actual cell recursion. The physical cell carrier itself supplies the
original lattice witness and the line containment inside the source ball.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Actual original rank-one tubes and their genuine finite-facet recursion
inherit the frozen ambient powers on the same selected physical grid. -/
theorem original_selected_grid_prism_tubes_le_frozen_powers {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε : ℝ} (hε : 0 < ε) (count : ℕ) (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _ : Fin (n + 2) => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let C := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Eline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Eraw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let Dline := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Draw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((count : ℝ≥0∞) * ENNReal.ofReal ε)
    (∀ k, (∑' z : L, Eline k z) ≤ c * ENNReal.ofReal A₀) →
    (∀ k, (∑' z : L, Dline k z) ≤ c * ENNReal.ofReal D₀) →
    let Cell : ℕ → Type := fun r =>
      {p : originalPhysicalCellCarrier r grid offset ε // StrictMono (p.val.1 : Fin r → Fin (n + 2))}
    let origin := fun (r : ℕ) (p : Cell r) => p.val.val.2
    let normal := fun (p : Cell 1) => p.val.val.1 (0 : Fin 1)
    let edgeA := fun p : Cell 1 => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (origin 1 p + s • EuclideanSpace.single (normal p) (1 : ℝ)) (normal p)‖ ^ 2 +
        ‖Dw 1 (origin 1 p + s • EuclideanSpace.single (normal p) (1 : ℝ)) (normal p)‖ ^ 2
    let edgeD := fun p : Cell 1 => ∫ s in Ioo (0 : ℝ) ε,
      ‖w 0 (origin 1 p + s • EuclideanSpace.single (normal p) (1 : ℝ)) -
        w 1 (origin 1 p + s • EuclideanSpace.single (normal p) (1 : ℝ))‖ ^ 2
    ∀ (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (Tube : (r : ℕ) → Cell r → ℝ),
      (∀ p : Cell 1, Tube 1 p ≤ edgeD p / ε + Real.sqrt (2 * edgeD p * edgeA p)) →
      (∀ (r : ℕ) (p : Cell (r + 2)), Tube (r + 2) p ≤
        ∑ i : Fin (r + 2), ∑ side : Bool, Tube (r + 1) (child (r + 1) p i side)) →
      ∀ (r : ℕ) (p : Cell (r + 1)), Tube (r + 1) p ≤
        ((2 : ℝ) ^ r * ((r + 1).factorial : ℝ)) *
          ((4 * (count : ℝ)) * ε ^ ((1 : ℤ) - (n + 2 : ℕ)) * Real.sqrt A₀ * Real.sqrt D₀ +
            (4 * (count : ℝ)) * ε ^ (-((n + 2 : ℕ) : ℤ)) * D₀) := by
  intro grid L y C Eraw Draw Eline Dline A₀ D₀ c hSelectE hSelectD Cell origin normal edgeA edgeD
    child Tube hBase hStep
  let Bglobal : ℝ := c.toReal * (D₀ / ε + Real.sqrt (2 * D₀ * A₀))
  have hBaseGlobal (p : Cell 1) : Tube 1 p ≤ Bglobal := by
    obtain ⟨z, hCell, hOrigin⟩ := p.val.property
    have hOrigin' : y z = origin 1 p := hOrigin
    have hClosed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) ε) : ∀ j,
        (origin 1 p + s • EuclideanSpace.single (normal p) (1 : ℝ)) j ∈ Ioo (-1 : ℝ) 1 := by
      have h := hCell (EuclideanSpace.single (0 : Fin 1) s)
        (fun k => by have hk : k = 0 := Subsingleton.elim _ _; simpa only [hk, PiLp.single_apply, ite_true] using hs)
      simpa only [Fin.sum_univ_one, PiLp.single_apply, ite_true, hOrigin] using h
    have hImage : ∀ s ∈ Ioo (0 : ℝ) ε,
        y z + s • EuclideanSpace.single (normal p) (1 : ℝ) ∈
          ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by
      intro s hs
      rw [hOrigin', mem_ball_zero_iff]
      have hUnit := hClosed s ⟨hs.1.le, hs.2.le⟩
      have hn := euclidean_norm_le_dim_of_coordinate_bound
        (origin 1 p + s • EuclideanSpace.single (normal p) (1 : ℝ))
        (fun j => abs_le.mpr ⟨(hUnit j).1.le, (hUnit j).2.le⟩)
      push_cast at hn
      linarith
    have hRaw := original_selected_grid_uniform_raw_edge_tube w Dw hε count offset
      hSelectE hSelectD z (normal p) hImage
    have hLocal : edgeD p / ε + Real.sqrt (2 * edgeD p * edgeA p) ≤ Bglobal := by
      simpa only [edgeD, edgeA, Bglobal, hOrigin] using hRaw
    exact (hBase p).trans hLocal
  have hUniform := prism_tube_uniform_recurrence child Tube Bglobal hBaseGlobal hStep
  have hD₀ : 0 ≤ D₀ := integral_nonneg fun _ => sq_nonneg _
  have hFrozen := original_grid_global_tube_le_frozen_powers (n := n) (A := A₀) hε hD₀ count
  intro r p
  exact (hUniform r p).trans (mul_le_mul_of_nonneg_left hFrozen (by positivity))

end StratificationTheory
