module
public import StratificationTheory.Foundation.OriginalPhysicalCellEnergySum

/-!
# Summed original paired real-line energies of physical edges

Actual contained sorted grid edges inject into their original direction
and lattice vertex. Their paired real-line gradient energies are bounded
by the same original selected ambient Hilbert--Schmidt channels.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The paired real-line energies used by the actual edge connector are
summably bounded by the original native global coordinate-line channels. -/
theorem original_physical_cell_line_energy_tsum_le_native_channels {n q : ℕ}
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε : ℝ} (hε : 0 < ε) (count : ℕ) (offset : Fin (n + 2) → ℝ) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _ : Fin (n + 2) => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    let y := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let C := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let channel := fun (coord : Fin 1 ↪ Fin (n + 2)) (z : L) =>
      ∫⁻ t in C, Eraw (y z + t 0 • EuclideanSpace.single (coord 0) (1 : ℝ))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let c := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
      ((count : ℝ≥0∞) * ENNReal.ofReal ε) * ENNReal.ofReal A₀
    (∀ coord, (∑' z : L, channel coord z) ≤ c) →
    let Cell := {p : originalPhysicalCellCarrier 1 grid offset ε //
      StrictMono (p.val.1 : Fin 1 → Fin (n + 2))}
    let A := fun p : Cell => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (p.val.val.2 + s • EuclideanSpace.single (p.val.val.1 0) (1 : ℝ)) (p.val.val.1 0)‖ ^ 2 +
        ‖Dw 1 (p.val.val.2 + s • EuclideanSpace.single (p.val.val.1 0) (1 : ℝ)) (p.val.val.1 0)‖ ^ 2
    (∑' p : Cell, ENNReal.ofReal (A p)) ≤ (Fintype.card (Fin 1 ↪ Fin (n + 2)) : ℝ≥0∞) * c := by
  classical
  intro grid L y C Eraw channel A₀ c hSelect Cell A
  have hWitness (p : Cell) : ∃ z : L,
      (p.val.val.1, z) ∈ originalCoordinateCellCarrier 1 grid offset ε ∧ y z = p.val.val.2 :=
    p.val.property
  choose z hContained hOrigin using hWitness
  let index : Cell → (Fin 1 ↪ Fin (n + 2)) × L := fun p => (p.val.val.1, z p)
  have hIndex : Function.Injective index := by
    intro p q h
    have hAxes : p.val.val.1 = q.val.val.1 := congrArg (fun a : (Fin 1 ↪ Fin (n + 2)) × L => a.1) h
    have hGrid : z p = z q := congrArg (fun a : (Fin 1 ↪ Fin (n + 2)) × L => a.2) h
    have hOrigins : p.val.val.2 = q.val.val.2 :=
      (hOrigin p).symm.trans ((congrArg y hGrid).trans (hOrigin q))
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hAxes hOrigins
  have hImage (p : Cell) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ε) :
      y (z p) + s • EuclideanSpace.single (p.val.val.1 0) (1 : ℝ) ∈
        ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by
    have hUnit := hContained p (EuclideanSpace.single (0 : Fin 1) s)
      (fun k => by have hk : k = 0 := Subsingleton.elim _ _; simpa only [hk, PiLp.single_apply, ite_true] using (show s ∈ Icc (0 : ℝ) ε from ⟨hs.1.le, hs.2.le⟩))
    simp only [Fin.sum_univ_one, PiLp.single_apply, ite_true] at hUnit
    rw [mem_ball_zero_iff]
    have hn := euclidean_norm_le_dim_of_coordinate_bound
      (y (z p) + s • EuclideanSpace.single (p.val.val.1 0) (1 : ℝ))
      (fun j => abs_le.mpr ⟨(hUnit j).1.le, (hUnit j).2.le⟩)
    push_cast at hn
    linarith
  have hNative (p : Cell) : ENNReal.ofReal (A p) ≤ channel p.val.val.1 (z p) := by
    have h := original_real_edge_combined_energy_le_native_channel
      (y (z p)) (p.val.val.1 0) Dw (hImage p)
    simpa only [A, channel, hOrigin p] using h
  calc
    _ ≤ ∑' p : Cell, channel p.val.val.1 (z p) := ENNReal.tsum_le_tsum hNative
    _ ≤ ∑' a : (Fin 1 ↪ Fin (n + 2)) × L, channel a.1 a.2 :=
      ENNReal.tsum_comp_le_tsum_of_injective hIndex (fun a => channel a.1 a.2)
    _ = ∑' coord : Fin 1 ↪ Fin (n + 2), ∑' z : L, channel coord z := ENNReal.tsum_prod
    _ ≤ ∑' _coord : Fin 1 ↪ Fin (n + 2), c := ENNReal.tsum_le_tsum hSelect
    _ = _ := by simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end StratificationTheory
