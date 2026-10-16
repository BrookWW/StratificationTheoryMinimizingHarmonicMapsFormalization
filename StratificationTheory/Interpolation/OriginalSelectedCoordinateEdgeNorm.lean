module
public import StratificationTheory.Foundation.CoordinateEdgeUnitNorm
public import StratificationTheory.Foundation.CoordinateNormalLineGeometry
public import StratificationTheory.Foundation.CoordinateGridCompatibility
public import StratificationTheory.Foundation.TwoCoordinateSquareGeometry
public import StratificationTheory.Foundation.GridNeighborCoordinates

/-!
# The original norm bound on a selected-lattice edge connector

The original selected ACL event supplies closed-target line values that
bound the literal connector on the whole closed unit square.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- One fixed original selected ACL event preserves the original target
norm bound on the whole literal closed unit-square connector. -/
theorem original_selected_coordinate_edge_norm {n q : ℕ}
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    {N : Set (Ambient q)}
    {ε : ℝ} (hε : 0 < ε) (offset : Fin (n + 1) → ℝ)
    (normal : Fin (n + 1)) :
    let p := Equiv.swap (Fin.last n) normal
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := fun y => (e₀ (Q.symm y)).1
    let rep := fun l => coordinatePermACLRepresentative p (-1) 1 (u l) (Du l)
    let line := fun x t => Q (e₀.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let S : Set (Domain n) := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω := {y : Domain (n + 1) | β y ∈ S ∧ (e₀ (Q.symm y)).2 0 ∈ Ioo (-1 : ℝ) 1}
    let L := fun (l : Fin 2) (y : Domain (n + 1)) => y ∈ Ω →
      rep l y = u l y ∧
      MemLp (fun t => u l (line (β y) t)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      MemLp (fun t => Du l (line (β y) t) j) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      AbsolutelyContinuousOnInterval (fun t => rep l (line (β y) t)) (-1) 1 ∧
      (fun t => rep l (line (β y) t)) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
        (fun t => u l (line (β y) t)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, rep l (line (β y) t) ∈ N) ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
        rep l (line (β y) t) - rep l (line (β y) s) = ∫ r in s..t, Du l (line (β y) r) j
    let grid := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _ : Fin (n + 1) => ε) (fun _ => hε.ne'.isUnit)
    (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2),
      L l (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) →
    ∀ z : Submodule.span ℤ (Set.range grid),
    let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
    (∀ s ∈ Icc (0 : ℝ) ε, ∀ i, (y + s • v) i ∈ Ioo (-1 : ℝ) 1) →
    ∀ M : ℝ, (∀ v ∈ N, ‖v‖ ≤ M) → ∀ x : Domain 2,
      (∀ i, x i ∈ Icc (-1 : ℝ) 1) →
        ‖coordinateEdgeUnitMap p (-1) 1 ε u Du y x‖ ≤ M := by
  intro p Q e₀ j v β rep line S Ω L grid hACL z y hCell
  have hNormal : j = normal := Equiv.swap_apply_left _ _
  have hΩ (x : Domain (n + 1)) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) : x ∈ Ω := by
    constructor
    · apply mem_iInter.mpr
      intro i
      change (e₀ (Q.symm x)).1 i ∈ Ioo (-1 : ℝ) 1
      rw [coordinate_split_first_eq]
      exact hx _
    · rw [coordinate_split_last_eq]
      exact hx _
  have hStartUnit : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := by
    simpa only [zero_smul, add_zero] using hCell 0 ⟨le_rfl, hε.le⟩
  have hSource (l : Fin 2) := hACL z l (hΩ y hStartUnit)
  have ha : (-1 : ℝ) ≤ y j := (hStartUnit j).1.le
  have hb : y j + ε ≤ (1 : ℝ) := by
    have h := (hCell ε ⟨hε.le, le_rfl⟩ j).2.le
    simpa only [v, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, mul_one] using h
  intro M hM x hx
  exact coordinateEdgeUnitMap_norm_le_of_original_line_values p y (-1) 1 ε hε u Du
    ha hb (fun l => (hSource l).2.2.2.2.2.1) hM x hx

end StratificationTheory
