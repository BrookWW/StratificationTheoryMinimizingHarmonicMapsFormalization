module
public import StratificationTheory.Interpolation.CoordinateEdgeUnitMaps
public import StratificationTheory.Foundation.CoordinateNormalLineGeometry

/-!
# The original target norm bound on the actual unit edge connector

The closed-target original line representatives and their original norm
bound control the literal affine connector on the whole closed square.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The whole unit connector retains the original common norm bound. -/
theorem coordinateEdgeUnitMap_norm_le_of_original_line_values {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (y : Domain (n + 1))
    (a b ε : ℝ) (hε : 0 < ε)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    {N : Set (Ambient q)} {M : ℝ} :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let β := (e (Q.symm y)).1
    let line := fun t => Q (e.symm (β, EuclideanSpace.single (0 : Fin 1) t))
    let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
    a ≤ y j → y j + ε ≤ b →
    (∀ l t, t ∈ Icc a b → rep l (line t) ∈ N) →
    (∀ v ∈ N, ‖v‖ ≤ M) → ∀ z : Domain 2,
      (∀ k, z k ∈ Icc (-1 : ℝ) 1) → ‖coordinateEdgeUnitMap p a b ε u Du y z‖ ≤ M := by
  intro Q e j β line rep ha hb hValues hM z hz
  let s : ℝ := ε / 2 + (ε / 2) * z 0
  let θ : ℝ := (z 1 + 1) / 2
  have hs : s ∈ Icc (0 : ℝ) ε := by
    constructor <;> dsimp only [s] <;> nlinarith [hz 0 |>.1, hz 0 |>.2]
  have hθ : 0 ≤ θ ∧ θ ≤ 1 := by
    constructor <;> dsimp only [θ] <;> linarith [hz 1 |>.1, hz 1 |>.2]
  have hline : line (y j + s) = y + s • EuclideanSpace.single j (1 : ℝ) := by
    simpa only [line, j, add_sub_cancel_left] using coordinate_line_eq_add_normal p y (y j + s)
  have hBound (l : Fin 2) : ‖rep l (y + s • EuclideanSpace.single j (1 : ℝ))‖ ≤ M := by
    rw [← hline]
    exact hM _ (hValues l (y j + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hcoef : (ε / 2 + (ε / 2) * z 1) / ε = θ := by
    dsimp only [θ]
    field_simp [hε.ne']
    ring
  have hMap : coordinateEdgeUnitMap p a b ε u Du y z =
      (1 - θ) • rep 0 (y + s • EuclideanSpace.single j (1 : ℝ)) +
        θ • rep 1 (y + s • EuclideanSpace.single j (1 : ℝ)) := by
    change (1 - (ε / 2 + (ε / 2) * z 1) / ε) •
        rep 0 (y + s • EuclideanSpace.single j (1 : ℝ)) +
        ((ε / 2 + (ε / 2) * z 1) / ε) • rep 1 (y + s • EuclideanSpace.single j (1 : ℝ)) = _
    rw [hcoef]
  rw [hMap]
  calc
    _ ≤ ‖(1 - θ) • rep 0 (y + s • EuclideanSpace.single j (1 : ℝ))‖ +
        ‖θ • rep 1 (y + s • EuclideanSpace.single j (1 : ℝ))‖ := norm_add_le _ _
    _ = (1 - θ) * ‖rep 0 (y + s • EuclideanSpace.single j (1 : ℝ))‖ +
        θ * ‖rep 1 (y + s • EuclideanSpace.single j (1 : ℝ))‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hθ.2), abs_of_nonneg hθ.1]
    _ ≤ (1 - θ) * M + θ * M :=
      add_le_add (mul_le_mul_of_nonneg_left (hBound 0) (sub_nonneg.mpr hθ.2))
        (mul_le_mul_of_nonneg_left (hBound 1) hθ.1)
    _ = M := by ring

end StratificationTheory
