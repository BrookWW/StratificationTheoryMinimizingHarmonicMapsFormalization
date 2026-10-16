module

public import StratificationTheory.Foundation.CubicalThreeFacetIncidence

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- A single physical representative for the lower boundary of a
three-spatial-coordinate prism uses original source values on the two time
caps and the original global directional representatives on each open
spatial edge. Its six edge formulas retain the original free coordinate. -/
theorem three_coordinate_prism_boundary_formulas {N q : ℕ}
    (w : Fin 2 → Domain N → Ambient q)
    (rep : Fin 2 → Fin N → Domain N → Ambient q)
    (coord : Fin 3 ↪ Fin N) (ε : ℝ) (y : Domain N) :
    let P := fun z : Domain 3 => y + ∑ k : Fin 3,
      (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (coord k) (1 : ℝ)
    let free := fun z : Domain 3 => if |z 0| < 1 then (0 : Fin 3) else if |z 1| < 1 then 1 else 2
    let X := fun (z : Domain 3) (t : ℝ) => WithLp.toLp 2 ![z 0, z 1, z 2, t]
    let E := fun z : Domain 4 =>
      let sp : Domain 3 := WithLp.toLp 2 ![z 0, z 1, z 2]
      if z 3 = -1 then w 0 (P sp) else if z 3 = 1 then w 1 (P sp) else
        (1 - (z 3 + 1) / 2) • rep 0 (coord (free sp)) (P sp) +
          ((z 3 + 1) / 2) • rep 1 (coord (free sp)) (P sp)
    (∀ z : Domain 3, ∀ side : Bool,
      E (X z (if side then 1 else -1)) = w (if side then 1 else 0) (P z)) ∧
    ∀ (sideI sideJ : Bool) (x t : ℝ), x ∈ Ioo (-1 : ℝ) 1 → t ∈ Ioo (-1 : ℝ) 1 →
      let r : ℝ := if sideI then 1 else -1
      let s : ℝ := if sideJ then 1 else -1
      let A := fun k (z : Domain 3) =>
        (1 - (t + 1) / 2) • rep 0 (coord k) (P z) +
          ((t + 1) / 2) • rep 1 (coord k) (P z)
      E (X (WithLp.toLp 2 ![r, x, s]) t) = A 1 (WithLp.toLp 2 ![r, x, s]) ∧
      E (X (WithLp.toLp 2 ![r, s, x]) t) = A 2 (WithLp.toLp 2 ![r, s, x]) ∧
      E (X (WithLp.toLp 2 ![s, r, x]) t) = A 2 (WithLp.toLp 2 ![s, r, x]) ∧
      E (X (WithLp.toLp 2 ![x, r, s]) t) = A 0 (WithLp.toLp 2 ![x, r, s]) ∧
      E (X (WithLp.toLp 2 ![s, x, r]) t) = A 1 (WithLp.toLp 2 ![s, x, r]) ∧
      E (X (WithLp.toLp 2 ![x, s, r]) t) = A 0 (WithLp.toLp 2 ![x, s, r]) := by
  intro P free X E
  have hSpatial (z : Domain 3) (t : ℝ) :
      (WithLp.toLp 2 ![(X z t) 0, (X z t) 1, (X z t) 2] : Domain 3) = z := by
    ext k
    fin_cases k <;> rfl
  have hTime (z : Domain 3) (t : ℝ) : (X z t) 3 = t := rfl
  constructor
  · intro z side
    dsimp only [E]
    rw [hSpatial, hTime]
    cases side <;> norm_num
  · intro sideI sideJ x t hx ht r s A
    have hx' : |x| < 1 := abs_lt.mpr hx
    have ht₀ : t ≠ -1 := ne_of_gt ht.1
    have ht₁ : t ≠ 1 := ne_of_lt ht.2
    have hr : ¬ |r| < 1 := by cases sideI <;> norm_num [r]
    have hs : ¬ |s| < 1 := by cases sideJ <;> norm_num [s]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [E, X, free, A, hr, hs, hx', ht₀, ht₁]

end StratificationTheory
