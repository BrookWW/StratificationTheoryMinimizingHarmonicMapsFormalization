module

public import HarmonicMaps.Sobolev

public section

open HarmonicMaps
open scoped BigOperators

namespace StratificationTheory

/-- Each original selected coordinate recovers exactly its own affine cell
parameter; other embedded coordinates contribute zero. -/
theorem coordinate_cell_affine_parameter_coordinate {k N : ℕ}
    (c : Fin k ↪ Fin N) (y : Domain N) (a h : ℝ) (t : Domain k) (j : Fin k) :
    (y + ∑ s : Fin k, (a + h * t s) • EuclideanSpace.single (c s) (1 : ℝ)) (c j) =
      y (c j) + a + h * t j := by
  have hSum : (∑ s : Fin k, (a + h * t s) • EuclideanSpace.single (c s) (1 : ℝ)) (c j) =
      a + h * t j := by
    rw [show (∑ s : Fin k, (a + h * t s) • EuclideanSpace.single (c s) (1 : ℝ)) (c j) =
      ∑ s : Fin k, ((a + h * t s) • EuclideanSpace.single (c s) (1 : ℝ)) (c j) by
        exact map_sum (EuclideanSpace.proj (c j)) _ _]
    rw [Finset.sum_eq_single j]
    · simp
    · intro s _ hsj
      have hc : c s ≠ c j := fun h => hsj (c.injective h)
      simp [hc]
    · simp
  calc
    _ = y (c j) + (∑ s : Fin k, (a + h * t s) • EuclideanSpace.single (c s) (1 : ℝ)) (c j) :=
      map_add (EuclideanSpace.proj (c j)) _ _
    _ = _ := by rw [hSum]; ring

/-- An actual nondegenerate affine coordinate cell has unique native
parameters, in every rank and ambient dimension. -/
theorem coordinate_cell_affine_parameter_injective {k N : ℕ}
    (c : Fin k ↪ Fin N) (y : Domain N) (a h : ℝ) (hh : h ≠ 0) :
    Function.Injective (fun t : Domain k =>
      y + ∑ s : Fin k, (a + h * t s) • EuclideanSpace.single (c s) (1 : ℝ)) := by
  intro t u hSame
  ext j
  have hj := congrArg (fun v : Domain N => v (c j)) hSame
  rw [coordinate_cell_affine_parameter_coordinate,
    coordinate_cell_affine_parameter_coordinate] at hj
  exact (mul_left_cancel₀ hh) (by linarith : h * t j = h * u j)

/-- The original spatial cell and independently scaled time together
recover the entire native lower-prism parameter from a physical point. -/
theorem coordinate_prism_affine_parameter_injective {k N : ℕ}
    (c : Fin k ↪ Fin N) (y : Domain N) (a h : ℝ) (hh : h ≠ 0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1)
    Function.Injective (fun z : Domain (k + 1) => E.symm
      (y + ∑ s : Fin k, (a + h * (e z).1 s) • EuclideanSpace.single (c s) (1 : ℝ),
        EuclideanSpace.single (0 : Fin 1) (a + h * (e z).2 0))) := by
  intro e E z v hSame
  have hPair := E.symm.injective hSame
  apply e.injective
  apply Prod.ext
  · exact coordinate_cell_affine_parameter_injective c y a h hh (congrArg Prod.fst hPair)
  · ext j
    have hj := congrArg (fun p : Domain N × Domain 1 => p.2 0) hPair
    have hj0 : a + h * (e z).2 0 = a + h * (e v).2 0 := by simpa using hj
    have heq : (e z).2 0 = (e v).2 0 :=
      (mul_left_cancel₀ hh) (by linarith : h * (e z).2 0 = h * (e v).2 0)
    simpa only [Subsingleton.elim j (0 : Fin 1)] using heq

end StratificationTheory
