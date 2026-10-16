module

public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier
public import StratificationTheory.Foundation.GridNeighborCoordinates
public import StratificationTheory.Foundation.UniformGridCarriers

public section

open HarmonicMaps Set Module MeasureTheory
open scoped BigOperators ENNReal

namespace StratificationTheory

/-- A finite translated positive mesh in the original selected integer
lattice, with its actual physical coordinate formula and no new offset. -/
theorem selected_grid_finite_mesh_frame {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (offset : Fin N → ℝ) (hOffset : ∀ j, offset j ∈ Ico (0 : ℝ) ε) :
    let grid := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _ : Fin N => ε) (fun _ => hε.ne'.isUnit)
    let L := Submodule.span ℤ (Set.range grid)
    ∃ K : ℕ, 2 < (K : ℝ) * ε ∧
      let M := 2 * K + 1
      let a : Domain N := WithLp.toLp 2 (fun j => offset j - (K : ℝ) * ε)
      ∃ node : (Fin N → Fin M) → L,
        (∀ α j, (node α : Fin N → ℝ) j =
          ((α j).val : ℝ) * ε - (K : ℝ) * ε) ∧
        Function.Injective node ∧
        (∀ α, WithLp.toLp 2 ((node α : Fin N → ℝ) + offset) =
          a + WithLp.toLp 2 (fun j => ((α j).val : ℝ) * ε)) ∧
        (∀ x : Domain N, (∀ j, |x j| < (3 / 4 : ℝ)) →
          x - a ∈ (uniformGridBox N M ε).val) := by
  intro grid L
  classical
  obtain ⟨K, hK⟩ := exists_nat_gt ((2 + ε) / ε)
  have hKε : (2 + ε : ℝ) < (K : ℝ) * ε := (div_lt_iff₀ hε).mp hK
  refine ⟨K, by linarith, ?_⟩
  dsimp only
  let step (j : Fin N) : L := ⟨grid j, Submodule.subset_span ⟨j, rfl⟩⟩
  let node (α : Fin N → Fin (2 * K + 1)) : L :=
    ∑ j : Fin N, (((α j).val : ℤ) - (K : ℤ)) • step j
  have hCoord (α : Fin N → Fin (2 * K + 1)) (j : Fin N) :
      (node α : Fin N → ℝ) j = ((α j).val : ℝ) * ε - (K : ℝ) * ε := by
    simp [node, step, grid, Basis.isUnitSMul_apply, Pi.basisFun_apply,
      Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, Pi.single_apply, sub_mul]
    rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro b hb hbj
      simp [Ne.symm hbj]
    · simp
  refine ⟨node, hCoord, ?_, ?_, ?_⟩
  · intro α β h
    funext j
    apply Fin.ext
    have hj := congrArg (fun z : L => (z : Fin N → ℝ) j) h
    rw [hCoord, hCoord] at hj
    have hv : ((α j).val : ℝ) = ((β j).val : ℝ) := by nlinarith
    exact_mod_cast hv
  · intro α
    ext j
    change (node α : Fin N → ℝ) j + offset j =
      (offset j - (K : ℝ) * ε) + ((α j).val : ℝ) * ε
    rw [hCoord]
    ring
  · intro x hx
    rw [mem_uniformGridBox_iff]
    intro j
    change x j - (offset j - (K : ℝ) * ε) ∈ Ioo 0 (((2 * K + 1 : ℕ) : ℝ) * ε)
    have hj := hx j
    have ho := hOffset j
    have hAbs := abs_lt.mp hj
    constructor
    · linarith [ho.2, hAbs.1]
    · push_cast
      nlinarith [ho.1, hAbs.2]

/-- A mesh cell meeting the inner cube has its entire closed cell in the
original open unit cube. -/
theorem selected_grid_active_closed_cell_contained {N : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < (1 / 8 : ℝ)) (y : Domain N)
    (hActive : ∃ x : Domain N, (∀ j, |x j| < (3 / 4 : ℝ)) ∧
      ∀ j, x j ∈ Icc (y j) (y j + ε)) :
    ∀ t : Domain N, (∀ j, t j ∈ Icc (0 : ℝ) ε) →
      ∀ j, (y + t) j ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨x, hx, hCell⟩ := hActive
  intro t ht j
  have ha := abs_lt.mp (hx j)
  have hb := hCell j
  have hc := ht j
  change y j + t j ∈ Ioo (-1 : ℝ) 1
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

end StratificationTheory
