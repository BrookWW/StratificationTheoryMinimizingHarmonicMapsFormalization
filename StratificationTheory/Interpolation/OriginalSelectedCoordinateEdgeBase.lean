module
public import StratificationTheory.Interpolation.CoordinateEdgeCanonicalBase
public import StratificationTheory.Foundation.CoordinateNormalLineGeometry
public import StratificationTheory.Foundation.CoordinateGridCompatibility
public import StratificationTheory.Foundation.TwoCoordinateSquareGeometry
public import StratificationTheory.Foundation.GridNeighborCoordinates

/-!
# The original selected-lattice edge base

The original ACL event at two actual neighboring lattice vertices produces
one canonical edge connector with the shared global raw vertex chords.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- One fixed original selected ACL event supplies the actual canonical
edge-prism graph and all four original boundary classes. -/
theorem original_selected_coordinate_edge_base {n q : ℕ}
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    {N : Set (Ambient q)} (hN : IsClosed N)
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
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let B : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let C : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let edge := fun (l : Fin 2) (x : Domain 1) => u l (y + (ε / 2 + (ε / 2) * x 0) • v)
    let V := coordinateEdgeUnitMap p (-1) 1 ε u Du y
    let DV := coordinateEdgeUnitGradient p (-1) 1 ε u Du y
    let D := ∫ s in Ioo (0 : ℝ) ε, ‖u 0 (y + s • v) - u 1 (y + s • v)‖ ^ 2
    let E := ∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2 + ‖Du 1 (y + s • v) j‖ ^ 2
    let face := fun (i : Fin 2) (side : Bool) => if i = 0 then
      rawVertexUnitChord u (y + (if side then ε else 0) • v) else edge (if side then 1 else 0)
    MemW12 B V DV ∧
      (∫ z in B.val, hsNormSq (DV z)) ≤
        (ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2) +
          ∫ s in Ioo (0 : ℝ) ε, ‖Du 1 (y + s • v) j‖ ^ 2) + ε⁻¹ * D ∧
      (∀ z : Domain 2, (∀ j, z j ∈ Icc (-1 : ℝ) 1) →
        (infDist (V z) N) ^ 2 ≤ D / ε + Real.sqrt (2 * D * E)) ∧
      ∃ K : Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => V (cubicalSignedFaceIsometry 1 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
            K i ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp
              (fun x => V (cubicalSignedFaceIsometry 1 i true
                (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i side,
          (K i ⟨if side then 1 else -1, by cases side <;> norm_num,
            by cases side <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C] face i side := by
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
  obtain ⟨z', hz'⟩ := exists_scaled_grid_neighbor hε offset z normal
  have hzEnd : WithLp.toLp 2 ((z' : Fin (n + 1) → ℝ) + offset) = y + ε • v := by
    simpa only [v, hNormal] using hz'
  have hEndRaw (l : Fin 2) : rep l (y + ε • v) = u l (y + ε • v) := by
    have h := (hACL z' l (hΩ _ (by rw [hzEnd]; exact hCell ε ⟨hε.le, le_rfl⟩))).1
    simpa only [hzEnd] using h
  have ha : (-1 : ℝ) ≤ y j := (hStartUnit j).1.le
  have hb : y j + ε ≤ (1 : ℝ) := by
    have h := (hCell ε ⟨hε.le, le_rfl⟩ j).2.le
    simpa only [v, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, mul_one] using h
  with_reducible exact (coordinate_edge_canonical_base_of_original_line_data
    p y (-1) 1 ε hε u Du hN ha hb
    (fun l => (hSource l).2.1) (fun l => (hSource l).2.2.1)
    (fun l => (hSource l).2.2.2.2.1) (fun l => (hSource l).2.2.2.2.2.1)
    (fun l => (hSource l).2.2.2.2.2.2) (fun l => (hSource l).1) hEndRaw)

end StratificationTheory
