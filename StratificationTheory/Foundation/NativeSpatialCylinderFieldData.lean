module

public import StratificationTheory.Foundation.NativeSpatialCylinderColumns

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- The original selected spatial cut columns supply the same literal
native field with its original radial and temporal coherence, tangency and energy. -/
theorem native_spatial_cylinder_field_data {n q : ℕ} {a b : ℝ}
    (r : ℝ) (DV : Domain (n + 1) → Gradient (n + 1) q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    let X : unitCylinder n a b → Domain (n + 1) := fun c => e.symm (r • (e c.val).1, (e c.val).2)
    let F : Domain (n + 1) → Domain (n + 1) := fun y => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
    let DG : Domain (n + 1) → Gradient (n + 1) q := fun y i => ∑ j : Fin (n + 1),
      (fderiv ℝ F y (EuclideanSpace.single i 1)) j • DV (F y) j
    let g : unitCylinder n a b → Gradient (n + 1) q := fun c => Fin.addCases
      (fun i : Fin n => r • tangentialColumns ⟨(e c.val).1, c.property.1⟩
        (fun j => DV (X c) (Fin.castAdd 1 j)) i)
      (fun _ : Fin 1 => DV (X c) (Fin.natAdd n (0 : Fin 1)))
    (∀ i : Fin (n + 1), MemLp (fun c => DV (X c) i) 2 μ) →
    (∀ᵐ ρ ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      ∀ᵐ c : unitCylinder n a b ∂μ, (e c.val).2 0 ∈ Ioo a b →
        (∀ i : Fin n, DG (e.symm (ρ • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
          ρ⁻¹ • g c (Fin.castAdd 1 i)) ∧
        DG (e.symm (ρ • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
          g c (Fin.natAdd n (0 : Fin 1))) ∧
    (∀ i : Fin (n + 1), MemLp (fun c => g c i) 2 μ) ∧
    (∀ᵐ c : unitCylinder n a b ∂μ,
      (∑ i : Fin n, (e c.val).1 i • g c (Fin.castAdd 1 i)) = 0) ∧
    Integrable (fun c => hsNormSq (g c)) μ ∧
    (|r| ≤ 1 → (∫ c, hsNormSq (g c) ∂μ) ≤ ∫ c, hsNormSq (DV (X c)) ∂μ) := by
  intro e μ X F DG g hCols
  have hFields := native_spatial_radial_chain_columns (a := a) (b := b) r DV
  obtain ⟨hgLp, hgTangent, hgInt, hgEnergy⟩ :=
    native_spatial_projected_column_data (a := a) (b := b) r DV hCols
  refine ⟨?_, hgLp, Eventually.of_forall hgTangent, hgInt, fun hr => (hgEnergy hr).2⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
  exact Eventually.of_forall fun (c : unitCylinder n a b) (_ht : (e c.val).2 0 ∈ Ioo a b) =>
    hFields ρ (by linarith [hρ.1]) c

end StratificationTheory
