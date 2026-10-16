module

public import StratificationTheory.Interpolation.AnnularRayCoherence
public import StratificationTheory.Foundation.AnnularColumnComparison
public import StratificationTheory.Foundation.CylinderNativeColumnSplit

/-!
# Energy comparison for the actual radially averaged columns

Original finite cylinder weak data, actual native L2 columns and radial
collar coherence determine the same averaged field. Its annular L2 membership
and energy comparison follow internally from measurable ray transport and
native column splitting. No annular energy bound or averaged-gradient formula
is an input.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal
namespace StratificationTheory

theorem annularAveragedColumns_energy_le_native_of_radial_coherence
    {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : MemW12 Ω w Dw)
    {δ a b s : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hab : a < b) (hs : 0 < s) (ha : -1 < a)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (1 - δ < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < 1 + δ) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    (A : sphere (0 : Domain n) 1 × ℝ → Gradient n q)
    (B : sphere (0 : Domain n) 1 × ℝ → Ambient q) (β : ℝ → ℝ)
    (hNative : ∀ i : Fin (n + 1), MemLp (fun c : unitCylinder n a b => Dw c.val i) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))) :
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let V := {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}
    let C := max (s * (1 + a))⁻¹ s⁻¹
    (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) = 1 →
    (∀ ρ : PositiveRadius, (1 - δ < ρ.val ∧ ρ.val < 1 + δ) →
      ∀ᵐ θ ∂σ, ∀ t ∈ Ioo a b,
      (∀ i : Fin n,
        Dw (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) (Fin.castAdd 1 i) =
          ρ.val⁻¹ • A (θ, t) i) ∧
      Dw (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t))
          (Fin.natAdd n (0 : Fin 1)) = B (θ, t)) →
    (∀ i : Fin n, MemLp (fun x => annularAveragedColumns s β P Dw x i) 2 (volume.restrict V)) ∧
      Integrable (fun x => hsNormSq (annularAveragedColumns s β P Dw x)) (volume.restrict V) ∧
      (∫ x in V, hsNormSq (annularAveragedColumns s β P Dw x)) ≤
        (s * (s * (1 + b)) ^ (n - 1)) * C ^ 2 *
          ∫ c : unitCylinder n a b, hsNormSq (Dw c.val) ∂Measure.euclideanHausdorffMeasure n := by
  intro σ η P e V C hmass hAll
  have hunit : ∀ᵐ θ : sphere (0 : Domain n) 1 ∂σ, ∀ t ∈ Ioo a b,
      Dw (e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
        Fin.addCases (A (θ, t)) (fun _ : Fin 1 => B (θ, t)) := by
    have hOne : 1 - δ < (1 : ℝ) ∧ (1 : ℝ) < 1 + δ := by
      constructor <;> linarith only [hδ]
    filter_upwards [hAll ⟨1, zero_lt_one⟩ hOne] with θ hθ
    intro t ht
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [one_smul, inv_one, Fin.addCases_left] using (hθ t ht).1 i
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simpa only [one_smul, Fin.addCases_right] using (hθ t ht).2
  obtain ⟨hA, hB, hEnergyAB⟩ := native_cylinder_split_columns_l2_and_energy hn Dw A B hNative hunit
  have hFormula := annularAveragedColumns_ae_of_radial_collar_coherence
    hn hw hδ hδsmall hs ha hΩ A B β hA hB hmass hAll
  have hCompare := annular_column_energy_le_of_native_formula
    hn hs ha hab (annularAveragedColumns s β P Dw) A B hA hB hFormula
  refine ⟨hCompare.1, hCompare.2.1, ?_⟩
  calc
    _ ≤ (s * (s * (1 + b)) ^ (n - 1)) * C ^ 2 *
        ∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (A p) + ‖B p‖ ^ 2
          ∂σ.prod (volume.restrict (Ioo a b)) := hCompare.2.2
    _ = _ := by rw [hEnergyAB]

end StratificationTheory
