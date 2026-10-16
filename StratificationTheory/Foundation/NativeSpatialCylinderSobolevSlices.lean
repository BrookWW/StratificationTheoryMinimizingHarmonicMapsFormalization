module

public import StratificationTheory.Foundation.NativeSpatialCylinderGraphSlices
public import StratificationTheory.Foundation.NativeCylinderSmoothGraphClosure

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal BigOperators
namespace StratificationTheory

/-- Original ambient Sobolev data produce actual native cylinder weak
slices at one common full-measure set of spatial radii. -/
theorem ae_memCylinderW12_of_original_ball {n q : ℕ} (hn : 2 ≤ n)
    {s R a b : ℝ} (hs : 0 < s) (hsR : s < R) (hab : a < b)
    {center : Domain (n + 1)} {B : ℝ} (hB : 0 < B)
    (W : Domain (n + 1) → Ambient q) (DW : Domain (n + 1) → Gradient (n + 1) q)
    (hW : MemW12 (ballDomain center B) W DW) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let source := {y : Domain (n + 1) |
      (s < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}
    let Ω : OpenDomain (n + 1) :=
      ⟨{y | (1 / 2 < ‖(e y).1‖ ∧ ‖(e y).1‖ < 2) ∧ (e y).2 0 ∈ Ioo a b},
        (isOpen_Ioo.preimage (continuous_fst.comp e.continuous).norm).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    source ⊆ ball center B →
    ∀ᵐ r ∂volume.restrict (Ioo s R),
      let X := fun c : unitCylinder n a b => e.symm (r • (e c.val).1, (e c.val).2)
      let F := fun y : Domain (n + 1) => e.symm (r • (‖(e y).1‖⁻¹ • (e y).1), (e y).2)
      MemCylinderW12 hn hab (fun c => W (X c)) ∧
        MemW12 Ω (W ∘ F) (fun y i => ∑ j : Fin (n + 1),
          (fderiv ℝ F y (EuclideanSpace.single i 1)) j • DW (F y) j) := by
  intro e source Ω hSource
  obtain ⟨f, hf, hGraph⟩ := exists_native_spatial_cylinder_graph_approximation
    (by omega : 0 < n) hs hsR hB W DW hW hSource
  filter_upwards [hGraph] with r hr
  exact memCylinderW12_of_native_spatial_smooth_graph_limit hn hab r W DW f hf
    hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2

end StratificationTheory
