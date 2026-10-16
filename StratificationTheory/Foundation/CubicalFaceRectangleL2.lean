module

public import StratificationTheory.Foundation.CubicalConeGeometry
public import StratificationTheory.Foundation.CoordinatePiecewiseSobolevData

public section

open HarmonicMaps MeasureTheory Set

namespace StratificationTheory

/-- The original full-face L2 map pulls back to the native spatial-time
rectangle on every measurable smaller base, with no supplied product data. -/
theorem memLp_unit_face_native_rectangle {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {w : Domain (n + 1) → E}
    (hw : MemLp w 2 (volume.restrict
      (⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1)))
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSbound : ∀ x ∈ S, ∀ k : Fin n, |x k| < 1) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MemLp (fun p : Domain n × ℝ => w (b.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))) 2
      ((volume.restrict S).prod (volume.restrict (Ioo (-1 : ℝ) 1))) := by
  intro b
  let V := {y : Domain (n + 1) | (b y).1 ∈ S ∧ (b y).2 0 ∈ Ioo (-1 : ℝ) 1}
  have hsub : V ⊆ ⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1 := by
    intro y hy
    apply (mem_unit_coordinate_face_iff y).mpr
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · exact abs_lt.mpr hy.2
    · exact hSbound (b y).1 hy.1 j
  have hV : MemLp w 2 (volume.restrict V) := hw.mono_measure (Measure.restrict_mono_set volume hsub)
  exact hV.comp_measurePreserving (measurePreserving_inverse_native_rectangle hS measurableSet_Ioo)

end StratificationTheory
