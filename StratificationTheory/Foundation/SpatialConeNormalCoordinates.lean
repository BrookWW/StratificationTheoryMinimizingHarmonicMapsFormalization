module

public import StratificationTheory.Foundation.SpatialConeNormalMaps

/-!
# Spatial cone normals with unchanged interpolation time

The actual spatial unit normal lifts by a zero time coordinate. Its normal
translations equal parallel-side slices with a small spatial tangential
shift; the independent time coordinate is unchanged.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology
namespace StratificationTheory

private theorem spatial_cone_normal_translation_raw (n : ℕ) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let γ : ℝ → Domain (n + 1) → Domain (n + 1 + 1) := fun δ y =>
      e.symm (b.symm ((b y).1, EuclideanSpace.single (0 : Fin 1) ((b y).2 0 - δ)),
        EuclideanSpace.single (0 : Fin 1) ((b y).2 0))
    let ν₀ := e.symm (b.symm (0, EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
      EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹)
    let ν := eF.symm (ν₀,0)
    let Γ : ℝ → Domain (n + 1 + 1) → Domain (n + 1 + 1 + 1) := fun δ y =>
      eF.symm (γ δ (e y).1,(e y).2)
    let τ₀ : ℝ → Domain (n + 1) := fun η =>
      b.symm (0,EuclideanSpace.single (0 : Fin 1) (η / Real.sqrt 2))
    let shift : ℝ → Domain (n + 1 + 1) := fun η => e.symm (τ₀ η,0)
    ‖ν‖ = 1 ∧
      (∀ y η, Γ 0 y + η • ν = Γ (Real.sqrt 2 * η) (y + shift η)) ∧
      Continuous shift ∧ shift 0 = 0 := by
  intro b e eF γ ν₀ ν Γ τ₀ shift
  have hsp := native_cone_normal_translation n
  have hnormal₀ : ∀ y η, γ 0 y + η • ν₀ = γ (Real.sqrt 2 * η) (y + τ₀ η) := hsp.2
  have hν : ‖ν‖ = 1 := by
    have hs : ‖ν₀‖ = 1 := hsp.1
    have hsq := norm_sq_finAddEquivProd_symm (n := n + 1 + 1) (m := 1) (ν₀,0)
    change ‖ν‖ ^ 2 = ‖ν₀‖ ^ 2 + ‖(0 : Domain 1)‖ ^ 2 at hsq
    rw [hs,norm_zero,zero_pow (by decide : 2 ≠ 0),one_pow,add_zero] at hsq
    nlinarith only [hsq,norm_nonneg ν]
  refine ⟨hν,?_,?_,?_⟩
  · intro y η
    dsimp only [Γ,ν,shift]
    rw [← eF.symm.map_smul,← eF.symm.map_add,e.map_add,e.apply_symm_apply]
    apply congrArg eF.symm
    apply Prod.ext
    · exact hnormal₀ (e y).1 η
    · simp only [Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]
  · have hs : Isometry (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
      intro r s
      exact PiLp.edist_single_same 2 (fun _ : Fin 1 => ℝ) 0 r s
    exact e.symm.continuous.comp
      ((b.symm.continuous.comp (continuous_const.prodMk
        (hs.continuous.comp (continuous_id.div_const _)))).prodMk continuous_const)
  · simp [shift,τ₀]

/-- The same literal maps have the genuine spatial unit normal and the
actual normal/parallel coordinate identity, with a vanishing shift. -/
theorem spatial_cone_normal_translation (n : ℕ) :
    ‖spatialConeNormalVector n‖ = 1 ∧
      (∀ y η, spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n =
        spatialConeParallelSlice n (Real.sqrt 2 * η) (y + spatialConeNormalTangentialShift n η)) ∧
      Continuous (spatialConeNormalTangentialShift n) ∧ spatialConeNormalTangentialShift n 0 = 0 := by
  have hraw := spatial_cone_normal_translation_raw n
  dsimp only at hraw
  refine ⟨?_,?_,?_,?_⟩
  · rw [spatialConeNormalVector_eq]
    exact hraw.1
  · intro y η
    simp only [spatialConeParallelSlice_eq,spatialConeNormalVector_eq,spatialConeNormalTangentialShift_eq]
    exact hraw.2.1 y η
  · change Continuous (fun η : ℝ =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)).symm
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (0,EuclideanSpace.single (0 : Fin 1) (η / Real.sqrt 2)),0))
    exact hraw.2.2.1
  · rw [spatialConeNormalTangentialShift_eq]
    exact hraw.2.2.2

end StratificationTheory
