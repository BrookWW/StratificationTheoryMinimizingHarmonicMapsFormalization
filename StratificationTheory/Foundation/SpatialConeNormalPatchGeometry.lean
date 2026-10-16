module

public import StratificationTheory.Foundation.SpatialConeNormalLinearChart

/-!
# Actual compact spatial normal patches

Compact lateral-time patches admit uniform inward normal rectangles. The
spatial cone inequalities are checked in their actual coordinates, and the
independent time coordinate is preserved.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology
namespace StratificationTheory

/-- Strict lateral bounds on a compact original parameter patch supply the
actual uniform positive normal cone inequalities. -/
theorem eventually_spatial_normal_patch_inside_cone {n : ℕ}
    {K : Set (Domain (n + 1 + 1))} (hK : IsCompact K)
    {ρ R c d : ℝ} :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let T := fun y : Domain (n + 1 + 1) => (b (e y).1).2 0
    (∀ y ∈ K, 0 < T y ∧ ρ < T y ∧ T y < 2 ∧
      (∀ i : Fin n, |(b (e y).1).1 i| < T y) ∧
      (e y).2 0 ∈ Ioo c d ∧ ‖spatialConeParallelSlice n 0 y‖ < R) →
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ y ∈ K,
      let z := spatialConeParallelSlice n 0 y + η • spatialConeNormalVector n
      (e (eF z).1).2 0 ∈ Ioo ρ 2 ∧
      (∀ i : Fin (n + 1), |(e (eF z).1).1 i| < (e (eF z).1).2 0) ∧
      (eF z).2 0 ∈ Ioo c d ∧ ‖z‖ < R := by
  intro b e eF T hBounds
  let Z : ℝ × Domain (n + 1 + 1) → Domain (n + 1 + 1 + 1) := fun p =>
    spatialConeParallelSlice n 0 p.2 + p.1 • spatialConeNormalVector n
  have hZ : Continuous Z := by
    have hΓ : Continuous (spatialConeParallelSlice n 0) := by
      obtain ⟨F,hF⟩ := exists_spatial_cone_normal_linear_chart n
      have hEq : spatialConeParallelSlice n 0 =
          fun y => F (eF.symm (y,EuclideanSpace.single (0 : Fin 1) (0 : ℝ))) := by
        funext y
        simpa only [zero_smul,add_zero] using (hF y 0).symm
      rw [hEq]
      exact F.continuous.comp (eF.symm.continuous.comp (continuous_id.prodMk continuous_const))
    exact (hΓ.comp continuous_snd).add (continuous_fst.smul continuous_const)
  have hTang (i : Fin n) :
      Continuous (fun p : ℝ × Domain (n + 1 + 1) =>
        |(b (e (eF (Z p)).1).1).1 i|) := by
    fun_prop
  have hHeight : Continuous (fun p : ℝ × Domain (n + 1 + 1) =>
      (e (eF (Z p)).1).2 0) := by fun_prop
  have hTime : Continuous (fun p : ℝ × Domain (n + 1 + 1) => (eF (Z p)).2 0) := by
    fun_prop
  have h0 (y : Domain (n + 1 + 1)) : Z (0,y) = spatialConeParallelSlice n 0 y := by
    simp only [Z,zero_smul,add_zero]
  have hCoords (y : Domain (n + 1 + 1)) (η : ℝ) :
      eF (Z (η,y)) =
        (e.symm (b.symm ((b (e y).1).1,EuclideanSpace.single (0 : Fin 1)
          (T y - η * (Real.sqrt 2)⁻¹)),
          EuclideanSpace.single (0 : Fin 1) (T y + η * (Real.sqrt 2)⁻¹)),(e y).2) := by
    dsimp only [Z]
    rw [spatialConeParallelSlice_eq,spatialConeNormalVector_eq]
    change eF (eF.symm
      (e.symm (b.symm ((b (e y).1).1,EuclideanSpace.single (0 : Fin 1) (T y - 0)),
        EuclideanSpace.single (0 : Fin 1) (T y)),(e y).2) + η •
      eF.symm (e.symm (b.symm (0,EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
        EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹),0)) = _
    rw [eF.map_add,eF.map_smul,eF.apply_symm_apply,eF.apply_symm_apply]
    simp only [sub_zero]
    apply Prod.ext
    · change e.symm (b.symm ((b (e y).1).1,EuclideanSpace.single (0 : Fin 1) (T y)),
        EuclideanSpace.single (0 : Fin 1) (T y)) + η •
        e.symm (b.symm (0,EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)),
          EuclideanSpace.single (0 : Fin 1) (Real.sqrt 2)⁻¹) = _
      rw [← e.symm.map_smul,← e.symm.map_add]
      apply congrArg e.symm
      apply Prod.ext
      · change b.symm ((b (e y).1).1,EuclideanSpace.single (0 : Fin 1) (T y)) +
          η • b.symm (0,EuclideanSpace.single (0 : Fin 1) (-(Real.sqrt 2)⁻¹)) = _
        rw [← b.symm.map_smul,← b.symm.map_add]
        apply congrArg b.symm
        apply Prod.ext
        · simp
        · ext i
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          simp only [Prod.snd_add,Prod.smul_snd,PiLp.add_apply,PiLp.smul_apply,
            PiLp.single_apply,ite_true,smul_eq_mul,T]
          ring
      · ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp only [Prod.snd_add,Prod.smul_snd,PiLp.add_apply,PiLp.smul_apply,
          PiLp.single_apply,ite_true,smul_eq_mul,T]
    · change (e y).2 + η • (0 : Domain 1) = (e y).2
      simp
  have hUniform : ∀ᶠ η in 𝓝 (0 : ℝ), ∀ y ∈ K,
      ρ < (e (eF (Z (η,y))).1).2 0 ∧ (e (eF (Z (η,y))).1).2 0 < 2 ∧
      (∀ i : Fin n, |(b (e (eF (Z (η,y))).1).1).1 i| <
        (e (eF (Z (η,y))).1).2 0) ∧
      (eF (Z (η,y))).2 0 ∈ Ioo c d ∧ ‖Z (η,y)‖ < R := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have h := hBounds y hy
    have hH0 : (e (eF (Z (0,y))).1).2 0 = T y := by
      simp only [hCoords,e.apply_symm_apply,zero_mul,add_zero,PiLp.single_apply,ite_true]
    have hT0 (i : Fin n) : (b (e (eF (Z (0,y))).1).1).1 i = (b (e y).1).1 i := by
      simp only [hCoords,e.apply_symm_apply,b.apply_symm_apply]
    have hTime0 : (eF (Z (0,y))).2 0 = (e y).2 0 := by rw [hCoords]
    have hlow : ∀ᶠ p in 𝓝 (0,y), ρ < (e (eF (Z p)).1).2 0 := by
      apply continuous_const.continuousAt.eventually_lt hHeight.continuousAt
      rw [hH0]
      exact h.2.1
    have hhigh : ∀ᶠ p in 𝓝 (0,y), (e (eF (Z p)).1).2 0 < 2 := by
      apply hHeight.continuousAt.eventually_lt continuous_const.continuousAt
      rw [hH0]
      exact h.2.2.1
    have hts : ∀ᶠ p in 𝓝 (0,y), ∀ i : Fin n,
        |(b (e (eF (Z p)).1).1).1 i| < (e (eF (Z p)).1).2 0 := by
      apply eventually_all.mpr
      intro i
      apply (hTang i).continuousAt.eventually_lt hHeight.continuousAt
      rw [hT0,hH0]
      exact h.2.2.2.1 i
    have htm : ∀ᶠ p in 𝓝 (0,y), (eF (Z p)).2 0 ∈ Ioo c d := by
      apply hTime.continuousAt.eventually
      apply isOpen_Ioo.mem_nhds
      change (eF (Z (0,y))).2 0 ∈ Ioo c d
      rw [hTime0]
      exact h.2.2.2.2.1
    have hnorm : ∀ᶠ p in 𝓝 (0,y), ‖Z p‖ < R := by
      apply hZ.norm.continuousAt.eventually_lt continuous_const.continuousAt
      change ‖Z (0,y)‖ < R
      rw [h0]
      exact h.2.2.2.2.2
    filter_upwards [hlow,hhigh,hts,htm,hnorm] with p hp₀ hp₁ hp₂ hp₃ hp₄
    constructor
    · exact hp₀
    constructor
    · exact hp₁
    constructor
    · exact hp₂
    exact ⟨hp₃,hp₄⟩
  filter_upwards [hUniform.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with η hη hηpos y hy
  have h := hη y hy
  refine ⟨⟨h.1,h.2.1⟩,?_,h.2.2.2.1,h.2.2.2.2⟩
  intro i
  have hty := (hBounds y hy).1
  have hp : 0 < η * (Real.sqrt 2)⁻¹ := mul_pos hηpos (inv_pos.mpr
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  change |(e (eF (Z (η,y))).1).1 i| < (e (eF (Z (η,y))).1).2 0
  refine Fin.addCases (fun j : Fin n => ?_) (fun j : Fin 1 => ?_) i
  · change |(b (e (eF (Z (η,y))).1).1).1 j| < (e (eF (Z (η,y))).1).2 0
    exact h.2.2.1 j
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change |(b (e (eF (Z (η,y))).1).1).2 0| < (e (eF (Z (η,y))).1).2 0
    simp only [hCoords,e.apply_symm_apply,b.apply_symm_apply,PiLp.single_apply,ite_true]
    apply abs_lt.mpr
    constructor <;> linarith

end StratificationTheory
