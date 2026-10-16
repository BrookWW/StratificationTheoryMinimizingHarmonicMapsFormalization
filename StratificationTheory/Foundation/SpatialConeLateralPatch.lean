module

public import StratificationTheory.Foundation.SpatialConeNormalMaps
public import StratificationTheory.Foundation.CubicalLateralPatch

/-!
# Compact actual spatial lateral patches with independent time

Every genuine simple spatial seam point inside the height band (0,2)
has a compact parameter neighborhood for the original normal weak graph.
The independent time remains inside its original open interval.
-/

public section
open HarmonicMaps Set Metric Filter
open scoped Topology
namespace StratificationTheory

theorem exists_spatial_cone_lateral_time_patch {n : ℕ}
    (y : Domain (n + 1 + 1 + 1)) {c d : ℝ} :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let T : Domain (n + 1) → ℝ := fun z => (b z).2 0
    let ξ : Domain (n + 1) → Domain n := fun z => (T z)⁻¹ • (b z).1
    0 < (e (eF y).1).2 0 → (e (eF y).1).2 0 < 2 →
    (b (e (eF y).1).1).2 0 = (e (eF y).1).2 0 →
    (∀ i : Fin n, |(b (e (eF y).1).1).1 i| < (e (eF y).1).2 0) →
    (eF y).2 0 ∈ Ioo c d →
    ∃ (b₀ b₁ : ℝ) (z : Domain (n + 1 + 1)) (U : OpenDomain (n + 1 + 1)),
      0 < b₀ ∧ b₀ < b₁ ∧ b₁ < 2 ∧ spatialConeParallelSlice n 0 z = y ∧ z ∈ U.val ∧
      IsCompact (closure U.val) ∧
      closure U.val ⊆ interior {x : Domain (n + 1 + 1) |
        (T (e x).1 ∈ Icc b₀ b₁ ∧ ξ (e x).1 ∈ S) ∧ (e x).2 0 ∈ Ioo c d} := by
  intro b e eF S T ξ ht ht2 htie hstrict htime
  let t := (e (eF y).1).2 0
  let z := e.symm ((e (eF y).1).1,(eF y).2)
  have hsingle (v : Domain 1) : EuclideanSpace.single (0 : Fin 1) (v 0) = v := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [PiLp.single_apply,ite_true]
  have hHeightVec : (b (e (eF y).1).1).2 = (e (eF y).1).2 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact htie
  have hΓ : spatialConeParallelSlice n 0 z = y := by
    rw [spatialConeParallelSlice_eq]
    change eF.symm
      (e.symm (b.symm ((b (e z).1).1,EuclideanSpace.single (0 : Fin 1) ((b (e z).1).2 0 - 0)),
        EuclideanSpace.single (0 : Fin 1) ((b (e z).1).2 0)),(e z).2) = y
    simp only [z,e.apply_symm_apply,sub_zero]
    rw [hsingle,b.symm_apply_apply,hHeightVec,e.symm_apply_apply,eF.symm_apply_apply]
  let b₀ := t / 2
  let b₁ := (t + 2) / 2
  have hTz : T (e z).1 = t := by
    change (b (e z).1).2 0 = t
    rw [show e z = ((e (eF y).1).1,(eF y).2) from e.apply_symm_apply _]
    exact htie
  have hξz : ξ (e z).1 ∈ S := by
    apply mem_iInter.mpr
    intro i
    change -1 < ξ (e z).1 i ∧ ξ (e z).1 i < 1
    rw [← abs_lt]
    change |(T (e z).1)⁻¹ * (b (e z).1).1 i| < 1
    rw [hTz,abs_mul,abs_inv,abs_of_pos ht]
    apply (inv_mul_lt_iff₀ ht).mpr
    rw [mul_one]
    change |(b (e (e.symm ((e (eF y).1).1,(eF y).2))).1).1 i| < t
    rw [e.apply_symm_apply]
    exact hstrict i
  have hTc : Continuous (fun x : Domain (n + 1 + 1) => T (e x).1) := by
    dsimp only [T]
    fun_prop
  have hBase : Continuous (fun x : Domain (n + 1 + 1) => (b (e x).1).1) := by fun_prop
  have hξc : ContinuousAt (fun x : Domain (n + 1 + 1) => ξ (e x).1) z :=
    (hTc.continuousAt.inv₀ (by rw [hTz]; exact ht.ne')).smul hBase.continuousAt
  have hSc : IsOpen S := isOpen_iInter_of_finite fun i : Fin n =>
    isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous
  have hTimec : Continuous (fun x : Domain (n + 1 + 1) => (e x).2 0) := by fun_prop
  have hnhds : {x : Domain (n + 1 + 1) |
      (T (e x).1 ∈ Icc b₀ b₁ ∧ ξ (e x).1 ∈ S) ∧ (e x).2 0 ∈ Ioo c d} ∈ 𝓝 z := by
    have hBand : (fun x => T (e x).1) ⁻¹' Ioo b₀ b₁ ∈ 𝓝 z :=
      hTc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by
        rw [hTz]
        constructor <;> dsimp only [b₀,b₁] <;> linarith only [ht,ht2]))
    have hTime : (fun x : Domain (n + 1 + 1) => (e x).2 0) ⁻¹' Ioo c d ∈ 𝓝 z :=
      hTimec.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by
        change (e (e.symm ((e (eF y).1).1,(eF y).2))).2 0 ∈ Ioo c d
        rw [e.apply_symm_apply]
        exact htime))
    filter_upwards [hBand,hξc.preimage_mem_nhds (hSc.mem_nhds hξz),hTime] with x hx hxξ hxTime
    exact ⟨⟨⟨hx.1.le,hx.2.le⟩,hxξ⟩,hxTime⟩
  obtain ⟨U,hzU,hU,hImage⟩ := exists_compact_open_patch_preimage continuous_id isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hnhds)
  refine ⟨b₀,b₁,z,U,?_,?_,?_,hΓ,hzU,hU,?_⟩
  · dsimp only [b₀]; linarith only [ht]
  · dsimp only [b₀,b₁]; linarith
  · dsimp only [b₁]; linarith only [ht2]
  · intro x hx
    exact hImage ⟨x,hx,rfl⟩

end StratificationTheory
