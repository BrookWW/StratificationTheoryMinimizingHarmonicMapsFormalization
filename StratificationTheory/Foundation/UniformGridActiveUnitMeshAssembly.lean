module

public import StratificationTheory.Foundation.UniformGridUnitMeshAssembly

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators
namespace StratificationTheory

/-- Actual unit prism maps on the cells meeting an open mesh domain produce
one physical weak map. Cells outside that domain are filled by zero; their
values and trace data do not contribute to the resulting map or its energy. -/
theorem memW12_uniform_grid_active_unit_mesh {n N q : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (Ω : OpenDomain (n + 2)) (hΩsub : Ω.val ⊆ (uniformGridBox (n + 2) N ε).val)
    (active : (Fin (n + 2) → Fin N) → Prop)
    (hActive : ∀ z, (∃ x ∈ Ω.val, ∀ i,
      x i ∈ Icc ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε)) → active z)
    (V : (z : Fin (n + 2) → Fin N) → active z → Domain (n + 2) → Ambient q)
    (DV : (z : Fin (n + 2) → Fin N) → active z → Domain (n + 2) → Gradient (n + 2) q)
    (g : (z : Fin (n + 2) → Fin N) → active z → Fin (n + 2) → Bool → Domain (n + 1) → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let S := ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain (n + 2) :=
      ⟨⋂ j : Fin (n + 2), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin (n + 2) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    (∀ z hz, MemW12 B (V z hz) (DV z hz)) →
    ∀ M : ℝ, 0 ≤ M → (∀ z hz, ∀ᵐ x ∂volume.restrict B.val, ‖V z hz x‖ ≤ M) →
    ∀ K : (z : Fin (n + 2) → Fin N) → active z → Fin (n + 2) →
      C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ z hz i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain (n + 1) => V z hz (cubicalSignedFaceIsometry (n + 1) i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K z hz i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V z hz (cubicalSignedFaceIsometry (n + 1) i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ z hz i positive,
      (K z hz i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 1) → Ambient q)
        =ᵐ[volume.restrict S] g z hz i positive) →
    (∀ (i : Fin (n + 2)) (z : Fin (n + 2) → Fin N) (hzi : 0 < (z i).val),
      (∃ x ∈ Ω.val, x i = ((z i).val : ℝ) * ε ∧
        ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε)) →
      ∀ (hz : active z) (hm : active (Function.update z i ⟨(z i).val - 1, by omega⟩)),
        g (Function.update z i ⟨(z i).val - 1, by omega⟩) hm i true = g z hz i false) →
    let lo := fun z : Fin (n + 2) → Fin N => WithLp.toLp 2 (fun j => ((z j).val : ℝ) * ε)
    let T := fun (z : Fin (n + 2) → Fin N) (x : Domain (n + 2)) =>
      (ε / 2)⁻¹ • (x - (lo z + WithLp.toLp 2 (fun _ => ε / 2)))
    let unitEnergy : (Fin (n + 2) → Fin N) → ℝ := fun z => by
      classical
      exact if hz : active z then (∫ y in B.val, hsNormSq (DV z hz y)) else 0
    ∃ (W : Domain (n + 2) → Ambient q) (D : Domain (n + 2) → Gradient (n + 2) q),
      MemW12 Ω W D ∧
      (∫ x in Ω.val, hsNormSq (D x)) ≤
        (ε / 2) ^ (((n + 2 : ℕ) : ℤ) - 2) *
          ∑ z : Fin (n + 2) → Fin N, unitEnergy z ∧
      (∀ z hz x, x ∈ Ω.val ∩ (uniformGridCell (n + 2) N ε z).val →
        W x = V z hz (T z x) ∧ D x = (ε / 2)⁻¹ • DV z hz (T z x)) ∧
      ∀ P : Ambient q → Prop,
        (∀ z hz, (Ω.val ∩ (uniformGridCell (n + 2) N ε z).val).Nonempty →
          ∀ᵐ x ∂volume.restrict B.val, P (V z hz x)) →
        ∀ᵐ x ∂volume.restrict Ω.val, P (W x) := by
  classical
  intro e S B hV M hM hBound K hK hEnd hFace lo T unitEnergy
  let V₀ : (Fin (n + 2) → Fin N) → Domain (n + 2) → Ambient q := fun z => if hz : active z then V z hz else 0
  let D₀ : (Fin (n + 2) → Fin N) → Domain (n + 2) → Gradient (n + 2) q := fun z => if hz : active z then DV z hz else 0
  let g₀ : (Fin (n + 2) → Fin N) → Fin (n + 2) → Bool → Domain (n + 1) → Ambient q := fun z => if hz : active z then g z hz else 0
  let K₀ : (Fin (n + 2) → Fin N) → Fin (n + 2) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)) := fun z => if hz : active z then K z hz else 0
  have hW₀ z : MemW12 B (V₀ z) (D₀ z) := by
    by_cases hz : active z
    · simpa only [V₀, D₀, dif_pos hz] using hV z hz
    · simp only [V₀, D₀, dif_neg hz]
      exact MemW12.zero B
  have hB₀ z : ∀ᵐ x ∂volume.restrict B.val, ‖V₀ z x‖ ≤ M := by
    by_cases hz : active z
    · simpa only [V₀, dif_pos hz] using hBound z hz
    · exact Filter.Eventually.of_forall (by intro x; simpa only [V₀, dif_neg hz, Pi.zero_apply, norm_zero] using hM)
  have hK₀ z i : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain (n + 1) => V₀ z (cubicalSignedFaceIsometry (n + 1) i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K₀ z i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V₀ z (cubicalSignedFaceIsometry (n + 1) i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
    by_cases hz : active z
    · simpa only [V₀, K₀, dif_pos hz] using hK z hz i
    · filter_upwards [] with t
      intro ht
      simp only [V₀, K₀, dif_neg hz, Pi.zero_apply, ContinuousMap.zero_apply]
      change ∃ hs : MemLp (0 : Domain (n + 1) → Ambient q) 2 (volume.restrict S),
        (0 : Lp (Ambient q) 2 (volume.restrict S)) = hs.toLp 0
      let hs : MemLp (0 : Domain (n + 1) → Ambient q) 2 (volume.restrict S) := MemLp.zero
      exact ⟨hs, hs.toLp_zero.symm⟩
  have hEnd₀ z i positive : (K₀ z i ⟨if positive then 1 else -1,
      by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 1) → Ambient q)
      =ᵐ[volume.restrict S] g₀ z i positive := by
    by_cases hz : active z
    · simpa only [K₀, g₀, dif_pos hz] using hEnd z hz i positive
    · simp only [K₀, g₀, dif_neg hz, Pi.zero_apply, ContinuousMap.zero_apply]
      exact Lp.coeFn_zero _ _ _
  have hCompat (i : Fin (n + 2)) (z : Fin (n + 2) → Fin N) (hzi : 0 < (z i).val)
      (hMeet : ∃ x ∈ Ω.val, x i = ((z i).val : ℝ) * ε ∧
        ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε)) :
      let k : Fin N := ⟨(z i).val - 1, by omega⟩
      g₀ (Function.update z i k) i true =ᵐ[volume.restrict S] g₀ z i false := by
    intro k
    obtain ⟨x, hx, hxi, hxj⟩ := hMeet
    have hkp : (k.val : ℝ) + 1 = (z i).val := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ (z i).val)
    have hz : active z := hActive z ⟨x, hx, fun j => by
      by_cases hj : j = i
      · subst j; rw [hxi]; exact ⟨le_rfl, by nlinarith [hε]⟩
      · exact ⟨(hxj j hj).1.le, (hxj j hj).2.le⟩⟩
    have hm : active (Function.update z i k) := hActive _ ⟨x, hx, fun j => by
      by_cases hj : j = i
      · subst j; simp only [Function.update_self]; rw [hxi]; constructor <;> nlinarith [hε]
      · simp only [Function.update_of_ne hj]; exact ⟨(hxj j hj).1.le, (hxj j hj).2.le⟩⟩
    rw [show g₀ (Function.update z i k) i true = g (Function.update z i k) hm i true from by simp only [g₀, dif_pos hm]]
    rw [show g₀ z i false = g z hz i false from by simp only [g₀, dif_pos hz]]
    exact Filter.Eventually.of_forall (congrFun (hFace i z hzi ⟨x, hx, hxi, hxj⟩ hz hm))
  obtain ⟨hFull, hEnergy, hPoint, hProp⟩ := memW12_uniform_grid_unit_mesh_on_open_subdomain
    hε Ω hΩsub V₀ D₀ g₀ hW₀ M hB₀ K₀ hK₀ hEnd₀ hCompat
  refine ⟨_, _, hFull, ?_, ?_, ?_⟩
  · convert hEnergy using 1
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : active z
    · simp only [unitEnergy, D₀, dif_pos hz, B]
    · simp [unitEnergy, D₀, dif_neg hz, hsNormSq]
  · intro z hz x hx
    have hh := hPoint z x hx
    constructor
    · simpa only [V₀, dif_pos hz, T, lo] using hh.1
    · funext j
      simpa only [D₀, dif_pos hz, T, lo, Pi.smul_apply] using congrFun hh.2 j
  · intro P hP
    apply hProp P
    intro z hz
    obtain ⟨x, hx⟩ := hz
    have ha : active z := hActive z ⟨x, hx.1, fun i =>
      ⟨(mem_uniformGridCell_iff _ _ _ _ _ |>.mp hx.2 i).1.le,
        (mem_uniformGridCell_iff _ _ _ _ _ |>.mp hx.2 i).2.le⟩⟩
    simpa only [V₀, dif_pos ha] using hP z ha ⟨x, hx⟩

end StratificationTheory
