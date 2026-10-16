module

public import StratificationTheory.Foundation.UniformGridActiveUnitMeshAssembly
public import StratificationTheory.Foundation.UniformGridSlabGeometry
public import StratificationTheory.Foundation.CanonicalNeighborPrismFaces

public section
open HarmonicMaps MeasureTheory Set Filter Module
open scoped Topology BigOperators
namespace StratificationTheory

/-- A coherent global family of filled coordinate prisms gives one actual
weak map on a finite open spatial mesh times the original single time slab.
The shared face classes are derived from the same physical child indices. -/
theorem memW12_uniform_grid_from_canonical_prism_family {n L q : ℕ}
    (grid : Module.Basis (Fin (n + 2)) ℝ (Fin (n + 2) → ℝ))
    (offset : Fin (n + 2) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    let Cell := fun r : ℕ => {c : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (c.val.1 : Fin r → Fin (n + 2))}
    let B := fun r : ℕ => (⟨⋂ j : Fin r, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite (fun j : Fin r => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩ : OpenDomain r)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 2) (m := 1)
    ∀ (V : (r : ℕ) → Cell r → Domain (r + 1) → Ambient q)
      (DV : (r : ℕ) → Cell r → Domain (r + 1) → Gradient (r + 1) q)
      (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (frame : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Equiv.Perm (Fin (r + 1)))
      (cap : Cell (n + 2) → Bool → Domain (n + 2) → Ambient q),
    (∀ r c i side, (child r c i side).val.val.1 = i.succAboveEmb.trans c.val.val.1) →
    (∀ r c i side, (child r c i side).val.val.2 = c.val.val.2 +
      (if side then ε else 0) • EuclideanSpace.single (c.val.val.1 i) (1 : ℝ)) →
    (∀ r c i side, frame r c i side i = Fin.last r) →
    (∀ r c i side (a : Fin r), frame r c i side (i.succAbove a) = a.castSucc) →
    (∀ c, MemW12 (B (n + 3)) (V (n + 2) c) (DV (n + 2) c)) →
    ∀ M : ℝ, 0 ≤ M →
    (∀ c, ∀ᵐ x ∂volume.restrict (B (n + 3)).val, ‖V (n + 2) c x‖ ≤ M) →
    ∀ H : Cell (n + 2) → Fin (n + 3) → C(Icc (-1 : ℝ) 1,
      Lp (Ambient q) 2 (volume.restrict (B (n + 2)).val)),
    (∀ c i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => V (n + 2) c (cubicalSignedFaceIsometry (n + 2) i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B (n + 2)).val),
        H c i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (n + 2) c (cubicalSignedFaceIsometry (n + 2) i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ c side, (H c (Fin.last (n + 2)) ⟨if side then 1 else -1,
      by cases side <;> norm_num, by cases side <;> norm_num⟩ : Domain (n + 2) → Ambient q)
        =ᵐ[volume.restrict (B (n + 2)).val] cap c side) →
    (∀ c (i : Fin (n + 2)) side, (H c i.castSucc ⟨if side then 1 else -1,
      by cases side <;> norm_num, by cases side <;> norm_num⟩ : Domain (n + 2) → Ambient q)
        =ᵐ[volume.restrict (B (n + 2)).val]
          V (n + 1) (child (n + 1) c i side) ∘
            cubicalSignedPermutation (n + 2) (frame (n + 1) c i side) (fun _ => true)) →
    ∀ (Ω : OpenDomain (n + 3))
      (hΩsub : Ω.val ⊆ (uniformGridBox (n + 3) L ε).val)
      (hTime : ∀ x ∈ Ω.val, x (Fin.last (n + 2)) ∈ Ioo (0 : ℝ) ε)
      (active : (Fin (n + 3) → Fin L) → Prop),
    (∀ z, (∃ x ∈ Ω.val, ∀ i,
      x i ∈ Icc ((z i).val * ε) (((z i).val + (1 : ℝ)) * ε)) → active z) →
    ∀ (index : (z : Fin (n + 3) → Fin L) → active z → Cell (n + 2))
      (base : Domain (n + 2)),
    (∀ z hz, (index z hz).val.val.1 = Function.Embedding.refl _) →
    (∀ z hz, (index z hz).val.val.2 = base +
      WithLp.toLp 2 (fun j : Fin (n + 2) => ((z j.castSucc).val : ℝ) * ε)) →
    let lo := fun z : Fin (n + 3) → Fin L => WithLp.toLp 2 (fun j => ((z j).val : ℝ) * ε)
    let T := fun (z : Fin (n + 3) → Fin L) (x : Domain (n + 3)) =>
      (ε / 2)⁻¹ • (x - (lo z + WithLp.toLp 2 (fun _ => ε / 2)))
    let unitEnergy : (Fin (n + 3) → Fin L) → ℝ := fun z => by
      classical
      exact if hz : active z then (∫ x in (B (n + 3)).val, hsNormSq (DV (n + 2) (index z hz) x)) else 0
    ∃ (W : Domain (n + 3) → Ambient q) (D : Domain (n + 3) → Gradient (n + 3) q),
      MemW12 Ω W D ∧
      (∫ x in Ω.val, hsNormSq (D x)) ≤ (ε / 2) ^ (n + 1) * ∑ z, unitEnergy z ∧
      (∀ z hz x, x ∈ Ω.val ∩ (uniformGridCell (n + 3) L ε z).val →
        W x = V (n + 2) (index z hz) (T z x) ∧
        D x = (ε / 2)⁻¹ • DV (n + 2) (index z hz) (T z x)) ∧
      ∀ P : Ambient q → Prop,
        (∀ z hz, (Ω.val ∩ (uniformGridCell (n + 3) L ε z).val).Nonempty →
          ∀ᵐ x ∂volume.restrict (B (n + 3)).val, P (V (n + 2) (index z hz) x)) →
        ∀ᵐ x ∂volume.restrict Ω.val, P (W x) := by
  classical
  intro Cell B e V DV child frame cap hAxes hOrigin hSlot hSurv hW M hM hBound H hRaw hCap hSpatial
    Ω hΩsub hTime active hActive index base hIndexAxes hIndexOrigin lo T unitEnergy
  let g : (z : Fin (n + 3) → Fin L) → active z → Fin (n + 3) → Bool → Domain (n + 2) → Ambient q :=
    fun z hz => Fin.lastCases (cap (index z hz)) (fun i side =>
      V (n + 1) (child (n + 1) (index z hz) i side) ∘
        cubicalSignedPermutation (n + 2) (frame (n + 1) (index z hz) i side) (fun _ => true))
  have hEnd z hz i : ∀ side,
      (H (index z hz) i ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain (n + 2) → Ambient q) =ᵐ[volume.restrict (B (n + 2)).val] g z hz i side := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [g, Fin.lastCases_last] using hCap (index z hz)
    · simpa only [g, Fin.lastCases_castSucc] using hSpatial (index z hz) j
  have hFace (i : Fin (n + 3)) (z : Fin (n + 3) → Fin L) (hzi : 0 < (z i).val)
      (hMeet : ∃ x ∈ Ω.val, x i = ((z i).val : ℝ) * ε ∧
        ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε))
      (hz : active z) (hm : active (Function.update z i ⟨(z i).val - 1, by omega⟩)) :
      g (Function.update z i ⟨(z i).val - 1, by omega⟩) hm i true = g z hz i false := by
    obtain ⟨x, hx, hxi, hxj⟩ := hMeet
    have hnot := (uniformGrid_shared_face_in_first_time_slab hε x (hTime x hx) i z hzi hxi hxj).1
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hnot
    subst i
    let k : Fin L := ⟨(z j.castSucc).val - 1, by omega⟩
    let zm := Function.update z j.castSucc k
    have hpAxes : (index zm hm).val.val.1 = (index z hz).val.val.1 :=
      (hIndexAxes zm hm).trans (hIndexAxes z hz).symm
    have hpOrigin : (index z hz).val.val.2 = (index zm hm).val.val.2 +
        ε • EuclideanSpace.single ((index zm hm).val.val.1 j) (1 : ℝ) := by
      rw [hIndexOrigin, hIndexOrigin, hIndexAxes]
      have hk : (k.val : ℝ) + 1 = (z j.castSucc).val := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ (z j.castSucc).val)
      ext a
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
        Function.Embedding.refl_apply]
      by_cases ha : a = j
      · subst a
        simp only [zm, Function.update_self, ite_true, smul_eq_mul]
        nlinarith
      · have hac : a.castSucc ≠ j.castSucc := by intro h; exact ha (Fin.castSucc_inj.mp h)
        simp only [zm, Function.update_of_ne hac, if_neg ha, smul_eq_mul, mul_zero, add_zero]
    have hh := canonical_neighbor_prism_face_maps_eq grid offset ε child frame hAxes hOrigin hSlot hSurv
      (index zm hm) (index z hz) j hpAxes hpOrigin (V (n + 1))
    simpa only [g, Fin.lastCases_castSucc] using hh.2.2
  obtain ⟨W, D, hFull, hEnergy, hPoint, hProp⟩ := memW12_uniform_grid_active_unit_mesh
    hε Ω hΩsub active hActive (fun z hz => V (n + 2) (index z hz))
    (fun z hz => DV (n + 2) (index z hz)) g (fun z hz => hW (index z hz))
    M hM (fun z hz => hBound (index z hz)) (fun z hz => H (index z hz))
    (fun z hz => hRaw (index z hz)) hEnd hFace
  refine ⟨W, D, hFull, ?_, hPoint, hProp⟩
  have hPower : (((n + 1 + 2 : ℕ) : ℤ) - 2) = (n + 1 : ℕ) := by omega
  simpa only [hPower, zpow_natCast] using hEnergy

end StratificationTheory
