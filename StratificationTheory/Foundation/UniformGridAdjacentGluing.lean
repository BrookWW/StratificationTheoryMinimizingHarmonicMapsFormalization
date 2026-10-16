module

public import StratificationTheory.Foundation.UniformGridCellCoordinates
public import StratificationTheory.Foundation.IsometricCoordinateTraceGluing

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Two actual adjacent uniform cells glue across their original common
native L2 trace class, producing a genuine graph on the open two-cell normal
rectangle, including the shared physical face. -/
theorem uniformGrid_adjacent_cell_gluing {n N q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin (n + 1)) (z : Fin (n + 1) → Fin N) (hzi : 0 < (z i).val)
    (u v : Domain (n + 1) → Ambient q) (Du Dv : Domain (n + 1) → Gradient (n + 1) q) :
    let k : Fin N := ⟨(z i).val - 1, by omega⟩
    let zm := Function.update z i k
    let U := uniformGridTransverseCell n N ε i z
    let Q := cubicalSignedFaceIsometry n i true
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let a := (k.val : ℝ) * ε
    let b := ((z i).val : ℝ) * ε
    let c := (((z i).val : ℝ) + 1) * ε
    let R := fun l r : ℝ => (⟨Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo l r},
      ((U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))).preimage Q.symm.continuous⟩ : OpenDomain (n + 1))
    MemW12 (uniformGridCell (n + 1) N ε zm) u Du →
    MemW12 (uniformGridCell (n + 1) N ε z) v Dv →
    ∀ (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
      (K : C(Icc b c, Lp (Ambient q) 2 (volume.restrict U.val))),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x : Domain n => u (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U.val),
        H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b c,
      ∃ hs : MemLp (fun x : Domain n => v (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U.val),
        K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => v (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ hab : a < b, ∀ hbc : b < c, H ⟨b, hab.le, le_rfl⟩ = K ⟨b, le_rfl, hbc.le⟩) →
    MemW12 (R a c) (fun y => if (e (Q.symm y)).2 0 < b then u y else v y)
      (fun y j => if (e (Q.symm y)).2 0 < b then Du y j else Dv y j) ∧
    (uniformGridCell (n + 1) N ε zm).val = (R a b).val ∧
    (uniformGridCell (n + 1) N ε z).val = (R b c).val := by
  intro k zm U Q e a b c R hu hv H K hH hK hMatch
  have hk : (k.val : ℝ) + 1 = (z i).val := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ (z i).val)
  have hab : a < b := by dsimp only [a, b]; nlinarith
  have hbc : b < c := by dsimp only [b, c]; nlinarith
  have hMinus : (uniformGridCell (n + 1) N ε zm).val = (R a b).val := by
    rw [uniformGridCell_as_face_rectangle n N ε i zm]
    change Q.symm ⁻¹' {y | (e y).1 ∈ (uniformGridTransverseCell n N ε i (Function.update z i k)).val ∧
      (e y).2 0 ∈ Ioo (((Function.update z i k) i).val * ε)
        ((((Function.update z i k) i).val + (1 : ℝ)) * ε)} = _
    rw [uniformGridTransverseCell_update_normal, Function.update_self, hk]
  have hPlus : (uniformGridCell (n + 1) N ε z).val = (R b c).val :=
    uniformGridCell_as_face_rectangle n N ε i z
  have hu' : MemW12 (R a b) u Du := by
    have hDomain : uniformGridCell (n + 1) N ε zm = R a b := Subtype.ext hMinus
    rwa [← hDomain]
  have hv' : MemW12 (R b c) v Dv := by
    have hDomain : uniformGridCell (n + 1) N ε z = R b c := Subtype.ext hPlus
    rwa [← hDomain]
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val) :=
    isFiniteMeasure_restrict.mpr (volume_uniformGridTransverseCell_ne_top n N ε i z)
  have hGlue := memW12_isometric_piecewise_of_matching_L2_traces U hab hbc Q u v Du Dv
    hu' hv' H K hH hK (hMatch hab hbc)
  exact ⟨hGlue.1, hMinus, hPlus⟩

end StratificationTheory
