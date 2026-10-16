module

public import StratificationTheory.Foundation.TranslatedCubeL2TraceDenormalization
public import StratificationTheory.Foundation.TranslatedCubeFaceCoordinates
public import StratificationTheory.Foundation.UniformGridCarriers

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- One original unit-cube pair and its original coordinate curves produce
the same physical mesh-cell pair, its exact native energy and every actual
physical coordinate curve with both original transformed face classes. -/
theorem uniformGrid_unit_cell_pair_and_coordinate_traces {n N q : ℕ}
    {ε : ℝ} (hε : 0 < ε) (z : Fin (n + 1) → Fin N)
    (V : Domain (n + 1) → Ambient q) (DV : Domain (n + 1) → Gradient (n + 1) q)
    (g : Fin (n + 1) → Bool → Domain n → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let S := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let lo : Domain (n + 1) := WithLp.toLp 2 (fun i => ((z i).val : ℝ) * ε)
    let a : Domain (n + 1) := lo + WithLp.toLp 2 (fun _ => ε / 2)
    let F : Domain (n + 1) → Domain (n + 1) := fun y => (ε / 2)⁻¹ • (y - a)
    let W := V ∘ F
    let D : Domain (n + 1) → Gradient (n + 1) q := fun y j => (ε / 2)⁻¹ • DV (F y) j
    MemW12 B V DV →
    ∀ K : Fin (n + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => V (cubicalSignedFaceIsometry n i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (cubicalSignedFaceIsometry n i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ i positive,
      (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict S] g i positive) →
    MemW12 (uniformGridCell (n + 1) N ε z) W D ∧
      (∫ y in (uniformGridCell (n + 1) N ε z).val, hsNormSq (D y)) =
        (ε / 2) ^ (((n + 1 : ℕ) : ℤ) - 2) * ∫ x in B.val, hsNormSq (DV x) ∧
      (∀ i : Fin (n + 1),
        let U := uniformGridTransverseCell n N ε i z
        let Q := cubicalSignedFaceIsometry n i true
        let l : Domain n := WithLp.toLp 2 (fun k => lo ((Equiv.swap (Fin.last n) i) k.castSucc))
        let Fi : Domain n → Domain n := fun x => (ε / 2)⁻¹ • (x - (l + WithLp.toLp 2 (fun _ => ε / 2)))
        ∃ H : C(Icc (lo i) (lo i + ε), Lp (Ambient q) 2 (volume.restrict U.val)),
          (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (lo i) (lo i + ε),
            ∃ hs : MemLp (fun x : Domain n => W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U.val),
              H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
          ((H ⟨lo i, le_rfl, by linarith⟩ : Domain n → Ambient q) =ᵐ[volume.restrict U.val] (g i false ∘ Fi)) ∧
          ((H ⟨lo i + ε, by linarith, le_rfl⟩ : Domain n → Ambient q) =ᵐ[volume.restrict U.val] (g i true ∘ Fi))) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (V x)) →
        ∀ᵐ y ∂volume.restrict (uniformGridCell (n + 1) N ε z).val, P (W y) := by
  intro e S B lo a F W D hV K hK hEnd
  let T : OpenDomain (n + 1) :=
    ⟨⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (lo j) (lo j + ε),
      isOpen_iInter_of_finite (fun j : Fin (n + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
  have hT : T = uniformGridCell (n + 1) N ε z := by
    apply Subtype.ext
    ext y
    rw [mem_uniformGridCell_iff]
    simp only [T, mem_iInter, mem_preimage]
    apply forall_congr'
    intro j
    have hHi : lo j + ε = (((z j).val : ℝ) + 1) * ε := by change ((z j).val : ℝ) * ε + ε = _; ring
    rw [hHi]
    rfl
  obtain ⟨hW, hEnergy, hProp⟩ := memW12_translated_cube_denormalization_energy hε lo V DV hV
  change MemW12 T W D at hW
  change (∫ y in T.val, hsNormSq (D y)) = _ at hEnergy
  change ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict B.val, P (V x)) →
    ∀ᵐ y ∂volume.restrict T.val, P (W y) at hProp
  rw [hT] at hW hEnergy hProp
  refine ⟨hW, hEnergy, ?_, hProp⟩
  intro i U Q l Fi
  have hU : U.val = ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (l k) (l k + ε) := by
    ext x
    rw [mem_uniformGridTransverseCell_iff]
    simp only [mem_iInter, mem_preimage]
    apply forall_congr'
    intro k
    have hHi : l k + ε =
        (((z ((Equiv.swap (Fin.last n) i) k.castSucc)).val : ℝ) + 1) * ε := by
      change ((z ((Equiv.swap (Fin.last n) i) k.castSucc)).val : ℝ) * ε + ε = _
      ring
    rw [hHi]
    rfl
  have hCurve := exists_translated_cube_L2_trace_denormalization hε l (lo i)
    (fun p : Domain n × ℝ => V (Q (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))))
    (g i false) (g i true) (K i) (hK i) (hEnd i false) (hEnd i true)
  rw [← hU] at hCurve
  obtain ⟨H, hH, hH₀, hH₁, _hUnique⟩ := hCurve
  refine ⟨H, ?_, hH₀, hH₁⟩
  have hRaw (x : Domain n) (t : ℝ) : W (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) =
      V (Q (e.symm (Fi x, EuclideanSpace.single (0 : Fin 1) ((t - lo i) / (ε / 2) - 1)))) :=
    congrArg V (inverse_translated_cube_face_coordinates hε lo i x t)
  simpa only [hRaw] using hH

end StratificationTheory
