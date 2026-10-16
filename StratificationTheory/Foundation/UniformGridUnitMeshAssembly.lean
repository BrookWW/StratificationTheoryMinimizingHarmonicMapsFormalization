module

public import StratificationTheory.Foundation.UniformGridOpenSubdomainAssembly
public import StratificationTheory.Foundation.UniformGridUnitCellTransport
public import StratificationTheory.Foundation.UniformGridTransverseNormalization

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Original unit-cell weak maps and their original coordinate traces with
common unit face classes produce the actual physical piecewise weak map
on any open mesh subdomain. All physical face trace qualifications and
their common classes are generated internally by the same similarities. -/
theorem memW12_uniform_grid_unit_mesh_on_open_subdomain {n N q : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (Ω : OpenDomain (n + 2)) (hΩsub : Ω.val ⊆ (uniformGridBox (n + 2) N ε).val)
    (V : (Fin (n + 2) → Fin N) → Domain (n + 2) → Ambient q)
    (DV : (Fin (n + 2) → Fin N) → Domain (n + 2) → Gradient (n + 2) q)
    (g : (Fin (n + 2) → Fin N) → Fin (n + 2) → Bool → Domain (n + 1) → Ambient q) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let S := ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain (n + 2) :=
      ⟨⋂ j : Fin (n + 2), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin (n + 2) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let lo : (Fin (n + 2) → Fin N) → Domain (n + 2) := fun z => WithLp.toLp 2 (fun j => ((z j).val : ℝ) * ε)
    let T : (Fin (n + 2) → Fin N) → Domain (n + 2) → Domain (n + 2) := fun z x =>
      (ε / 2)⁻¹ • (x - (lo z + WithLp.toLp 2 (fun _ => ε / 2)))
    let u := fun z => V z ∘ T z
    let A := fun z x j => (ε / 2)⁻¹ • DV z (T z x) j
    (∀ z, MemW12 B (V z) (DV z)) →
    ∀ Bnd : ℝ, (∀ z, ∀ᵐ x ∂volume.restrict B.val, ‖V z x‖ ≤ Bnd) →
    ∀ K : (Fin (n + 2) → Fin N) → Fin (n + 2) →
      C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ z i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain (n + 1) => V z (cubicalSignedFaceIsometry (n + 1) i true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K z i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V z (cubicalSignedFaceIsometry (n + 1) i true
          (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ z i positive,
      (K z i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 1) → Ambient q)
        =ᵐ[volume.restrict S] g z i positive) →
    (∀ (i : Fin (n + 2)) (z : Fin (n + 2) → Fin N) (hzi : 0 < (z i).val),
      (∃ x ∈ Ω.val, x i = ((z i).val : ℝ) * ε ∧
        ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε)) →
      let k : Fin N := ⟨(z i).val - 1, by omega⟩
      g (Function.update z i k) i true =ᵐ[volume.restrict S] g z i false) →
    let C : (Fin (n + 2) → Fin N) → OpenDomain (n + 2) := fun z =>
      ⟨Ω.val ∩ (uniformGridCell (n + 2) N ε z).val,
        Ω.property.inter (uniformGridCell (n + 2) N ε z).property⟩
    let W : Domain (n + 2) → Ambient q := fun x => ∑ z : Fin (n + 2) → Fin N, (C z).val.indicator (u z) x
    let D : Domain (n + 2) → Gradient (n + 2) q := fun x => ∑ z : Fin (n + 2) → Fin N, (C z).val.indicator (A z) x
    MemW12 Ω W D ∧
      (∫ x in Ω.val, hsNormSq (D x)) ≤
        (ε / 2) ^ (((n + 2 : ℕ) : ℤ) - 2) * ∑ z : Fin (n + 2) → Fin N,
          ∫ y in B.val, hsNormSq (DV z y) ∧
      (∀ z x, x ∈ (C z).val → W x = V z (T z x) ∧ D x = A z x) ∧
      ∀ P : Ambient q → Prop, (∀ z, (C z).val.Nonempty → ∀ᵐ x ∂volume.restrict B.val, P (V z x)) →
        ∀ᵐ x ∂volume.restrict Ω.val, P (W x) := by
  classical
  intro e S B lo T u A hV Bnd hBound K hK hEnd hCompat C W D
  have hData (z : Fin (n + 2) → Fin N) := uniformGrid_unit_cell_pair_and_coordinate_traces
    hε z (V z) (DV z) (g z) (hV z) (K z) (hK z) (hEnd z)
  have hCell (z : Fin (n + 2) → Fin N) : MemW12 (uniformGridCell (n + 2) N ε z) (u z) (A z) := (hData z).1
  have hBoundCell (z : Fin (n + 2) → Fin N) : ∀ᵐ x ∂volume.restrict (uniformGridCell (n + 2) N ε z).val,
      ‖u z x‖ ≤ Bnd := (hData z).2.2.2 (fun y => ‖y‖ ≤ Bnd) (hBound z)
  have hTrace : ∀ (i : Fin (n + 2)) (z : Fin (n + 2) → Fin N) (hzi : 0 < (z i).val),
      (∃ x ∈ Ω.val, x i = ((z i).val : ℝ) * ε ∧
        ∀ j, j ≠ i → x j ∈ Ioo ((z j).val * ε) (((z j).val + (1 : ℝ)) * ε)) →
      let k : Fin N := ⟨(z i).val - 1, by omega⟩
      let zm := Function.update z i k
      let U := uniformGridTransverseCell (n + 1) N ε i z
      let Q := cubicalSignedFaceIsometry (n + 1) i true
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
      let a := (k.val : ℝ) * ε
      let b := ((z i).val : ℝ) * ε
      let c := (((z i).val : ℝ) + 1) * ε
      ∃ (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
        (K : C(Icc b c, Lp (Ambient q) 2 (volume.restrict U.val))),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
          ∃ hs : MemLp (fun x : Domain (n + 1) => u zm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U.val),
            H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u zm (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b c,
          ∃ hs : MemLp (fun x : Domain (n + 1) => u z (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U.val),
            K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u z (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ hab : a < b, ∀ hbc : b < c, H ⟨b, hab.le, le_rfl⟩ = K ⟨b, le_rfl, hbc.le⟩ := by
    intro i z hzi hMeet
    let k : Fin N := ⟨(z i).val - 1, by omega⟩
    let zm := Function.update z i k
    let U := uniformGridTransverseCell (n + 1) N ε i z
    let Q := cubicalSignedFaceIsometry (n + 1) i true
    let l : Domain (n + 1) := WithLp.toLp 2 (fun j => ((z ((Equiv.swap (Fin.last (n + 1)) i) j.castSucc)).val : ℝ) * ε)
    let Fi : Domain (n + 1) → Domain (n + 1) := fun x => (ε / 2)⁻¹ • (x - (l + WithLp.toLp 2 (fun _ => ε / 2)))
    let a := (k.val : ℝ) * ε
    let b := ((z i).val : ℝ) * ε
    let c := (((z i).val : ℝ) + 1) * ε
    have hk : (k.val : ℝ) + 1 = (z i).val := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ (z i).val)
    have ha : lo zm i = a := by simp only [lo, zm, Function.update_self]; rfl
    have hb : lo z i = b := rfl
    have hab : a + ε = b := by dsimp only [a, b]; nlinarith
    have hbc : b + ε = c := by dsimp only [b, c]; ring
    have hOrigin : (WithLp.toLp 2 (fun j : Fin (n + 1) =>
      lo zm ((Equiv.swap (Fin.last (n + 1)) i) j.castSucc)) : Domain (n + 1)) = l :=
      uniformGrid_transverse_origin_update ε i z k
    have hUm : uniformGridTransverseCell (n + 1) N ε i zm = U :=
      uniformGridTransverseCell_update_normal ε i z k
    let Data := fun (a₀ b₀ : ℝ) (U₀ : OpenDomain (n + 1))
      (f₀ : Domain (n + 2) → Ambient q) (g₀ g₁ : Domain (n + 1) → Ambient q) =>
      ∃ H : C(Icc a₀ b₀, Lp (Ambient q) 2 (volume.restrict U₀.val)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a₀ b₀,
          ∃ hs : MemLp (fun x => f₀ (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict U₀.val),
            H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f₀ (Q (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ h : a₀ ≤ b₀,
          ((H ⟨a₀, le_rfl, h⟩ : Domain (n + 1) → Ambient q) =ᵐ[volume.restrict U₀.val] g₀) ∧
          ((H ⟨b₀, h, le_rfl⟩ : Domain (n + 1) → Ambient q) =ᵐ[volume.restrict U₀.val] g₁)
    let lm : Domain (n + 1) := WithLp.toLp 2 (fun j => lo zm ((Equiv.swap (Fin.last (n + 1)) i) j.castSucc))
    let Fm : Domain (n + 1) → Domain (n + 1) := fun x => (ε / 2)⁻¹ • (x - (lm + WithLp.toLp 2 (fun _ => ε / 2)))
    have hFm : Fm = Fi := by
      funext x
      change (ε / 2)⁻¹ • (x - (lm + _)) = (ε / 2)⁻¹ • (x - (l + _))
      rw [show lm = l from hOrigin]
    have hM : Data (lo zm i) (lo zm i + ε) (uniformGridTransverseCell (n + 1) N ε i zm)
        (u zm) (g zm i false ∘ Fm) (g zm i true ∘ Fm) := by
      obtain ⟨H, hH, hH₀, hH₁⟩ := (hData zm).2.2.1 i
      exact ⟨H, hH, fun _ => ⟨hH₀, hH₁⟩⟩
    have hP : Data (lo z i) (lo z i + ε) U (u z) (g z i false ∘ Fi) (g z i true ∘ Fi) := by
      obtain ⟨H, hH, hH₀, hH₁⟩ := (hData z).2.2.1 i
      exact ⟨H, hH, fun _ => ⟨hH₀, hH₁⟩⟩
    rw [hFm, hUm, ha, hab] at hM
    rw [hb, hbc] at hP
    obtain ⟨H, hH, hHEnd⟩ := hM
    obtain ⟨J, hJ, hJEnd⟩ := hP
    have hShared : (g zm i true ∘ Fi) =ᵐ[volume.restrict U.val] (g z i false ∘ Fi) :=
      ae_uniformGrid_transverse_inverse_property hε i z (fun x => g zm i true x = g z i false x)
        (hCompat i z hzi hMeet)
    refine ⟨H, J, hH, hJ, ?_⟩
    intro hab' hbc'
    apply Lp.ext
    exact (hHEnd hab'.le).2.trans (hShared.trans (hJEnd hbc'.le).1.symm)
  obtain ⟨hFull, hPoint, hEnergy, hProp⟩ := memW12_uniform_grid_piecewise_on_open_subdomain
    hε Ω hΩsub u A hCell Bnd hBoundCell hTrace
  refine ⟨hFull, ?_, hPoint, ?_⟩
  · rw [hEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    have hInt := (hCell z).integrable_hsNormSq
    calc
      (∫ x in (C z).val, hsNormSq (A z x)) ≤
          ∫ x in (uniformGridCell (n + 2) N ε z).val, hsNormSq (A z x) :=
        setIntegral_mono_set hInt (Eventually.of_forall fun x => hsNormSq_nonneg (A z x))
          (Eventually.of_forall fun _ hx => hx.2)
      _ = _ := (hData z).2.1
  · intro P hP
    apply hProp P
    intro z
    by_cases hz : (C z).val.Nonempty
    · exact ae_restrict_of_ae_restrict_of_subset (fun _ hx => hx.2) ((hData z).2.2.2 P (hP z hz))
    · filter_upwards [ae_restrict_mem (C z).property.measurableSet] with x hx
      exact False.elim (hz ⟨x, hx⟩)

end StratificationTheory
