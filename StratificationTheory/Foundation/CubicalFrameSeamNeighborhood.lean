module

public import StratificationTheory.Foundation.CubicalLateralPatch

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Original compatible face curves in one actual finite frame produce a
weak graph for the radial map on an open neighborhood of its seam point. -/
theorem exists_cubical_frame_seam_neighborhood {n q : ℕ} (hn : 2 ≤ n + 1)
    (G : Domain ((n + 1) + 1) → Ambient q)
    (Df : (Fin ((n + 1) + 1) × Bool) → Domain (n + 1) → Gradient (n + 1) q)
    (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool)
    (x : Domain ((n + 1) + 1)) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let A := cubicalSignedPermutation ((n + 1) + 1) p s
    let A₀ := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
    let B : OpenDomain (n + 1) :=
      ⟨⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let S : OpenDomain n :=
      ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let f : (Fin ((n + 1) + 1) × Bool) → Domain (n + 1) → Ambient q := fun j z =>
      G (cubicalSignedFaceIsometry (n + 1) j.1 j.2 (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1)))
    let w₀ : Domain (n + 1) → Ambient q := fun z => G (A (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1)))
    let w₁ : Domain (n + 1) → Ambient q := fun z => G (A (A₀ (e.symm (z, EuclideanSpace.single (0 : Fin 1) 1))))
    (∀ j, MemW12 B (f j) (Df j)) →
    ∀ (H₀ H₁ : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S.val))),
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun z : Domain n => w₀ (b.symm (z, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S.val),
        H₀ ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun z => w₀ (b.symm (z, EuclideanSpace.single (0 : Fin 1) t)))) →
    (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun z : Domain n => w₁ (b.symm (z, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S.val),
        H₁ ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun z => w₁ (b.symm (z, EuclideanSpace.single (0 : Fin 1) t)))) →
    H₀ ⟨1, by norm_num, le_rfl⟩ = H₁ ⟨1, by norm_num, le_rfl⟩ →
    0 < (e (A.symm x)).2 0 → (e (A.symm x)).2 0 < 1 →
    (b (e (A.symm x)).1).2 0 = (e (A.symm x)).2 0 →
    (∀ k : Fin n, |(b (e (A.symm x)).1).1 k| < (e (A.symm x)).2 0) →
    ∃ (V : OpenDomain ((n + 1) + 1)) (D : Domain ((n + 1) + 1) → Gradient ((n + 1) + 1) q),
      x ∈ V.val ∧ MemW12 V (fun y => G (‖WithLp.ofLp y‖⁻¹ • y)) D := by
  intro b e A A₀ B S f w₀ w₁ hface H₀ H₁ hSlices₀ hSlices₁ hMatch ht ht1 htie hstrict
  obtain ⟨b₀, b₁, z, U, hb₀, hbb, hb₁, hΓz, hzU, hU, hImage⟩ :=
    exists_native_cone_lateral_patch (A.symm x) ht ht1 htie hstrict
  obtain ⟨Q, hQ, hGlue⟩ := exists_cubical_frame_seam_weak_pair hn G Df p s
    hface H₀ H₁ hSlices₀ hSlices₁ hMatch b₀ b₁ hb₀ hbb hb₁
  obtain ⟨ε, hε, D, hW⟩ := hGlue U hU hImage
  let V : OpenDomain ((n + 1) + 1) :=
    ⟨Q.symm ⁻¹' {y | (e y).1 ∈ U.val ∧ (e y).2 0 ∈ Ioo (-ε) ε},
      ((U.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))).preimage Q.symm.continuous⟩
  have hxQ : Q (e.symm (z, EuclideanSpace.single (0 : Fin 1) 0)) = x := by
    rw [hQ, zero_smul, add_zero, hΓz, A.apply_symm_apply]
  have hQx : Q.symm x = e.symm (z, EuclideanSpace.single (0 : Fin 1) 0) :=
    Q.symm_apply_eq.mpr hxQ.symm
  refine ⟨V, D, ?_, hW⟩
  change (e (Q.symm x)).1 ∈ U.val ∧ (e (Q.symm x)).2 0 ∈ Ioo (-ε) ε
  rw [hQx, e.apply_symm_apply]
  exact ⟨hzU, by simpa using (show -ε < (0 : ℝ) ∧ 0 < ε by constructor <;> linarith)⟩

end StratificationTheory
