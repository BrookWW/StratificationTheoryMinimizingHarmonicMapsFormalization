module

public import StratificationTheory.Foundation.CubicalBoundaryFrameCurve
public import StratificationTheory.Foundation.CubicalSignedPermutationComposition

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StratificationTheory

/-- Literal common original edge classes make the two adjacent face curves
compatible in every finite ambient signed frame. All frame curves are
constructed from the original coordinate curves. -/
theorem exists_cubical_compatible_frame_curves_of_coordinate_traces {n q : ℕ}
    (f : (Fin ((n + 1) + 1) × Bool) → Domain (n + 1) → Ambient q)
    (G E : Domain ((n + 1) + 1) → Ambient q) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let B := ⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let S := ⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let Q := fun j : Fin ((n + 1) + 1) × Bool => cubicalSignedFaceIsometry (n + 1) j.1 j.2
    (∀ j x, x ∈ B → G (Q j (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = f j x) →
    ∀ K : (Fin ((n + 1) + 1) × Bool) → Fin (n + 1) →
      C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ j i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x : Domain n => f j (cubicalSignedFaceIsometry n i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K j i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f j (cubicalSignedFaceIsometry n i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ j (i : Fin (n + 1)) (positive : Bool),
      (K j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain n → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (Q j (e.symm
          (cubicalSignedFaceIsometry n i positive (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1))))) →
    let A₀ := cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true
    let w : Equiv.Perm (Fin ((n + 1) + 1)) → (Fin ((n + 1) + 1) → Bool) → Bool → Domain (n + 1) → Ambient q :=
      fun p s side x => G (cubicalSignedPermutation ((n + 1) + 1) p s
        (if side then A₀ (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))
          else e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))
    ∃ H : Equiv.Perm (Fin ((n + 1) + 1)) → (Fin ((n + 1) + 1) → Bool) → Bool →
      C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
      (∀ p s side, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x : Domain n => w p s side
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict S),
          H p s side ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => w p s side (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      ∀ p s, H p s false ⟨1, by norm_num, le_rfl⟩ = H p s true ⟨1, by norm_num, le_rfl⟩ := by
  classical
  intro b e B S Q hG K hK hEnd A₀ w
  have hEach := exists_cubical_boundary_frame_curve f G E hG K hK hEnd
  choose J hJ hJEnd using hEach
  let σ := Equiv.swap (Fin.last (n + 1)) (Fin.last n).castSucc
  have hComposition (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool) :
      cubicalSignedPermutation ((n + 1) + 1) (σ.trans p) (fun k => s (σ k)) =
        A₀.trans (cubicalSignedPermutation ((n + 1) + 1) p s) := by
    change _ = (cubicalSignedFaceIsometry (n + 1) (Fin.last n).castSucc true).trans _
    rw [cubicalSignedFaceIsometry_as_signedPermutation, cubicalSignedPermutation_compose]
    simp only [ite_self, ite_true]
    rfl
  let H := fun (p : Equiv.Perm (Fin ((n + 1) + 1))) (s : Fin ((n + 1) + 1) → Bool) (side : Bool) =>
    if side then J (σ.trans p) (fun k => s (σ k)) else J p s
  have hFix (x : Domain n) :
      A₀ (e.symm (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1), EuclideanSpace.single (0 : Fin 1) 1)) =
        e.symm (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1), EuclideanSpace.single (0 : Fin 1) 1) := by
    let y := e.symm (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1), EuclideanSpace.single (0 : Fin 1) 1)
    have hLast : y (Fin.last (n + 1)) = 1 := by
      change (e y).2 0 = 1
      simp only [y, e.apply_symm_apply, PiLp.single_apply, ite_true]
    have hPen : y (Fin.last n).castSucc = 1 := by
      change (b (e y).1).2 0 = 1
      simp only [y, e.apply_symm_apply, b.apply_symm_apply, PiLp.single_apply, ite_true]
    ext k
    have h := cubicalSignedFaceIsometry_apply (Fin.last n).castSucc true y (σ k)
    rw [Equiv.swap_apply_self] at h
    simp only [ite_true, ite_self] at h
    rw [h]
    change y (σ k) = y k
    by_cases hk : k = Fin.last (n + 1)
    · subst k
      simp only [σ, Equiv.swap_apply_left, hLast, hPen]
    · by_cases hk' : k = (Fin.last n).castSucc
      · subst k
        simp only [σ, Equiv.swap_apply_right, hLast, hPen]
      · rw [show σ k = k from Equiv.swap_apply_of_ne_of_ne hk hk']
  refine ⟨H, ?_, ?_⟩
  · intro p s side
    cases side
    · exact hJ p s
    · simpa only [H, w, ite_true, hComposition, LinearIsometryEquiv.trans_apply] using
        hJ (σ.trans p) (fun k => s (σ k))
  · intro p s
    apply Lp.ext
    filter_upwards [hJEnd p s, hJEnd (σ.trans p) (fun k => s (σ k))] with x hx₀ hx₁
    change J p s ⟨1, by norm_num, le_rfl⟩ x = J (σ.trans p) (fun k => s (σ k)) ⟨1, by norm_num, le_rfl⟩ x
    rw [hx₀, hx₁, hComposition]
    change E (_) = E (cubicalSignedPermutation _ p s (A₀ _))
    rw [hFix]

end StratificationTheory
