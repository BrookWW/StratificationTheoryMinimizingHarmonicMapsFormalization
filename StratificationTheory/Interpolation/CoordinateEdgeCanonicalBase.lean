module
public import StratificationTheory.Interpolation.QualifiedCoordinateEdgeUnitMaps
public import StratificationTheory.Foundation.RawVertexUnitChordData
public import StratificationTheory.Foundation.UnitSquareCoordinateSwap

/-!
# Canonical coordinate traces of the original edge base

The original line qualifications produce the actual square connector with
all canonical native coordinate curves. Its spatial endpoints are the
same global raw vertex chords and its time endpoints are the original edges.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original line data produce the canonical complete edge-prism base. -/
theorem coordinate_edge_canonical_base_of_original_line_data {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (y : Domain (n + 1))
    (a b ε : ℝ) (hε : 0 < ε)
    (u : Fin 2 → Domain (n + 1) → Ambient q)
    (Du : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    {N : Set (Ambient q)} (hN : IsClosed N) :
    let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
    let e₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := p (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    let β := (e₀ (Q.symm y)).1
    let rep := fun l => coordinatePermACLRepresentative p a b (u l) (Du l)
    let line := fun t => Q (e₀.symm (β, EuclideanSpace.single (0 : Fin 1) t))
    a ≤ y j → y j + ε ≤ b →
    (∀ l, MemLp (fun t => u l (line t)) 2 (volume.restrict (Ioo a b))) →
    (∀ l, MemLp (fun t => Du l (line t) j) 2 (volume.restrict (Ioo a b))) →
    (∀ l, (fun t => rep l (line t)) =ᵐ[volume.restrict (Ioo a b)] (fun t => u l (line t))) →
    (∀ l t, t ∈ Icc a b → rep l (line t) ∈ N) →
    (∀ l s, s ∈ Icc a b → ∀ t, t ∈ Icc a b →
      rep l (line t) - rep l (line s) = ∫ r in s..t, Du l (line r) j) →
    (∀ l, rep l y = u l y) → (∀ l, rep l (y + ε • v) = u l (y + ε • v)) →
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let B : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let C : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let edge := fun (l : Fin 2) (x : Domain 1) => u l (y + (ε / 2 + (ε / 2) * x 0) • v)
    let V := coordinateEdgeUnitMap p a b ε u Du y
    let DV := coordinateEdgeUnitGradient p a b ε u Du y
    let D := ∫ s in Ioo (0 : ℝ) ε, ‖u 0 (y + s • v) - u 1 (y + s • v)‖ ^ 2
    let E := ∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2 + ‖Du 1 (y + s • v) j‖ ^ 2
    let face := fun (i : Fin 2) (side : Bool) => if i = 0 then
      rawVertexUnitChord u (y + (if side then ε else 0) • v) else edge (if side then 1 else 0)
    MemW12 B V DV ∧
      (∫ z in B.val, hsNormSq (DV z)) ≤
        (ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖Du 0 (y + s • v) j‖ ^ 2) +
          ∫ s in Ioo (0 : ℝ) ε, ‖Du 1 (y + s • v) j‖ ^ 2) + ε⁻¹ * D ∧
      (∀ z : Domain 2, (∀ j, z j ∈ Icc (-1 : ℝ) 1) →
        (infDist (V z) N) ^ 2 ≤ D / ε + Real.sqrt (2 * D * E)) ∧
      ∃ K : Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => V (cubicalSignedFaceIsometry 1 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
            K i ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp
              (fun x => V (cubicalSignedFaceIsometry 1 i true
                (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i side,
          (K i ⟨if side then 1 else -1, by cases side <;> norm_num,
            by cases side <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C] face i side := by
  intro Q e₀ j v β rep line ha hb hU hD hAE hValues hInc hRaw₀ hRawε
    e B C edge V DV D E face
  obtain ⟨hW, hEnergy, hDist, HT, HS, hHT, hHT₀, hHT₁, hHS, hHS₀, hHS₁⟩ :=
    coordinate_edge_unit_maps_of_original_line_data p y a b ε hε u Du hN
      ha hb hU hD hAE hValues hInc hRaw₀ hRawε
  have hSwap (x : Domain 1) (t : ℝ) :
      cubicalSignedFaceIsometry 1 (0 : Fin 2) true
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
          e.symm (EuclideanSpace.single (0 : Fin 1) t, x) := unit_square_coordinate_swap.2 x t
  have hId (z : Domain 2) : cubicalSignedFaceIsometry 1 (1 : Fin 2) true z = z := by
    ext i
    have h := cubicalSignedFaceIsometry_apply (1 : Fin 2) true z i
    simpa only [show Fin.last 1 = (1 : Fin 2) by decide, Equiv.swap_self, Equiv.refl_apply, ite_true, ite_self] using h
  let K : Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)) :=
    fun i => if i = 0 then HS else HT
  refine ⟨hW, hEnergy, hDist, K, ?_, ?_⟩
  · intro i
    fin_cases i
    · change ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => V (cubicalSignedFaceIsometry 1 (0 : Fin 2) true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          HS ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (cubicalSignedFaceIsometry 1 (0 : Fin 2) true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))
      simp_rw [hSwap]
      with_reducible exact hHS
    · change ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => V (cubicalSignedFaceIsometry 1 (1 : Fin 2) true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          HT ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V (cubicalSignedFaceIsometry 1 (1 : Fin 2) true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))
      simp_rw [hId]
      with_reducible exact hHT
  · intro i side
    fin_cases i <;> cases side
    · obtain ⟨hs, heq⟩ := hHS₀
      change (HS ⟨-1, le_rfl, by norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C]
        rawVertexUnitChord u (y + 0 • v)
      rw [heq]
      rw [← coordinateEdgeRawUnitChord_eq_rawVertexUnitChord p hε u y 0]
      exact hs.coeFn_toLp
    · obtain ⟨hs, heq⟩ := hHS₁
      change (HS ⟨1, by norm_num, le_rfl⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C]
        rawVertexUnitChord u (y + ε • v)
      rw [heq]
      rw [← coordinateEdgeRawUnitChord_eq_rawVertexUnitChord p hε u y ε]
      exact hs.coeFn_toLp
    · obtain ⟨hs, heq⟩ := hHT₀
      change (HT ⟨-1, le_rfl, by norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C] edge 0
      rw [heq]
      exact hs.coeFn_toLp
    · obtain ⟨hs, heq⟩ := hHT₁
      change (HT ⟨1, by norm_num, le_rfl⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C] edge 1
      rw [heq]
      exact hs.coeFn_toLp

end StratificationTheory
