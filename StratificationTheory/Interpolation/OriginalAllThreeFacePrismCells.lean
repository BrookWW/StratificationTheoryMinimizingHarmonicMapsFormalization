module

public import StratificationTheory.Interpolation.OriginalAllFacePrismGrid
public import StratificationTheory.Interpolation.OriginalSelectedThreeFaceUnitData
public import StratificationTheory.Interpolation.OriginalThreeCellPrismFromFirstPrisms
public import StratificationTheory.Foundation.CoordinateCellClosedFacets
public import StratificationTheory.Foundation.GridNeighborCoordinates
public import StratificationTheory.Foundation.FourPrismEnergyBudget
public import StratificationTheory.Foundation.NativeCoordinateCubeOpen
public import StratificationTheory.Foundation.OriginalCoordinateCellCarrier
public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology BigOperators ENNReal

namespace StratificationTheory

/-- One original ball pair supplies one lattice on which every contained
coordinate three-cell has a genuine four-dimensional prism connector.
The original three-face, square-face and edge energies remain explicit,
and all eight original face trace classes belong to the same weak pair.
The lower maps and columns are one global family on the actual physical
cell carrier, and each cell exposes its six exact physical indices. -/
theorem exists_original_ball_all_three_face_prism_cells {n q : ℕ}
    (w : Fin 2 → Domain (n + 3) → Ambient q)
    (Dw : Fin 2 → Domain (n + 3) → Gradient (n + 3) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 3)) ((n : ℝ) + 4)) (w l) (Dw l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 3)) ((n : ℝ) + 4)), w l x ∈ N)
    {ε : ℝ} (hε : 0 < ε) :
    let J₀ := (Fin 2 ↪ Fin (n + 3)) ⊕ Fin (n + 3)
    let J₁ := (k : Fin (n + 1)) × (Fin (k.val + 3) ↪ Fin (n + 3))
    let J := J₀ ⊕ J₁
    let d₀ : J₀ → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)
    let d : J → ℕ := Sum.elim d₀ (fun c => c.1.val + 3)
    let sampleFace₀ : (j : J₀) → (Fin (d₀ j) ↪ Fin (n + 3)) :=
      Sum.rec (motive := fun j : J₀ => Fin (d₀ j) ↪ Fin (n + 3)) (fun c => c)
        (fun i => (⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin (n + 3)))
    let sampleFace : (j : J) → (Fin (d j) ↪ Fin (n + 3)) :=
      Sum.rec (motive := fun j : J => Fin (d j) ↪ Fin (n + 3)) sampleFace₀ (fun c => c.2)
    let C := fun j : J => ⋂ k : Fin (d j), (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 3)) ((n : ℝ) + 4)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 3)) ((n : ℝ) + 4)).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Asample := fun (j : J) (y : Domain (n + 3)) (t : Domain (d j)) =>
      y + ∑ k : Fin (d j), t k • EuclideanSpace.single (sampleFace j k) (1 : ℝ)
    let grid := (Pi.basisFun ℝ (Fin (n + 3))).isUnitSMul
      (w := fun _j : Fin (n + 3) => ε) (fun _j => hε.ne'.isUnit)
    ∃ offset : Fin (n + 3) → ℝ, (∀ j, offset j ∈ Ico (0 : ℝ) ε) ∧
      (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
        Eraw (Asample j (WithLp.toLp 2 ((z : Fin (n + 3) → ℝ) + offset)) t)) ≤
          2 * (ENNReal.ofReal (ε ^ (n + 3)))⁻¹ *
            ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
              ((∫ x in ball (0 : Domain (n + 3)) ((n : ℝ) + 4), hsNormSq (Dw 0 x)) +
                ∫ x in ball (0 : Domain (n + 3)) ((n : ℝ) + 4), hsNormSq (Dw 1 x))) ∧
      (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
        Draw (Asample j (WithLp.toLp 2 ((z : Fin (n + 3) → ℝ) + offset)) t)) ≤
          2 * (ENNReal.ofReal (ε ^ (n + 3)))⁻¹ *
            ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
              (∫ x in ball (0 : Domain (n + 3)) ((n : ℝ) + 4), ‖w 0 x - w 1 x‖ ^ 2)) ∧
      ∃ (Vglobal : ↥(originalPhysicalCellCarrier 2 grid offset ε) → Domain 3 → Ambient q) (Dglobal : ↥(originalPhysicalCellCarrier 2 grid offset ε) → Domain 3 → Gradient 3 q),
      ∀ (coord : Fin 3 ↪ Fin (n + 3)) (z : Submodule.span ℤ (Set.range grid)),
      let y := WithLp.toLp 2 ((z : Fin (n + 3) → ℝ) + offset)
      let source := fun t : Domain 3 => y + ∑ k : Fin 3, t k • EuclideanSpace.single (coord k) (1 : ℝ)
      let P₃ : Set (Domain 3) := ⋂ k : Fin 3, (fun t : Domain 3 => t k) ⁻¹' Ioo (0 : ℝ) ε
      let P₂ : Set (Domain 2) := ⋂ k : Fin 2, (fun t : Domain 2 => t k) ⁻¹' Ioo (0 : ℝ) ε
      let B : OpenDomain 3 := ⟨⋂ k : Fin 3, (fun t : Domain 3 => t k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_native_coordinate_cube 3 (-1) 1⟩
      let Ω : OpenDomain 4 := ⟨⋂ k : Fin 4, (fun t : Domain 4 => t k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_native_coordinate_cube 4 (-1) 1⟩
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)
      let U := fun (side : Bool) (x : Domain 3) => w (if side then 1 else 0)
        (source (WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • x))
      let A := fun i : Fin 3 => cubicalSignedPermutation 3 (Equiv.swap (Fin.last 2) i) (fun _ => true)
      let E₃ := ∑ l : Fin 2, ∫ t in P₃, hsNormSq (fun k => Dw l (source t) (coord k))
      let pair := fun i : Fin 3 =>
        (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
      let origin := fun j : Fin 3 × Bool => y + (if j.2 then ε else 0) • EuclideanSpace.single (coord j.1) (1 : ℝ)
      let embed := fun (j : Fin 3 × Bool) (t : Domain 2) => origin j +
        t 0 • EuclideanSpace.single (pair j.1 0) (1 : ℝ) + t 1 • EuclideanSpace.single (pair j.1 1) (1 : ℝ)
      let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
      let edgePoint := fun (a : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 a true
        (b.symm (EuclideanSpace.single (0 : Fin 1) s,
          EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
      let f := fun j a side l s => w l (embed j (edgePoint a side s))
      let g := fun j a side l s => Dw l (embed j (edgePoint a side s))
        (pair j.1 ((Equiv.swap (0 : Fin 2) 1) a))
      let E₂ := fun j : Fin 3 × Bool => ∑ l : Fin 2, ∫ t in P₂,
        hsNormSq (fun k => Dw l (embed j t) (pair j.1 k))
      let Dedge := fun j a side => ∫ s in Ioo (0 : ℝ) ε, ‖f j a side 0 s - f j a side 1 s‖ ^ 2
      let Aedge := fun j a side => ∫ s in Ioo (0 : ℝ) ε, ‖g j a side 0 s‖ ^ 2 + ‖g j a side 1 s‖ ^ 2
      let L := fun j => E₂ j + ∑ a : Fin 2, ∑ side : Bool,
        ((ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖g j a side 0 s‖ ^ 2) +
          ∫ s in Ioo (0 : ℝ) ε, ‖g j a side 1 s‖ ^ 2) + ε⁻¹ * Dedge j a side)
      let C := fun j => ∑ a : Fin 2, ∑ side : Bool,
        (Dedge j a side / ε + Real.sqrt (2 * Dedge j a side * Aedge j a side))
      (∀ t : Domain 3, (∀ k, t k ∈ Icc (0 : ℝ) ε) →
        ∀ k : Fin (n + 3), (source t) k ∈ Ioo (-1 : ℝ) 1) →
      ∃ faceIndex : (Fin 3 × Bool) → ↥(originalPhysicalCellCarrier 2 grid offset ε),
        (∀ j, (faceIndex j).val.1 = pair j.1 ∧
          (faceIndex j).val.2 = origin j) ∧
      ∃ (V₃ : (Fin 3 × Bool) → Domain 3 → Ambient q)
        (D₃ : (Fin 3 × Bool) → Domain 3 → Gradient 3 q)
        (G : Domain 4 → Ambient q) (D : Domain 4 → Gradient 4 q),
        let W := fun x : Domain 4 => G (‖WithLp.ofLp x‖⁻¹ • x)
        (∀ j, V₃ j = Vglobal (faceIndex j) ∧ D₃ j = Dglobal (faceIndex j)) ∧
        (∀ j, MemW12 B (V₃ j) (D₃ j)) ∧
        (∀ j, (∫ x in B.val, hsNormSq (D₃ j x)) ≤ 3 * L j) ∧
        (∀ j, ∀ᵐ x ∂volume.restrict B.val, (infDist (V₃ j x) N) ^ 2 ≤ C j) ∧
        MemW12 Ω W D ∧
        (∫ x in Ω.val, hsNormSq (D x)) ≤ 2 * ((ε / 2)⁻¹ * E₃ + 3 * ∑ j : Fin 3 × Bool, L j) ∧
        (∀ᵐ x ∂volume.restrict Ω.val, (infDist (W x) N) ^ 2 ≤ ∑ j : Fin 3 × Bool, max (C j) 0) ∧
        ∃ H : Fin 4 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
          (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
            ∃ hs : MemLp (fun x => W (cubicalSignedFaceIsometry 3 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
              H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (cubicalSignedFaceIsometry 3 i true
                (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
          ∀ (i : Fin 4) (side : Bool),
            (H i ⟨if side then 1 else -1, Bool.rec (motive := fun b : Bool => (-1 : ℝ) ≤ if b then 1 else -1) le_rfl (by norm_num) side, Bool.rec (motive := fun b : Bool => (if b then 1 else -1 : ℝ) ≤ 1) (by norm_num) le_rfl side⟩ : Domain 3 → Ambient q)
              =ᵐ[volume.restrict B.val]
                Fin.lastCases (motive := fun _ : Fin 4 => Domain 3 → Ambient q) (U side) (fun j => V₃ (j, side) ∘ A j) i := by
  classical
  intro J₀ J₁ J d₀ d sampleFace₀ sampleFace C Eraw Draw Asample grid
  have hRadius : ((n + 1 : ℕ) : ℝ) + 3 = (n : ℝ) + 4 := by push_cast; ring
  have hSob' : ∀ l, MemW12 (ballDomain (0 : Domain ((n + 1) + 2)) (((n + 1 : ℕ) : ℝ) + 3)) (w l) (Dw l) := by
    simpa only [hRadius] using hSob
  have hTarget' : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain ((n + 1) + 2)) (((n + 1 : ℕ) : ℝ) + 3)), w l x ∈ N := by
    simpa only [hRadius] using hTarget
  obtain ⟨offset, hoffset, _hEnergy, _hDiscrepancy, hWeak, hRawTarget, hHigh, hFirst⟩ :=
    exists_original_ball_all_face_prism_grid (n := n + 1) w Dw hSob' hN hTarget' hε
  refine ⟨offset, hoffset, ?_, ?_, ?_⟩
  · simpa only [hRadius] using _hEnergy
  · simpa only [hRadius] using _hDiscrepancy
  generalize hCanonical : (@coordinatePermACLRepresentative (n + 2) q) = R at hFirst
  let CellCarrier : Type := ↥(originalPhysicalCellCarrier 2 grid offset ε)
  let nativeVertex : CellCarrier → Submodule.span ℤ (Set.range grid) := fun c => c.property.choose
  have hVertexCell (c : CellCarrier) := c.property.choose_spec.1
  have hVertexOrigin (c : CellCarrier) :
      WithLp.toLp 2 (((nativeVertex c : Submodule.span ℤ (Set.range grid)) : Fin (n + 3) → ℝ) + offset) = c.val.2 :=
    c.property.choose_spec.2
  have hGlobalData (c : CellCarrier) := hFirst c.val.1 (nativeVertex c) (by
    have hCell₂ := hVertexCell c
    change ∀ t : Domain 2, (∀ k, t k ∈ Icc (0 : ℝ) ε) → ∀ k : Fin (n + 3),
      (WithLp.toLp 2 (((nativeVertex c : Submodule.span ℤ (Set.range grid)) : Fin (n + 3) → ℝ) + offset) +
        ∑ j : Fin 2, t j • EuclideanSpace.single (c.val.1 j) (1 : ℝ)) k ∈ Ioo (-1 : ℝ) 1 at hCell₂
    simpa only [Fin.sum_univ_two, ← add_assoc] using hCell₂)
  obtain ⟨Gglobal, hGlobalGradient⟩ := Classical.axiomOfChoice hGlobalData
  obtain ⟨Dglobal, hGlobalProps⟩ := Classical.axiomOfChoice hGlobalGradient
  let Vglobal := fun c (x : Domain 3) => Gglobal c (‖WithLp.ofLp x‖⁻¹ • x)
  refine ⟨Vglobal, Dglobal, ?_⟩
  intro coord z y source P₃ P₂ B Ω e U A E₃ pair origin embed b edgePoint f g E₂ Dedge Aedge L C hCell
  have hStep := fun i : Fin 3 => exists_scaled_grid_neighbor hε offset z (coord i)
  choose zs hzs using hStep
  let ze := fun j : Fin 3 × Bool => if j.2 then zs j.1 else z
  have hYE (j : Fin 3 × Bool) : WithLp.toLp 2 (((ze j : Submodule.span ℤ (Set.range grid)) : Fin (n + 3) → ℝ) + offset) = origin j := by
    rcases j with ⟨i, side⟩
    cases side
    · simp only [ze, Bool.false_eq_true, ite_false, origin, zero_smul, add_zero]
      rfl
    · exact hzs i
  have hLowerCell (j : Fin 3 × Bool) (t : Domain 2) (ht : ∀ k, t k ∈ Icc (0 : ℝ) ε) :
      ∀ k : Fin (n + 3), (embed j t) k ∈ Ioo (-1 : ℝ) 1 := by
    have h := coordinate_cell_closed_facet_containment hε.le coord y hCell j.1 j.2 t ht
    simpa only [Fin.sum_univ_two, ← add_assoc] using h
  let faceIndex : (Fin 3 × Bool) → CellCarrier := fun j => ⟨(pair j.1, origin j),
    ⟨ze j, by
      change ∀ t : Domain 2, (∀ k, t k ∈ Icc (0 : ℝ) ε) → ∀ k : Fin (n + 3),
        (WithLp.toLp 2 (((ze j : Submodule.span ℤ (Set.range grid)) : Fin (n + 3) → ℝ) + offset) +
          ∑ a : Fin 2, t a • EuclideanSpace.single (pair j.1 a) (1 : ℝ)) k ∈ Ioo (-1 : ℝ) 1
      simp only [Fin.sum_univ_two, ← add_assoc]
      rw [hYE]
      exact hLowerCell j,
      hYE j⟩⟩
  have hData (j : Fin 3 × Bool) := by
    have h := hGlobalProps (faceIndex j)
    dsimp only at h
    rw [hVertexOrigin (faceIndex j)] at h
    exact h
  let Gv := fun j : Fin 3 × Bool => Gglobal (faceIndex j)
  let Dv := fun j : Fin 3 × Bool => Dglobal (faceIndex j)
  have hCapv := fun j : Fin 3 × Bool => (hData j).1
  have hSobv := fun j : Fin 3 × Bool => (hData j).2.1
  have hEv := fun j : Fin 3 × Bool => (hData j).2.2.1
  have hDistv := fun j : Fin 3 × Bool => (hData j).2.2.2.1
  choose Kv hKv hKvEnd using fun j : Fin 3 × Bool => (hData j).2.2.2.2
  let V := fun j (x : Domain 3) => Gv j (‖WithLp.ofLp x‖⁻¹ • x)
  let rep := fun (l : Fin 2) (i : Fin (n + 3)) =>
    R (Equiv.swap (Fin.last (n + 2)) i) (-1) 1 (w l) (Dw l)
  let j₃ : ((Fin 2 ↪ Fin (n + 3)) ⊕ Fin (n + 3)) ⊕ ((k : Fin (n + 1)) × (Fin (k.val + 3) ↪ Fin (n + 3))) :=
    Sum.inr ⟨0, coord⟩
  have hWeak₃ := hWeak j₃ z
  have hTarget₃ := hRawTarget j₃ z
  have hHigh₂ := fun base normal hbase l => hHigh (0 : Fin (n + 1)) base normal hbase z l
  obtain ⟨hU, hUEnergy, hUTarget, Kh, hKh, hKhEnd⟩ :=
    original_selected_three_face_unit_data hε w Dw coord y hWeak₃ hTarget₃ hHigh₂ hCell
  let index := fun side : Bool => if side then (1 : Fin 2) else 0
  have hKHend (side : Bool) (i : Fin 3) (positive : Bool) := (hKhEnd (index side) i positive).choose_spec
  have hKHendAE (side : Bool) (i : Fin 3) (positive : Bool) :
      (Kh (index side) i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain 2 → Ambient q)
        =ᵐ[volume.restrict (⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1)] (fun x => U side (cubicalSignedFaceIsometry 2 i positive
          ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
    rw [hKHend side i positive]
    exact (hKhEnd (index side) i positive).choose.coeFn_toLp
  have hCore := exists_original_three_cell_prism_from_first_prisms w Dw rep coord hε y V Dv hN C
  dsimp only [rep] at hCore
  obtain ⟨G, D, _hCap, hW, hE, hDist, ⟨H, hH, hHEnd⟩, _hProp⟩ :=
    hCore (fun side => hU (index side)) (fun side => hUTarget (index side)) hSobv hDistv
      (fun side => Kh (index side)) (fun side => hKh (index side)) hKHendAE Kv hKv hKvEnd
  refine ⟨faceIndex, fun _j => ⟨rfl, rfl⟩, V, Dv, G, D, fun j => ⟨rfl, rfl⟩,
    hSobv, hEv, hDistv, hW, ?_, hDist, H, hH, ?_⟩
  · exact four_prism_energy_from_normalized_face_bounds _ ((ε / 2)⁻¹)
      (fun l : Fin 2 => ∫ t in P₃, hsNormSq (fun k => Dw l (source t) (coord k)))
      _ _ L hE (fun side => hUEnergy (index side)) hEv
  · intro i side
    exact hHEnd i side

end StratificationTheory
