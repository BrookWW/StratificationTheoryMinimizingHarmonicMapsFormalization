module

public import StratificationTheory.Interpolation.OriginalAllRankUnitGrid
public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier

public section
open HarmonicMaps MeasureTheory Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Original unit-face data on one fixed selected lattice reindex over all
actual sorted physical cells. One global native trace family retains the
same original maps and both original signed endpoint classes. -/
theorem exists_global_original_unit_face_data {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    {ε : ℝ} (hε : 0 < ε) (offset : Fin (n + 2) → ℝ) (Target : Set (Ambient q)) :
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _ : Fin (n + 2) => ε) (fun _ => hε.ne'.isUnit)
    (      ∀ (r : Fin (n + 2)) (coord : Fin (r.val + 1) ↪ Fin (n + 2))
        (z : Submodule.span ℤ (Set.range grid)),
        let y := WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
        (∀ t : Domain (r.val + 1), (∀ j, t j ∈ Icc (0 : ℝ) ε) →
          ∀ j : Fin (n + 2), (y + ∑ i, t i • EuclideanSpace.single (coord i) (1 : ℝ)) j ∈ Ioo (-1 : ℝ) 1) →
    let P : OpenDomain (r.val + 1) := ⟨⋂ j : Fin (r.val + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
      isOpen_iInter_of_finite fun j : Fin (r.val + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let B : OpenDomain (r.val + 1) := ⟨⋂ j : Fin (r.val + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite fun j : Fin (r.val + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let C := ⋂ j : Fin r.val, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := r.val) (m := 1)
    let source := fun z : Domain (r.val + 1) => y + ∑ j : Fin (r.val + 1), z j • EuclideanSpace.single (coord j) (1 : ℝ)
    let u := fun l => w l ∘ source
    let Du := fun l z j => Dw l (source z) (coord j)
    let T : Domain (r.val + 1) → Domain (r.val + 1) := fun z => WithLp.toLp 2 (fun _ : Fin (r.val + 1) => ε / 2) + (ε / 2) • z
    let U := fun l => u l ∘ T
    let DU := fun l z j => (ε / 2) • Du l (T z) j
    (∀ l, MemW12 B (U l) (DU l)) ∧
    (∀ l, (∫ z in B.val, hsNormSq (DU l z)) =
      (ε / 2) ^ ((2 : ℤ) - (r.val + 1 : ℕ)) * ∫ z in P.val, hsNormSq (Du l z)) ∧
    (∀ l, ∀ᵐ z ∂volume.restrict B.val, U l z ∈ Target) ∧
    ∃ Kh : Fin 2 → Fin (r.val + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry r.val i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          Kh l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U l
            (cubicalSignedFaceIsometry r.val i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ l i (positive : Bool),
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry r.val i positive
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C),
          Kh l i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
            by cases positive <;> norm_num⟩ = hs.toLp (fun x => U l
              (cubicalSignedFaceIsometry r.val i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) →
    let Cell := fun r : ℕ => {c : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (c.val.1 : Fin r → Fin (n + 2))}
    let B := fun r : ℕ => (⟨⋂ i : Fin r, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite fun i : Fin r => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous⟩ : OpenDomain r)
    let Pos := fun r : ℕ => ⋂ i : Fin r, (EuclideanSpace.proj i) ⁻¹' Ioo (0 : ℝ) ε
    let e := fun r : ℕ => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := r) (m := 1)
    let source := fun (r : ℕ) (c : Cell r) (z : Domain r) => c.val.val.2 +
      ∑ j : Fin r, z j • EuclideanSpace.single (c.val.val.1 j) (1 : ℝ)
    let T : (r : ℕ) → Domain r → Domain r := fun r z =>
      WithLp.toLp 2 (fun _ : Fin r => ε / 2) + (ε / 2) • z
    let U := fun (r : ℕ) (c : Cell r) (l : Fin 2) => w l ∘ source r c ∘ T r
    let DU := fun (r : ℕ) (c : Cell r) (l : Fin 2) (z : Domain r) (j : Fin r) =>
      (ε / 2) • Dw l (source r c (T r z)) (c.val.val.1 j)
    (∀ (r : ℕ) (c : Cell (r + 1)) (l : Fin 2), MemW12 (B (r + 1)) (U (r + 1) c l) (DU (r + 1) c l)) ∧
    (∀ (r : ℕ) (c : Cell (r + 1)) (l : Fin 2),
      (∫ z in (B (r + 1)).val, hsNormSq (DU (r + 1) c l z)) =
        (ε / 2) ^ ((2 : ℤ) - (r + 1 : ℕ)) * ∫ z in Pos (r + 1),
          hsNormSq (fun j => Dw l (source (r + 1) c z) (c.val.val.1 j))) ∧
    (∀ (r : ℕ) (c : Cell (r + 1)) (l : Fin 2), ∀ᵐ z ∂volume.restrict (B (r + 1)).val,
      U (r + 1) c l z ∈ Target) ∧
    ∃ Hsource : (r : ℕ) → Cell (r + 1) → Fin 2 → Fin (r + 1) →
        C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B r).val)),
      (∀ r c l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U (r + 1) c l (cubicalSignedFaceIsometry r i true
            ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B r).val),
          Hsource r c l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U (r + 1) c l
            (cubicalSignedFaceIsometry r i true ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ r c l i (side : Bool),
        (Hsource r c l i ⟨if side then 1 else -1, by cases side <;> norm_num,
          by cases side <;> norm_num⟩ : Domain r → Ambient q) =ᵐ[volume.restrict (B r).val]
          (fun x => U (r + 1) c l (cubicalSignedFaceIsometry r i side
            ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  classical
  intro grid hUnit Cell B Pos e source T U DU
  have hCellData (r : ℕ) (c : Cell (r + 1)) :
      (∀ l, MemW12 (B (r + 1)) (U (r + 1) c l) (DU (r + 1) c l)) ∧
      (∀ l, (∫ z in (B (r + 1)).val, hsNormSq (DU (r + 1) c l z)) =
        (ε / 2) ^ ((2 : ℤ) - (r + 1 : ℕ)) * ∫ z in Pos (r + 1),
          hsNormSq (fun j => Dw l (source (r + 1) c z) (c.val.val.1 j))) ∧
      (∀ l, ∀ᵐ z ∂volume.restrict (B (r + 1)).val, U (r + 1) c l z ∈ Target) ∧
      ∃ KH : Fin 2 → Fin (r + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B r).val)),
        (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => U (r + 1) c l (cubicalSignedFaceIsometry r i true
              ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B r).val),
            KH l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U (r + 1) c l
              (cubicalSignedFaceIsometry r i true ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ l i (side : Bool),
          (KH l i ⟨if side then 1 else -1, by cases side <;> norm_num,
            by cases side <;> norm_num⟩ : Domain r → Ambient q) =ᵐ[volume.restrict (B r).val]
            (fun x => U (r + 1) c l (cubicalSignedFaceIsometry r i side
              ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
    rcases c with ⟨⟨⟨coord, y⟩, hMem⟩, hSorted⟩
    have hr : r + 1 ≤ n + 2 := by
      have h := Fintype.card_le_of_injective coord coord.injective
      simpa only [Fintype.card_fin] using h
    let s : Fin (n + 2) := ⟨r, by omega⟩
    obtain ⟨z, hNative, hy⟩ := (mem_originalPhysicalCellCarrier_iff _ _ _ _ _).mp hMem
    dsimp only at hy
    subst y
    have hClosed := (mem_originalCoordinateCellCarrier_iff _ _ _ _ _).mp hNative
    obtain ⟨hW, hEnergy, hN, KH, hRaw, hEnd⟩ := hUnit s coord z hClosed
    refine ⟨?_, ?_, ?_, KH, ?_, ?_⟩
    · with_reducible simpa only [U, DU, source, T, B, Function.comp_def] using hW
    · with_reducible simpa only [U, DU, source, T, B, Pos, Function.comp_def] using hEnergy
    · with_reducible simpa only [U, source, T, B, Function.comp_def] using hN
    · with_reducible simpa only [U, source, T, B, e, Function.comp_def] using hRaw
    ·
      intro l i side
      obtain ⟨hs, hEq⟩ := hEnd l i side
      rw [hEq]
      with_reducible simpa only [U, source, T, B, e, Function.comp_def] using hs.coeFn_toLp
  have hTraces (r : ℕ) (c : Cell (r + 1)) := (hCellData r c).2.2.2
  choose Hsource hRaw hEnd using hTraces
  exact ⟨fun r c => (hCellData r c).1, fun r c => (hCellData r c).2.1,
    fun r c => (hCellData r c).2.2.1, Hsource, hRaw, hEnd⟩

end StratificationTheory
