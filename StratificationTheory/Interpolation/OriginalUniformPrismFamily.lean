module

public import StratificationTheory.Interpolation.OriginalGlobalEdgeBase
public import StratificationTheory.Interpolation.OriginalAllRankUnitGrid
public import StratificationTheory.Foundation.CanonicalSortedPrismFacetFamily
public import StratificationTheory.Interpolation.CanonicalPrismSuccessor
public import StratificationTheory.Interpolation.OriginalGlobalUnitFaceData
public import StratificationTheory.Foundation.NativeCoordinateCubeOpen
public import StratificationTheory.Foundation.CoherentTwoStepRecursion
public import StratificationTheory.Foundation.CoordinateLinePairEnergy

public section

open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped Topology BigOperators ENNReal
namespace StratificationTheory

/-- One original source pair gives a single coherent family of actual
filled coordinate prisms, with shared native lower-face traces and the full
original rank-energy and edge-distance recurrences. -/
theorem exists_original_ball_uniform_prism_family {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 2)) ((n : ℝ) + 3)) (w l) (Dw l))
    (N : Set (Ambient q)) (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)), w l x ∈ N)
    (ε : ℝ) (hε : 0 < ε) :
  ((fun {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (_hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 2)) ((n : ℝ) + 3)) (w l) (Dw l))
    (N : Set (Ambient q)) (_hN : IsCompact N)
    (_hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)), w l x ∈ N)
    (ε : ℝ) (hε : 0 < ε) =>
  let Dspace := n + 2
  let grid := (Pi.basisFun ℝ (Fin Dspace)).isUnitSMul
    (w := fun _ : Fin Dspace => ε) (fun _ => hε.ne'.isUnit)
  let J := (r : Fin (Dspace + 1)) × (Fin r.val ↪ Fin Dspace)
  let sample := fun (j : J) (y : Domain Dspace) (x : Domain j.1.val) =>
    y + ∑ i, x i • EuclideanSpace.single (j.2 i) (1 : ℝ)
  let Csource := fun j : J => ⋂ i : Fin j.1.val, (fun x : Domain j.1.val => x i) ⁻¹' Ico (0 : ℝ) ε
  let Eraw := (ball (0 : Domain Dspace) ((n : ℝ) + 3)).indicator
    (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
  let Draw := (ball (0 : Domain Dspace) ((n : ℝ) + 3)).indicator
    (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
  ∃ offset : Fin Dspace → ℝ, (∀ j, offset j ∈ Ico (0 : ℝ) ε) ∧
    (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ x in Csource j,
      Eraw (sample j (WithLp.toLp 2 ((z : Fin Dspace → ℝ) + offset)) x)) ≤
        2 * (ENNReal.ofReal (ε ^ Dspace))⁻¹ *
          ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ j.1.val)) * ENNReal.ofReal
            ((∫ x in ball (0 : Domain Dspace) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
              ∫ x in ball (0 : Domain Dspace) ((n : ℝ) + 3), hsNormSq (Dw 1 x))) ∧
    (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ x in Csource j,
      Draw (sample j (WithLp.toLp 2 ((z : Fin Dspace → ℝ) + offset)) x)) ≤
        2 * (ENNReal.ofReal (ε ^ Dspace))⁻¹ *
          ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ j.1.val)) * ENNReal.ofReal
            (∫ x in ball (0 : Domain Dspace) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2)) ∧
    let Cell : ℕ → Type := fun r : ℕ => {p : originalPhysicalCellCarrier r grid offset ε // StrictMono (p.val.1 : Fin r → Fin Dspace)}
    let axes : (r : ℕ) → Cell r → (Fin r ↪ Fin Dspace) := fun _r p => p.val.val.1
    let origin : (r : ℕ) → Cell r → Domain Dspace := fun _r p => p.val.val.2
    let B := fun r : ℕ => (⟨⋂ i : Fin r, (fun x : Domain r => x i) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_native_coordinate_cube r (-1) 1⟩ : OpenDomain r)
    let P := fun r : ℕ => (⟨⋂ i : Fin r, (fun x : Domain r => x i) ⁻¹' Ioo (0 : ℝ) ε,
      isOpen_native_coordinate_cube r 0 ε⟩ : OpenDomain r)
    let e := fun r : ℕ => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := r) (m := 1)
    let T : (r : ℕ) → Domain r → Domain r := fun r x => WithLp.toLp 2 (fun _ : Fin r => ε / 2) + (ε / 2) • x
    let source := fun (r : ℕ) (p : Cell r) (x : Domain r) =>
      origin r p + ∑ i, x i • EuclideanSpace.single (axes r p i) (1 : ℝ)
    let U := fun (r : ℕ) (p : Cell r) (l : Fin 2) => w l ∘ source r p ∘ T r
    let DU := fun (r : ℕ) (p : Cell r) (l : Fin 2) (x : Domain r) (i : Fin r) =>
      (ε / 2) • Dw l (source r p (T r x)) (axes r p i)
    let physicalPrism := fun (r : ℕ) (p : Cell r) (x : Domain (r + 1)) =>
      (e Dspace).symm (source r p (T r ((e r x).1)),
        EuclideanSpace.single (0 : Fin 1) ((ε / 2) + (ε / 2) * (e r x).2 0))
    let originalEnergy := fun (r : ℕ) (p : Cell r) => ∑ l : Fin 2, ∫ x in (P r).val,
      hsNormSq (fun i => Dw l (source r p x) (axes r p i))
    let linePoint := fun (p : Cell 1) (s : ℝ) => source 1 p (EuclideanSpace.single (0 : Fin 1) s)
    let lineA := fun p : Cell 1 => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (linePoint p s) (axes 1 p 0)‖ ^ 2 + ‖Dw 1 (linePoint p s) (axes 1 p 0)‖ ^ 2
    let lineD := fun p : Cell 1 => ∫ s in Ioo (0 : ℝ) ε, ‖w 0 (linePoint p s) - w 1 (linePoint p s)‖ ^ 2
    ∃ (V : (r : ℕ) → Cell r → Domain (r + 1) → Ambient q)
      (DV : (r : ℕ) → Cell r → Domain (r + 1) → Gradient (r + 1) q)
      (H : (r : ℕ) → Cell r → Fin (r + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B r).val)))
      (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (frame : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Equiv.Perm (Fin (r + 1)))
      (Tube : (r : ℕ) → Cell r → ℝ)
      (Hsource : (r : ℕ) → Cell (r + 1) → Fin 2 → Fin (r + 1) →
        C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B r).val)))
      (M : ℝ),
      let energy := fun (r : ℕ) (p : Cell r) =>
        (ε / 2) ^ ((r : ℤ) - 1) * ∫ x in (B (r + 1)).val, hsNormSq (DV r p x)
      (0 ≤ M ∧ ∀ z ∈ N, ‖z‖ ≤ M) ∧
      (∀ (r : ℕ) (p : Cell r) (l : Fin 2), MemW12 (B r) (U r p l) (DU r p l)) ∧
      (∀ (r : ℕ) (p : Cell r) (l : Fin 2), ∀ᵐ x ∂volume.restrict (B r).val, U r p l x ∈ N) ∧
      (∀ (r : ℕ) (p : Cell (r + 1)) (l : Fin 2) (i : Fin (r + 1)),
        ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => U (r + 1) p l (cubicalSignedFaceIsometry r i true
              ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B r).val),
            Hsource r p l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
              (fun x => U (r + 1) p l (cubicalSignedFaceIsometry r i true
                ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      (∀ (r : ℕ) (p : Cell (r + 1)) (l : Fin 2) (i : Fin (r + 1)) (side : Bool),
        (Hsource r p l i ⟨if side then 1 else -1,
          Bool.rec (motive := fun b : Bool => (-1 : ℝ) ≤ if b then 1 else -1) le_rfl (le_trans (neg_nonpos.mpr (show (0 : ℝ) ≤ 1 from zero_le_one)) (show (0 : ℝ) ≤ 1 from zero_le_one)) side,
          Bool.rec (motive := fun b : Bool => (if b then 1 else -1 : ℝ) ≤ 1) (le_trans (neg_nonpos.mpr (show (0 : ℝ) ≤ 1 from zero_le_one)) (show (0 : ℝ) ≤ 1 from zero_le_one)) le_rfl side⟩ : Domain r → Ambient q)
          =ᵐ[volume.restrict (B r).val] (fun x => U (r + 1) p l (cubicalSignedFaceIsometry r i side
            ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) ∧
      (∀ (p : Cell 0) (x : Domain 1), V 0 p x =
        (1 - (x 0 + 1) / 2) • w 0 (origin 0 p) + ((x 0 + 1) / 2) • w 1 (origin 0 p)) ∧
      (∀ (r : ℕ) (p : Cell r), MemW12 (B (r + 1)) (V r p) (DV r p)) ∧
      (∀ (r : ℕ) (p : Cell r), ∀ᵐ x ∂volume.restrict (B (r + 1)).val, ‖V r p x‖ ≤ M) ∧
      (∀ (r : ℕ) (p : Cell r) (i : Fin (r + 1)),
        ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => V r p (cubicalSignedFaceIsometry r i true
              ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B r).val),
            H r p i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V r p (cubicalSignedFaceIsometry r i true
              ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      (∀ (r : ℕ) (p : Cell r) (side : Bool),
        (H r p (Fin.last r) ⟨if side then 1 else -1,
          Bool.rec (motive := fun b : Bool => (-1 : ℝ) ≤ if b then 1 else -1) le_rfl (le_trans (neg_nonpos.mpr (show (0 : ℝ) ≤ 1 from zero_le_one)) (show (0 : ℝ) ≤ 1 from zero_le_one)) side,
          Bool.rec (motive := fun b : Bool => (if b then 1 else -1 : ℝ) ≤ 1) (le_trans (neg_nonpos.mpr (show (0 : ℝ) ≤ 1 from zero_le_one)) (show (0 : ℝ) ≤ 1 from zero_le_one)) le_rfl side⟩ : Domain r → Ambient q)
          =ᵐ[volume.restrict (B r).val] U r p (if side then 1 else 0)) ∧
      (∀ (r : ℕ) (p : Cell (r + 1)) (i : Fin (r + 1)) (side : Bool),
        let c := child r p i side
        let A := cubicalSignedPermutation (r + 1) (frame r p i side) (fun _ => true)
        axes r c = i.succAboveEmb.trans (axes (r + 1) p) ∧
        origin r c = origin (r + 1) p + (if side then ε else 0) • EuclideanSpace.single (axes (r + 1) p i) (1 : ℝ) ∧
        frame r p i side i = Fin.last r ∧
        (∀ a : Fin r, frame r p i side (i.succAbove a) = a.castSucc) ∧
        (∀ z : Domain (r + 1), physicalPrism (r + 1) p (cubicalSignedFaceIsometry (r + 1) i.castSucc side
          ((e (r + 1)).symm (z, EuclideanSpace.single (0 : Fin 1) 1))) = physicalPrism r c (A z)) ∧
        (H (r + 1) p i.castSucc ⟨if side then 1 else -1,
          Bool.rec (motive := fun b : Bool => (-1 : ℝ) ≤ if b then 1 else -1) le_rfl (le_trans (neg_nonpos.mpr (show (0 : ℝ) ≤ 1 from zero_le_one)) (show (0 : ℝ) ≤ 1 from zero_le_one)) side,
          Bool.rec (motive := fun b : Bool => (if b then 1 else -1 : ℝ) ≤ 1) (le_trans (neg_nonpos.mpr (show (0 : ℝ) ≤ 1 from zero_le_one)) (show (0 : ℝ) ≤ 1 from zero_le_one)) le_rfl side⟩ : Domain (r + 1) → Ambient q)
          =ᵐ[volume.restrict (B (r + 1)).val] V r c ∘ A) ∧
      (∀ p : Cell 1, energy 1 p ≤ (ε / 2) * lineA p + ε⁻¹ * lineD p) ∧
      (∀ (r : ℕ), 1 ≤ r → ∀ p : Cell (r + 1), energy (r + 1) p ≤
        (((r : ℝ) + 2) / (r : ℝ)) * (ε / 2) *
          (originalEnergy (r + 1) p + ∑ i : Fin (r + 1), ∑ side : Bool, energy r (child r p i side))) ∧
      (∀ (r : ℕ) (p : Cell r), 0 ≤ Tube r p) ∧
      (∀ (r : ℕ) (p : Cell r), ∀ᵐ x ∂volume.restrict (B (r + 1)).val, (infDist (V r p x) N) ^ 2 ≤ Tube r p) ∧
      (∀ p : Cell 0, Tube 0 p ≤ ‖w 0 (origin 0 p) - w 1 (origin 0 p)‖ ^ 2) ∧
      (∀ p : Cell 1, Tube 1 p ≤ lineD p / ε + Real.sqrt (2 * lineD p * lineA p)) ∧
      (∀ (r : ℕ), 1 ≤ r → ∀ p : Cell (r + 1),
        Tube (r + 1) p ≤ ∑ i : Fin (r + 1), ∑ side : Bool, Tube r (child r p i side))
) w Dw hSob N hN hTarget ε hε) := by
  classical
  dsimp (config := {zeta := false}) only
  intro Dspace grid J sample Csource Eraw Draw
  obtain ⟨offset, hoffset, hSource⟩ :=
    exists_original_ball_all_rank_unit_grid w Dw hSob hN hTarget hε
  have hVertexBase := hSource.1
  have hACL := hSource.2.2.2.1
  have hEnergy := hSource.2.2.2.2.2.2.1
  have hDiscrepancy := hSource.2.2.2.2.2.2.2.1
  have hUnit := hSource.2.2.2.2.2.2.2.2.2
  clear hSource
  refine ⟨offset, hoffset, ?_, ?_, ?_⟩
  · simpa only [Dspace, grid, J, sample, Csource, Eraw, WithLp.toLp_add, Set.preimage, PiLp.proj_apply] using hEnergy
  · simpa only [Dspace, grid, J, sample, Csource, Draw, WithLp.toLp_add, Set.preimage, PiLp.proj_apply] using hDiscrepancy
  · intro Cell axes origin B P e T source U DU physicalPrism originalEnergy linePoint lineA lineD
    clear hEnergy hDiscrepancy
    obtain ⟨child, frame, hFields⟩ := exists_canonical_sorted_prism_facet_family grid offset hε.le (by
      intro j
      simp only [grid, Basis.isUnitSMul_apply, Pi.basisFun_apply])
    have hAxes := fun r c i side => (hFields r c i side).1
    have hOrigin := fun r c i side => (hFields r c i side).2.1
    have hFrameTime := fun r c i => (hFields r c i false).2.2.1
    have hFrameSpatial := fun r c i => (hFields r c i false).2.2.2.1
    have hPhysical := fun r c i side => (hFields r c i side).2.2.2.2.2
    obtain ⟨M₀, hM₀⟩ := hN.isBounded.exists_norm_le
    let M : ℝ := max M₀ 0
    have hM0 : 0 ≤ M := le_max_right _ _
    have hM : ∀ z ∈ N, ‖z‖ ≤ M := fun z hz => (hM₀ z hz).trans (le_max_left _ _)

    obtain ⟨hWpos, hEpos, hNpos, Hsource, hHsourceRaw, hHsourceEnd⟩ :=
      exists_global_original_unit_face_data w Dw hε offset N hUnit
    have hOrigW (r : ℕ) (c : Cell (r + 1)) (l : Fin 2) :
        MemW12 (B (r + 1)) (U (r + 1) c l) (DU (r + 1) c l) := by
      with_reducible simpa only [B, Set.preimage, PiLp.proj_apply] using hWpos r c l
    have hOrigN (r : ℕ) (c : Cell (r + 1)) (l : Fin 2) :
        ∀ᵐ x ∂volume.restrict (B (r + 1)).val, U (r + 1) c l x ∈ N := by
      with_reducible simpa only [B, Set.preimage, PiLp.proj_apply] using hNpos r c l
    have hOrigE (r : ℕ) (c : Cell (r + 1)) (l : Fin 2) :
        (∫ x in (B (r + 1)).val, hsNormSq (DU (r + 1) c l x)) =
          (ε / 2) ^ ((2 : ℤ) - (r + 1 : ℕ)) * ∫ x in (P (r + 1)).val,
            hsNormSq (fun i => Dw l (source (r + 1) c x) (axes (r + 1) c i)) := by
      with_reducible simpa only [B, P, Set.preimage, PiLp.proj_apply] using hEpos r c l
    let HS : (r : ℕ) → Cell (r + 1) → Fin 2 → Fin (r + 1) →
        C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B r).val)) := Hsource
    have hHSRaw (r : ℕ) (c : Cell (r + 1)) (l : Fin 2) (i : Fin (r + 1)) :
        ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U (r + 1) c l (cubicalSignedFaceIsometry r i true
            ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B r).val),
          HS r c l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U (r + 1) c l
            (cubicalSignedFaceIsometry r i true ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
      exact hHsourceRaw r c l i
    have hHSEnd (r : ℕ) (c : Cell (r + 1)) (l : Fin 2) (i : Fin (r + 1)) (side : Bool) :
        (HS r c l i ⟨if side then 1 else -1, by cases side <;> norm_num,
          by cases side <;> norm_num⟩ : Domain r → Ambient q) =ᵐ[volume.restrict (B r).val]
          (fun x => U (r + 1) c l (cubicalSignedFaceIsometry r i side
            ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
      exact hHsourceEnd r c l i side
    clear hUnit hWpos hEpos hNpos hHsourceRaw hHsourceEnd
    let Raw : ℕ → Type := fun r =>
      (Cell r → Domain (r + 1) → Ambient q) ×
      (Cell r → Domain (r + 1) → Gradient (r + 1) q) ×
      (Cell r → Fin (r + 1) → C(Icc (-1 : ℝ) 1,
        Lp (Ambient q) 2 (volume.restrict (B r).val))) × (Cell r → ℝ)
    let Good : (r : ℕ) → Raw r → Prop := fun r d =>
      (∀ c, MemW12 (B (r + 1)) (d.1 c) (d.2.1 c)) ∧
      (∀ c, ∀ᵐ x ∂volume.restrict (B (r + 1)).val, ‖d.1 c x‖ ≤ M) ∧
      (∀ c i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => d.1 c (cubicalSignedFaceIsometry r i true
          ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B r).val),
          d.2.2.1 c i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp
            (fun x => d.1 c (cubicalSignedFaceIsometry r i true
              ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      (∀ c (side : Bool),
        (d.2.2.1 c (Fin.last r) ⟨if side then 1 else -1,
          by cases side <;> norm_num, by cases side <;> norm_num⟩ : Domain r → Ambient q)
          =ᵐ[volume.restrict (B r).val] U r c (if side then 1 else 0)) ∧
      (∀ c, 0 ≤ d.2.2.2 c) ∧
      (∀ c, ∀ᵐ x ∂volume.restrict (B (r + 1)).val, (infDist (d.1 c x) N) ^ 2 ≤ d.2.2.2 c)
    let Rank : ℕ → Type := fun r => {d : Raw r // Good r d}
    let E := fun (r : ℕ) (d : Rank r) (c : Cell r) =>
      (ε / 2) ^ ((r : ℤ) - 1) * ∫ x in (B (r + 1)).val, hsNormSq (d.val.2.1 c x)
    let Rel : (r : ℕ) → Rank r → Rank (r + 1) → Prop := fun r a b =>
      (∀ (c : Cell (r + 1)) (i : Fin (r + 1)) (side : Bool),
        (b.val.2.2.1 c i.castSucc ⟨if side then 1 else -1,
          by cases side <;> norm_num, by cases side <;> norm_num⟩ : Domain (r + 1) → Ambient q)
          =ᵐ[volume.restrict (B (r + 1)).val]
          a.val.1 (child r c i side) ∘
            (cubicalSignedPermutation (r + 1) (frame r c i) (fun _ => true))) ∧
      (1 ≤ r → ∀ c : Cell (r + 1), E (r + 1) b c ≤
        (((r : ℝ) + 2) / (r : ℝ)) * (ε / 2) *
          (originalEnergy (r + 1) c + ∑ i : Fin (r + 1), ∑ side : Bool, E r a (child r c i side))) ∧
      (1 ≤ r → ∀ c : Cell (r + 1), b.val.2.2.2 c ≤
        ∑ i : Fin (r + 1), ∑ side : Bool, a.val.2.2.2 (child r c i side))

    let vertex : (r : ℕ) → Cell r → Submodule.span ℤ (Set.range grid) :=
      fun r c => c.val.property.choose
    have hVertexOrigin (r : ℕ) (c : Cell r) :
        WithLp.toLp 2 (((vertex r c : Submodule.span ℤ (Set.range grid)) : Fin Dspace → ℝ) + offset) =
          origin r c := c.val.property.choose_spec.2
    have hClosed (r : ℕ) (c : Cell r) (t : Domain r)
        (ht : ∀ j, t j ∈ Icc (0 : ℝ) ε) :
        ∀ j, (source r c t) j ∈ Ioo (-1 : ℝ) 1 := by
      have h := c.val.property.choose_spec.1
      change ∀ t : Domain r, (∀ j, t j ∈ Icc (0 : ℝ) ε) → ∀ j,
        (WithLp.toLp 2 (((vertex r c : Submodule.span ℤ (Set.range grid)) : Fin Dspace → ℝ) + offset) +
          ∑ i : Fin r, t i • EuclideanSpace.single (axes r c i) (1 : ℝ)) j ∈ Ioo (-1 : ℝ) 1 at h
      simpa only [hVertexOrigin] using h t ht
    have hOriginUnit (r : ℕ) (c : Cell r) : ∀ j, (origin r c) j ∈ Ioo (-1 : ℝ) 1 := by
      have h := hClosed r c 0 (by intro j; change (0 : ℝ) ∈ Icc (0 : ℝ) ε; exact ⟨le_rfl, hε.le⟩)
      simpa only [source, PiLp.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] using h
    have hBaseZero (c : Cell 0) := hVertexBase (vertex 0 c) (by
      rw [hVertexOrigin]
      exact hOriginUnit 0 c)
    let V₀ : Cell 0 → Domain 1 → Ambient q := fun c => rawVertexUnitChord w (origin 0 c)
    let D₀ : Cell 0 → Domain 1 → Gradient 1 q := fun c => rawVertexUnitGradient w (origin 0 c)
    let Tube₀ : Cell 0 → ℝ := fun c => ‖w 0 (origin 0 c) - w 1 (origin 0 c)‖ ^ 2

    have hN₀ (c : Cell 0) (l : Fin 2) : w l (origin 0 c) ∈ N := by
      have h := (hBaseZero c).1 l
      simpa only [hVertexOrigin] using h
    have hU₀ (c : Cell 0) (l : Fin 2) : U 0 c l = fun _ : Domain 0 => w l (origin 0 c) := by
      funext x
      simp only [U, Function.comp_apply, source, Fin.sum_univ_zero, add_zero]
    choose K₀ hK₀ hK₀End using fun c : Cell 0 => exists_rawVertexUnitChord_trace w (origin 0 c)
    let H₀ : Cell 0 → Fin 1 → C(Icc (-1 : ℝ) 1,
        Lp (Ambient q) 2 (volume.restrict (B 0).val)) := fun c _ => K₀ c
    have hQ₀ (i : Fin 1) (z : Domain 1) : cubicalSignedFaceIsometry 0 i true z = z := by
      ext j
      have hj : j = i := by apply Fin.ext; have := j.isLt; have := i.isLt; omega
      have hi : Fin.last 0 = i := by apply Fin.ext; have := i.isLt; simp only [Fin.val_last]; omega
      rw [cubicalSignedFaceIsometry_coordinate, if_pos hj, if_pos rfl, hi, hj]
    have hGood₀ : Good 0 (V₀, D₀, H₀, Tube₀) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c
        simpa only [V₀, D₀, B, Set.preimage, PiLp.proj_apply] using rawVertexUnitChord_memW12 w (origin 0 c)
      · intro c
        filter_upwards [ae_restrict_mem (B 1).property.measurableSet] with x hx
        apply rawVertexUnitChord_norm_le w (origin 0 c) (fun l => hM _ (hN₀ c l))
        exact ⟨(mem_iInter.mp hx 0).1.le, (mem_iInter.mp hx 0).2.le⟩
      · intro c i
        filter_upwards [] with t
        intro ht
        obtain ⟨hs, heq⟩ := hK₀ c ⟨t, ht.1.le, ht.2.le⟩
        let F : Domain 0 → Ambient q := fun x => V₀ c (cubicalSignedFaceIsometry 0 i true
          ((e 0).symm (x, EuclideanSpace.single (0 : Fin 1) t)))
        have hs' : MemLp F 2 (volume.restrict (B 0).val) := by
          simpa only [F, V₀, hQ₀, B, e, Set.preimage, PiLp.proj_apply] using hs
        refine ⟨hs', ?_⟩
        change K₀ c ⟨t, ht.1.le, ht.2.le⟩ = hs'.toLp F
        rw [heq]
        apply MemLp.toLp_congr hs hs'
        exact Filter.Eventually.of_forall fun x => by simp only [F, V₀, hQ₀, e]
      · intro c side
        obtain ⟨hs, heq⟩ := hK₀End c side
        change (K₀ c _ : Domain 0 → Ambient q) =ᵐ[volume.restrict (B 0).val] U 0 c _
        rw [heq, hU₀]
        exact hs.coeFn_toLp
      · intro c
        exact sq_nonneg _
      · intro c
        filter_upwards [ae_restrict_mem (B 1).property.measurableSet] with x hx
        apply rawVertexUnitChord_infDist_sq_le w (origin 0 c) (hN₀ c 0)
        exact ⟨(mem_iInter.mp hx 0).1.le, (mem_iInter.mp hx 0).2.le⟩
    let a₀ : Rank 0 := ⟨(V₀, D₀, H₀, Tube₀), hGood₀⟩

    have hRankStep (k : ℕ) (a : Rank k) (b : Rank (k + 1)) (hab : Rel k a b) :
        ∃ c : Rank (k + 2), Rel (k + 1) b c := by
      rcases b.property with ⟨hWb, hNormb, hRawb, hTimeb, hTubeNonnegB, hDistb⟩
      rcases hab with ⟨hSpatialb, _hOldEnergy, _hOldTube⟩
      have hNext (parent : Cell (k + 2)) := exists_canonical_prism_successor
        grid offset ε hε w Dw N hN child frame hAxes hOrigin hFrameTime hFrameSpatial hPhysical
        parent b.val.1 b.val.2.1 a.val.1 b.val.2.2.2 b.val.2.2.1 (HS (k + 1) parent)
        hWb hTubeNonnegB hDistb hRawb hTimeb hSpatialb
        (hOrigW (k + 1) parent) (hOrigE (k + 1) parent) (hOrigN (k + 1) parent)
        (hHSRaw (k + 1) parent) (hHSEnd (k + 1) parent)
      choose Gn Dn Kn hAllN using hNext
      have hWn := fun c => (hAllN c).1
      have hPhysicalEn := fun c => (hAllN c).2.2.1
      have hDistn := fun c => (hAllN c).2.2.2.1
      have hRawn := fun c => (hAllN c).2.2.2.2.1
      have hTimen := fun c => (hAllN c).2.2.2.2.2.1
      have hSpatialn := fun c => (hAllN c).2.2.2.2.2.2.1
      have hPropn := fun c => (hAllN c).2.2.2.2.2.2.2
      let Vn : Cell (k + 2) → Domain (k + 3) → Ambient q := fun c z => Gn c (‖WithLp.ofLp z‖⁻¹ • z)
      let Tn : Cell (k + 2) → ℝ := fun c => ∑ i : Fin (k + 2), ∑ side : Bool,
        b.val.2.2.2 (child (k + 1) c i side)
      have hGoodN : Good (k + 2) (Vn, Dn, Kn, Tn) := by
        refine ⟨hWn, ?_, hRawn, hTimen, ?_, hDistn⟩
        · intro c
          apply hPropn c (fun z => ‖z‖ ≤ M)
          · intro l
            exact (hOrigN (k + 1) c l).mono fun x hx => hM _ hx
          · intro i side
            exact hNormb _
        · intro c
          change 0 ≤ Tn c
          dsimp only [Tn]
          exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun side _ => hTubeNonnegB _
      let cn : Rank (k + 2) := ⟨(Vn, Dn, Kn, Tn), hGoodN⟩
      refine ⟨cn, hSpatialn, ?_, ?_⟩
      · intro _ c
        have h := hPhysicalEn c
        have hCoeff : (k : ℝ) + 1 + 2 = (k : ℝ) + 3 := by ring
        simpa only [E, cn, B, P, originalEnergy, source, origin, axes,
          Set.preimage, PiLp.proj_apply, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
          add_sub_cancel_right, show (2 : ℤ) - 1 = 1 by norm_num, add_sub_assoc, hCoeff]
          using h
      · intro _ c
        exact le_rfl

    have hOrigZeroW (c : Cell 0) (l : Fin 2) : MemW12 (B 0) (U 0 c l) (DU 0 c l) := by
      rw [hU₀]
      letI : IsFiniteMeasure (volume.restrict (B 0).val) := isFiniteMeasure_restrict.mpr (by
        simpa only [B, Set.preimage, PiLp.proj_apply] using volume_unit_coordinate_face_ne_top 0)
      refine ⟨⟨continuous_const.continuousOn.locallyIntegrableOn (B 0).property.measurableSet,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, memLp_const _, fun i => Fin.elim0 i⟩
    have hOrigAllW (r : ℕ) (c : Cell r) (l : Fin 2) : MemW12 (B r) (U r c l) (DU r c l) := by
      cases r with
      | zero => exact hOrigZeroW c l
      | succ r => exact hOrigW r c l
    have hOrigAllN (r : ℕ) (c : Cell r) (l : Fin 2) :
        ∀ᵐ x ∂volume.restrict (B r).val, U r c l x ∈ N := by
      cases r with
      | zero =>
        rw [hU₀]
        exact Filter.Eventually.of_forall fun _ => hN₀ c l
      | succ r => exact hOrigN r c l

    let emptyBase : Fin 0 ↪ Fin Dspace := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
    let normalIndex : Fin Dspace → (r : Fin Dspace) ×
        {v : (Fin r.val ↪ Fin Dspace) × Fin Dspace // ∀ s, v.1 s ≠ v.2} :=
      fun normal => ⟨⟨0, by dsimp only [Dspace]; omega⟩,
        ⟨(emptyBase, normal), by intro i; exact Fin.elim0 i⟩⟩
    have allnormalACL (normal : Fin Dspace) (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) :=
      hACL z l (normalIndex normal)
    obtain ⟨hEdgeW, hEdgeE, hEdgeTubeNonneg, hEdgeTubeClosed, hEdgeNormClosed,
        K₁, hK₁Raw, hK₁End⟩ := exists_global_original_edge_base (n := n + 1) w Dw hN.isClosed hε offset M hM (by
          intro normal z l
          with_reducible exact allnormalACL normal z l)
    let V₁ : Cell 1 → Domain 2 → Ambient q := fun c => coordinateEdgeUnitMap
      (Equiv.swap (Fin.last (n + 1)) (axes 1 c 0)) (-1) 1 ε w Dw (origin 1 c)
    let D₁ : Cell 1 → Domain 2 → Gradient 2 q := fun c => coordinateEdgeUnitGradient
      (Equiv.swap (Fin.last (n + 1)) (axes 1 c 0)) (-1) 1 ε w Dw (origin 1 c)
    let Tube₁ : Cell 1 → ℝ := fun c => lineD c / ε + Real.sqrt (2 * lineD c * lineA c)
    let H₁ : Cell 1 → Fin 2 → C(Icc (-1 : ℝ) 1,
        Lp (Ambient q) 2 (volume.restrict (B 1).val)) := K₁
    have hLinePoint (c : Cell 1) (s : ℝ) : linePoint c s =
        origin 1 c + s • EuclideanSpace.single (axes 1 c 0) (1 : ℝ) := by
      simp only [linePoint, source, Fin.sum_univ_one, PiLp.single_apply, ite_true]
    have hGood₁ : Good 1 (V₁, D₁, H₁, Tube₁) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c
        with_reducible simpa only [V₁, D₁, B, axes, origin, Set.preimage, PiLp.proj_apply] using hEdgeW c
      · intro c
        filter_upwards [ae_restrict_mem (B 2).property.measurableSet] with x hx
        have h := hEdgeNormClosed c x (fun i => ⟨(mem_iInter.mp hx i).1.le, (mem_iInter.mp hx i).2.le⟩)
        with_reducible simpa only [V₁, axes, origin] using h
      · intro c i
        filter_upwards [hK₁Raw c i] with t ht
        intro hti
        obtain ⟨hs, heq⟩ := ht hti
        let F : Domain 1 → Ambient q := fun x => V₁ c (cubicalSignedFaceIsometry 1 i true
          ((e 1).symm (x, EuclideanSpace.single (0 : Fin 1) t)))
        have hs' : MemLp F 2 (volume.restrict (B 1).val) := by
          with_reducible simpa only [F, V₁, B, e, axes, origin, Set.preimage, PiLp.proj_apply] using hs
        refine ⟨hs', ?_⟩
        change K₁ c i ⟨t, hti.1.le, hti.2.le⟩ = hs'.toLp F
        rw [heq]
        apply MemLp.toLp_congr hs hs'
        exact Filter.Eventually.of_forall fun _ => rfl
      · intro c side
        have hLast : (Fin.last 1 : Fin 2) ≠ 0 := by decide
        have h := hK₁End c (Fin.last 1) side
        dsimp only at h
        rw [if_neg hLast] at h
        exact h
      · intro c
        with_reducible simpa only [Tube₁, lineD, lineA, hLinePoint, axes, origin] using hEdgeTubeNonneg c
      · intro c
        filter_upwards [ae_restrict_mem (B 2).property.measurableSet] with x hx
        have h := hEdgeTubeClosed c x (fun i => ⟨(mem_iInter.mp hx i).1.le, (mem_iInter.mp hx i).2.le⟩)
        with_reducible simpa only [V₁, Tube₁, lineD, lineA, hLinePoint, axes, origin] using h
    let a₁ : Rank 1 := ⟨(V₁, D₁, H₁, Tube₁), hGood₁⟩
    have hRel₀ : Rel 0 a₀ a₁ := by
      refine ⟨?_, ?_, ?_⟩
      · intro c i side
        have hi : i = 0 := by apply Fin.ext; have := i.isLt; omega
        subst i
        have hSp : (H₁ c (0 : Fin 2) ⟨if side then 1 else -1,
            by cases side <;> norm_num, by cases side <;> norm_num⟩ : Domain 1 → Ambient q)
            =ᵐ[volume.restrict (B 1).val] rawVertexUnitChord w
              (origin 1 c + (if side then ε else 0) • EuclideanSpace.single (axes 1 c 0) (1 : ℝ)) := by
          have h := hK₁End c 0 side
          dsimp only at h
          rw [if_pos rfl] at h
          exact h
        have hA (x : Domain 1) :
            (cubicalSignedPermutation 1 (frame 0 c 0) (fun _ => true)) x = x := by
          ext j
          obtain ⟨a, rfl⟩ := (frame 0 c 0).surjective j
          rw [cubicalSignedPermutation_apply, if_pos rfl]
          apply congrArg (fun a : Fin 1 => x a)
          apply Fin.ext
          have := a.isLt
          have := ((frame 0 c 0) a).isLt
          omega
        filter_upwards [hSp] with x hx
        change H₁ c 0 _ x = (V₀ (child 0 c 0 side))
          ((cubicalSignedPermutation 1 (frame 0 c 0) (fun _ => true)) x)
        rw [hA]
        change H₁ c 0 _ x = rawVertexUnitChord w (origin 0 (child 0 c 0 side)) x
        rw [show origin 0 (child 0 c 0 side) = origin 1 c +
          (if side then ε else 0) • EuclideanSpace.single (axes 1 c 0) (1 : ℝ) by
            exact hOrigin 0 c 0 side]
        exact hx
      · intro h
        omega
      · intro h
        omega
    have hBaseEnergy (c : Cell 1) : E 1 a₁ c ≤ (ε / 2) * lineA c + ε⁻¹ * lineD c := by
      with_reducible simpa only [E, a₁, D₁, B, lineA, lineD, hLinePoint, axes, origin,
        Set.preimage, PiLp.proj_apply, show ((1 : ℕ) : ℤ) - 1 = 0 by norm_num,
        zpow_zero, one_mul] using hEdgeE c
    have hBaseTube (c : Cell 1) : a₁.val.2.2.2 c ≤
        lineD c / ε + Real.sqrt (2 * lineD c * lineA c) := le_rfl

    clear hVertexBase hACL hBaseZero hVertexOrigin hClosed hOriginUnit allnormalACL normalIndex emptyBase
    have hFamily : ∃ f : (r : ℕ) → Rank r,
        f 0 = a₀ ∧ f 1 = a₁ ∧ ∀ r, Rel r (f r) (f (r + 1)) := by
      with_reducible exact exists_coherent_two_step_family (A := Rank) Rel a₀ a₁ hRel₀ hRankStep
    obtain ⟨f, hf₀, hf₁, hRel⟩ := hFamily
    refine ⟨(fun r => (f r).val.1), (fun r => (f r).val.2.1),
      (fun r => (f r).val.2.2.1), child, (fun r c i _side => frame r c i),
      (fun r => (f r).val.2.2.2), HS, M, ⟨hM0, hM⟩, hOrigAllW, hOrigAllN,
      hHSRaw, hHSEnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c x
      change (f 0).val.1 c x = _
      exact congrArg (fun a : Rank 0 => a.val.1 c x) hf₀
    · with_reducible exact fun r => (f r).property.1
    · with_reducible exact fun r => (f r).property.2.1
    · with_reducible exact fun r => (f r).property.2.2.1
    · with_reducible exact fun r => (f r).property.2.2.2.1
    · intro r c i side
      exact ⟨hAxes r c i side, hOrigin r c i side, hFrameTime r c i,
        hFrameSpatial r c i, hPhysical r c i side, (hRel r).1 c i side⟩
    · intro c
      change E 1 (f 1) c ≤ _
      exact (congrArg (fun a : Rank 1 => E 1 a c) hf₁).le.trans (hBaseEnergy c)
    · intro r hr c
      exact (hRel r).2.1 hr c
    · with_reducible exact fun r => (f r).property.2.2.2.2.1
    · with_reducible exact fun r => (f r).property.2.2.2.2.2
    · intro c
      change (f 0).val.2.2.2 c ≤ _
      exact (congrArg (fun a : Rank 0 => a.val.2.2.2 c) hf₀).le
    · intro c
      change (f 1).val.2.2.2 c ≤ _
      exact (congrArg (fun a : Rank 1 => a.val.2.2.2 c) hf₁).le.trans (hBaseTube c)
    · intro r hr c
      exact (hRel r).2.2 hr c

end StratificationTheory
