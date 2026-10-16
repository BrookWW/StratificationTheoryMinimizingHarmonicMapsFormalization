module

public import StratificationTheory.Interpolation.OriginalUniformPrismFamily
public import StratificationTheory.Interpolation.OriginalGridPrismEnergyBound
public import StratificationTheory.Interpolation.OriginalGridPrismUniformTube

public section

open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped Topology BigOperators ENNReal
namespace StratificationTheory

/-- One original source pair produces a coherent all-rank prism family whose
actual terminal physical energy sum is finite and has the coupled original
energy/discrepancy bound. The same family's tubes have the frozen ambient
powers at every positive rank. -/
theorem exists_original_ball_uniform_prism_family_with_estimates {n q : ℕ}
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
      (
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
      ) ∧
      let A₀ := (∫ x in ball (0 : Domain Dspace) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
        ∫ x in ball (0 : Domain Dspace) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
      let D₀ := ∫ x in ball (0 : Domain Dspace) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
      let K : ℝ≥0∞ := 4 * (Fintype.card J : ℝ≥0∞) * (Fintype.card J : ℝ≥0∞) *
        (6 * ((n + 3 : ℕ) : ℝ≥0∞)) ^ (n + 1)
      (0 < K ∧ K ≠ ⊤ ∧
        (∑' p : Cell Dspace, ENNReal.ofReal (energy Dspace p)) ≤
          K * (ENNReal.ofReal ε * ENNReal.ofReal A₀ +
            (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal D₀) ∧
        (∑' p : Cell Dspace, ENNReal.ofReal (energy Dspace p)) ≠ ⊤) ∧
      (∀ (r : ℕ) (p : Cell (r + 1)), Tube (r + 1) p ≤
        ((2 : ℝ) ^ r * ((r + 1).factorial : ℝ)) *
          ((4 * (Fintype.card J : ℝ)) * ε ^ ((1 : ℤ) - (Dspace : ℤ)) * Real.sqrt A₀ * Real.sqrt D₀ +
            (4 * (Fintype.card J : ℝ)) * ε ^ (-(Dspace : ℤ)) * D₀))
) w Dw hSob N hN hTarget ε hε) := by
  classical
  dsimp (config := {zeta := false}) only
  intro Dspace grid J sample Csource Eraw Draw
  obtain ⟨offset, hoffset, hEnergy, hDiscrepancy, hFamily⟩ :=
    exists_original_ball_uniform_prism_family w Dw hSob N hN hTarget ε hε
  refine ⟨offset, hoffset, ?_, ?_, ?_⟩
  · simpa only [Dspace, grid, J, sample, Csource, Eraw, WithLp.toLp_add,
      Set.preimage, PiLp.proj_apply] using hEnergy
  · simpa only [Dspace, grid, J, sample, Csource, Draw, WithLp.toLp_add,
      Set.preimage, PiLp.proj_apply] using hDiscrepancy
  · intro Cell axes origin B P e T source U DU physicalPrism originalEnergy linePoint lineA lineD
    obtain ⟨V, DV, H, child, frame, Tube, HS, M, hAll⟩ := hFamily
    refine ⟨V, DV, H, child, frame, Tube, HS, M, ?_⟩
    intro energy
    refine ⟨hAll, ?_⟩
    intro A₀ D₀ K
    have hFacets := hAll.2.2.2.2.2.2.2.2.2.2.1
    have hBaseEnergy := hAll.2.2.2.2.2.2.2.2.2.2.2.1
    have hRecEnergy := hAll.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hBaseTube := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hRecTube := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hLinePoint (p : Cell 1) (s : ℝ) : linePoint p s =
        origin 1 p + s • EuclideanSpace.single (axes 1 p 0) (1 : ℝ) := by
      simp only [linePoint, source, Fin.sum_univ_one, PiLp.single_apply, ite_true]
    let coord : Fin Dspace → (Fin 1 ↪ Fin Dspace) := fun normal =>
      ⟨fun _ => normal, by intro a b _; exact Subsingleton.elim a b⟩
    let rankOne : Fin Dspace → J := fun normal =>
      ⟨⟨1, by dsimp only [Dspace]; omega⟩, coord normal⟩
    have hLineSelectE (normal : Fin Dspace) := hEnergy (rankOne normal)
    have hLineSelectD (normal : Fin Dspace) := hDiscrepancy (rankOne normal)
    have hTotal := original_selected_grid_prism_total_energy_bound w Dw hε offset
      (by
        intro j
        simpa only [sample, Csource, Eraw, Set.preimage, PiLp.proj_apply] using hEnergy j)
      (by
        intro normal
        with_reducible simpa only [Dspace, J, rankOne, coord, Function.Embedding.coeFn_mk, sample, Csource, Draw, Set.preimage,
          PiLp.proj_apply, Fin.sum_univ_one, pow_one] using hLineSelectD normal)
      DV child (fun r p i side => (hFacets (r + 1) p i side).1)
      (fun r p i side => (hFacets (r + 1) p i side).2.1)
      (by
        simpa only [energy, B, Set.preimage, PiLp.proj_apply] using hBaseEnergy)
      (by
        simpa only [energy, B, P, originalEnergy, source, axes, origin,
          Set.preimage, PiLp.proj_apply] using hRecEnergy)
    have hTubes := original_selected_grid_prism_tubes_le_frozen_powers w Dw hε
      (Fintype.card J) offset
      (by
        intro normal
        with_reducible simpa only [Dspace, J, rankOne, coord, Function.Embedding.coeFn_mk, sample, Csource, Eraw, Set.preimage,
          PiLp.proj_apply, Fin.sum_univ_one, pow_one] using hLineSelectE normal)
      (by
        intro normal
        with_reducible simpa only [Dspace, J, rankOne, coord, Function.Embedding.coeFn_mk, sample, Csource, Draw, Set.preimage,
          PiLp.proj_apply, Fin.sum_univ_one, pow_one] using hLineSelectD normal)
      child Tube
      (by
        simpa only [lineA, lineD, hLinePoint, axes, origin, Fin.sum_univ_one, PiLp.single_apply, ite_true] using hBaseTube)
      (fun r p => hRecTube (r + 1) (by omega) p)
    refine ⟨?_, ?_⟩
    · simpa only [K, J, Dspace, A₀, D₀, energy, B, Set.preimage, PiLp.proj_apply] using hTotal
    · simpa only [Dspace, A₀, D₀] using hTubes

end StratificationTheory
