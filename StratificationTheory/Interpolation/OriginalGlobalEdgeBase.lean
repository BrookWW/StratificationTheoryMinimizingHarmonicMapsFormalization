module

public import StratificationTheory.Interpolation.OriginalSelectedCoordinateEdgeBase
public import StratificationTheory.Interpolation.OriginalSelectedCoordinateEdgeNorm
public import StratificationTheory.Foundation.CoordinateLinePairEnergy
public import StratificationTheory.Foundation.OriginalPhysicalCellCarrier

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Original selected line events on one fixed lattice produce one global
canonical edge-prism trace family. The maps and columns retain their literal
original ACL formulas, with paired physical line energy and raw vertex chords. -/
theorem exists_global_original_edge_base {n q : ℕ}
    (w : Fin 2 → Domain (n + 1) → Ambient q)
    (Dw : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    {Target : Set (Ambient q)} (hTarget : IsClosed Target)
    {ε : ℝ} (hε : 0 < ε) (offset : Fin (n + 1) → ℝ)
    (M : ℝ) (hM : ∀ z ∈ Target, ‖z‖ ≤ M) :
    let p := fun normal : Fin (n + 1) => Equiv.swap (Fin.last n) normal
    let Q := fun normal => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p normal)
    let e₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let j := fun normal => p normal (Fin.natAdd n (0 : Fin 1))
    let β := fun normal (y : Domain (n + 1)) => (e₀ ((Q normal).symm y)).1
    let rep := fun l normal => coordinatePermACLRepresentative (p normal) (-1) 1 (w l) (Dw l)
    let line := fun normal x t => Q normal (e₀.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω := fun normal => {y : Domain (n + 1) |
      β normal y ∈ S ∧ (e₀ ((Q normal).symm y)).2 0 ∈ Ioo (-1 : ℝ) 1}
    let L := fun (l : Fin 2) normal (y : Domain (n + 1)) => y ∈ Ω normal →
      rep l normal y = w l y ∧
      MemLp (fun t => w l (line normal (β normal y) t)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      MemLp (fun t => Dw l (line normal (β normal y) t) (j normal)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      AbsolutelyContinuousOnInterval (fun t => rep l normal (line normal (β normal y) t)) (-1) 1 ∧
      (fun t => rep l normal (line normal (β normal y) t)) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
        (fun t => w l (line normal (β normal y) t)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, rep l normal (line normal (β normal y) t) ∈ Target) ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
        rep l normal (line normal (β normal y) t) - rep l normal (line normal (β normal y) s) =
          ∫ r in s..t, Dw l (line normal (β normal y) r) (j normal)
    let grid := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _ : Fin (n + 1) => ε) (fun _ => hε.ne'.isUnit)
    (∀ normal (z : Submodule.span ℤ (Set.range grid)) l,
      L l normal (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) →
    let Cell := {c : originalPhysicalCellCarrier 1 grid offset ε // StrictMono (c.val.1 : Fin 1 → Fin (n + 1))}
    let B : OpenDomain 2 := ⟨⋂ i : Fin 2, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite fun i : Fin 2 => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous⟩
    let C := ⋂ i : Fin 1, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let axis := fun c : Cell => c.val.val.1 0
    let V1 := fun c : Cell => coordinateEdgeUnitMap (p (axis c)) (-1) 1 ε w Dw c.val.val.2
    let D1 := fun c : Cell => coordinateEdgeUnitGradient (p (axis c)) (-1) 1 ε w Dw c.val.val.2
    let point := fun (c : Cell) (s : ℝ) => c.val.val.2 + s • EuclideanSpace.single (axis c) (1 : ℝ)
    let A := fun c : Cell => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (point c s) (axis c)‖ ^ 2 + ‖Dw 1 (point c s) (axis c)‖ ^ 2
    let D := fun c : Cell => ∫ s in Ioo (0 : ℝ) ε, ‖w 0 (point c s) - w 1 (point c s)‖ ^ 2
    let source1 := fun (c : Cell) (x : Domain 1) => c.val.val.2 +
      ∑ a : Fin 1, x a • EuclideanSpace.single (c.val.val.1 a) (1 : ℝ)
    let T1 := fun x : Domain 1 => WithLp.toLp 2 (fun _ : Fin 1 => ε / 2) + (ε / 2) • x
    let U1 := fun (c : Cell) (l : Fin 2) => w l ∘ source1 c ∘ T1
    let face := fun (c : Cell) (i : Fin 2) (side : Bool) => if i = 0 then
      rawVertexUnitChord w (point c (if side then ε else 0)) else U1 c (if side then 1 else 0)
    (∀ c, MemW12 B (V1 c) (D1 c)) ∧
    (∀ c, (∫ x in B.val, hsNormSq (D1 c x)) ≤ (ε / 2) * A c + ε⁻¹ * D c) ∧
    (∀ c, 0 ≤ D c / ε + Real.sqrt (2 * D c * A c)) ∧
    (∀ c x, (∀ i, x i ∈ Icc (-1 : ℝ) 1) → (infDist (V1 c x) Target) ^ 2 ≤
      D c / ε + Real.sqrt (2 * D c * A c)) ∧
    (∀ c x, (∀ i, x i ∈ Icc (-1 : ℝ) 1) → ‖V1 c x‖ ≤ M) ∧
    ∃ K1 : Cell → Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ c i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => V1 c (cubicalSignedFaceIsometry 1 i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          K1 c i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V1 c
            (cubicalSignedFaceIsometry 1 i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ c i (side : Bool),
        (K1 c i ⟨if side then 1 else -1, by cases side <;> norm_num,
          by cases side <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C] face c i side := by
  classical
  intro p Q e₀ j β rep line S Ω L grid hACL Cell B C e axis V1 D1 point A D source1 T1 U1 face
  let v := fun normal => EuclideanSpace.single (j normal) (1 : ℝ)
  have hCellData (c : Cell) :
      MemW12 B (V1 c) (D1 c) ∧
      (∫ x in B.val, hsNormSq (D1 c x)) ≤ (ε / 2) * A c + ε⁻¹ * D c ∧
      (∀ x, (∀ i, x i ∈ Icc (-1 : ℝ) 1) → (infDist (V1 c x) Target) ^ 2 ≤
        D c / ε + Real.sqrt (2 * D c * A c)) ∧
      (∀ x, (∀ i, x i ∈ Icc (-1 : ℝ) 1) → ‖V1 c x‖ ≤ M) ∧
      ∃ K : Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => V1 c (cubicalSignedFaceIsometry 1 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
            K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V1 c
              (cubicalSignedFaceIsometry 1 i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i (side : Bool),
          (K i ⟨if side then 1 else -1, by cases side <;> norm_num,
            by cases side <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C] face c i side := by
    rcases c with ⟨⟨⟨coord, y⟩, hMem⟩, hSorted⟩
    obtain ⟨z, hNative, hy⟩ := (mem_originalPhysicalCellCarrier_iff _ _ _ _ _).mp hMem
    dsimp only at hy
    subst y
    let normal := coord 0
    let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
    have hNormal : j normal = normal := Equiv.swap_apply_left _ _
    have hColumn : (Equiv.swap (Fin.last n) (coord 0))
        (Fin.natAdd n (0 : Fin 1)) = coord 0 := Equiv.swap_apply_left _ _
    have hClosed := (mem_originalCoordinateCellCarrier_iff _ _ _ _ _).mp hNative
    have hLine (s : ℝ) (hs : s ∈ Icc (0 : ℝ) ε) :
        ∀ a, (y + s • EuclideanSpace.single normal (1 : ℝ)) a ∈ Ioo (-1 : ℝ) 1 := by
      have ht : ∀ a : Fin 1, (EuclideanSpace.single (0 : Fin 1) s) a ∈ Icc (0 : ℝ) ε := by
        intro a
        have ha : a = 0 := Subsingleton.elim _ _
        simpa only [ha, PiLp.single_apply, ite_true] using hs
      have h := hClosed (EuclideanSpace.single (0 : Fin 1) s) ht
      simpa only [Fin.sum_univ_one, PiLp.single_apply, ite_true] using h
    have hLineV (s : ℝ) (hs : s ∈ Icc (0 : ℝ) ε) : ∀ a,
        (y + s • v normal) a ∈ Ioo (-1 : ℝ) 1 := by simpa only [v, hNormal] using hLine s hs
    have hStart : ∀ a, y a ∈ Ioo (-1 : ℝ) 1 := by
      simpa only [zero_smul, add_zero] using hLine 0 ⟨le_rfl, hε.le⟩
    have hΩ : y ∈ Ω normal := by
      constructor
      · apply mem_iInter.mpr
        intro a
        change (e₀ ((Q normal).symm y)).1 a ∈ Ioo (-1 : ℝ) 1
        rw [coordinate_split_first_eq]
        exact hStart _
      · rw [coordinate_split_last_eq]
        exact hStart _
    have ha : (-1 : ℝ) ≤ y (j normal) := (hStart _).1.le
    have hb : y (j normal) + ε ≤ (1 : ℝ) := by
      have h := (hLineV ε ⟨hε.le, le_rfl⟩ (j normal)).2.le
      simpa only [v, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
        smul_eq_mul, mul_one] using h
    have hBaseProducer := original_selected_coordinate_edge_base w Dw hTarget hε offset normal
    have hNormProducer := original_selected_coordinate_edge_norm (N := Target) w Dw hε offset normal
    dsimp only at hBaseProducer hNormProducer
    dsimp only [L, rep] at hACL
    generalize hCanonical : (@coordinatePermACLRepresentative n q) = Rep at hACL hBaseProducer hNormProducer
    obtain ⟨hW, hEnergy, hRange, K, hRaw, hEnd⟩ := hBaseProducer (hACL normal) z hLineV
    have hNorm := hNormProducer (hACL normal) z hLineV M hM
    obtain ⟨_hIntegrable, hPair⟩ := coordinate_line_pair_energy_integrable (p normal) y (-1) 1 ε Dw
      ha hb (fun l => (hACL normal z l hΩ).2.2.1)
    rw [← hPair] at hEnergy
    refine ⟨?_, ?_, ?_, ?_, K, ?_, ?_⟩
    · with_reducible simpa only [V1, D1, axis] using hW
    · with_reducible simpa only [D1, A, D, point, axis, v, j, p, normal, y, B, hColumn] using hEnergy
    · with_reducible simpa only [V1, A, D, point, axis, v, j, p, normal, y, B, hColumn] using hRange
    · with_reducible simpa only [V1, axis] using hNorm
    · with_reducible simpa only [V1, axis, e] using hRaw
    · with_reducible simpa only [face, U1, source1, T1, point, axis, v, j, p, normal, y, C, hColumn,
        Fin.sum_univ_one, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul,
        Function.comp_def] using hEnd
  have hTraces (c : Cell) := (hCellData c).2.2.2.2
  choose K1 hRaw hEnd using hTraces
  refine ⟨fun c => (hCellData c).1, fun c => (hCellData c).2.1, ?_,
    fun c => (hCellData c).2.2.1, fun c => (hCellData c).2.2.2.1, K1, hRaw, hEnd⟩
  intro c
  apply add_nonneg
  · exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) hε.le
  · exact Real.sqrt_nonneg _

end StratificationTheory
