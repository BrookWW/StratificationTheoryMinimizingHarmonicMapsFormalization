module

public import StratificationTheory.Interpolation.PositiveSquarePrismConnector
public import StratificationTheory.Foundation.OriginalClosedTargetFaceGridJoint
public import StratificationTheory.Foundation.CoordinateEdgePrismInputs
public import StratificationTheory.Foundation.TwoVectorSquareTraceTransport
public import StratificationTheory.Foundation.GridCubeBallContainment

/-!
# First prism cells from the original ball pair on one selected lattice

One original ball pair determines a single offset. Every contained square in the
first two coordinate directions of that lattice has an actual three-dimensional
connector, with the original square and edge energies, target-distance
bound and all six original signed boundary trace classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The original source produces every square and edge input of the actual
first prism cell inside the proof, on the same selected lattice. -/
theorem exists_original_ball_two_face_prism_cells {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 2)) ((n : ℝ) + 3)) (w l) (Dw l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)), w l x ∈ N)
    {ε : ℝ} (hε : 0 < ε) :
    let coord : Fin 2 ↪ Fin (n + 2) :=
      ⟨fun i => ⟨i.val, by omega⟩, by intro i j hij; exact Fin.ext (congrArg (fun k : Fin (n + 2) => k.val) hij)⟩
    let vec := fun i : Fin 2 => EuclideanSpace.single (coord i) (1 : ℝ)
    let p := fun i : Fin 2 => Equiv.swap (Fin.last (n + 1)) (coord i)
    let other₀ := fun i : Fin 2 => (Equiv.swap (0 : Fin 2) 1) i
    let rep := fun (l : Fin 2) (i : Fin 2) => coordinatePermACLRepresentative (p i) (-1) 1 (w l) (Dw l)
    let embed := fun (y : Domain (n + 2)) (t : Domain 2) => y + t 0 • vec 0 + t 1 • vec 1
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    ∃ offset : Fin (n + 2) → ℝ,
      (∀ j, offset j ∈ Ico (0 : ℝ) ε) ∧
      ∀ z : Submodule.span ℤ (Set.range grid),
      let y := WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
      let u := fun (l : Fin 2) (t : Domain 2) => w l (embed y t)
      let Du := fun (l : Fin 2) (t : Domain 2) (j : Fin 2) => Dw l (embed y t) (coord j)
      let F := fun (i : Fin 2) (side : Bool) (l : Fin 2) (s : ℝ) =>
        rep l (other₀ i) (embed y (cubicalSignedFaceIsometry 1 i true
          ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
            (EuclideanSpace.single (0 : Fin 1) s,
              EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))))
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let δ := fun side : Bool => if side then ε else 0
    let index := fun side : Bool => if side then (1 : Fin 2) else 0
    let other := fun i : Fin 2 => (Equiv.swap (0 : Fin 2) 1) i
    let edgePoint := fun (i : Fin 2) (side : Bool) (s : ℝ) =>
      cubicalSignedFaceIsometry 1 i true
        (b.symm (EuclideanSpace.single (0 : Fin 1) s, EuclideanSpace.single (0 : Fin 1) (δ side)))
    let f := fun i side l s => u l (edgePoint i side s)
    let g := fun i side l s => Du l (edgePoint i side s) (other i)
    let P : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let _S₀ := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let B : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let _S := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let Ω : OpenDomain 3 :=
      ⟨⋂ j : Fin 3, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 3 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let A : Domain 2 := WithLp.toLp 2 (fun _ => ε / 2)
    let T := fun z : Domain 2 => A + (ε / 2) • z
    let U := fun side : Bool => u (index side) ∘ T
    let _DU := fun (side : Bool) (z : Domain 2) j => (ε / 2) • Du (index side) (T z) j
    let V := fun (i : Fin 2) (side : Bool) (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F i side 0 ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F i side 1 ((b (T z)).1 0)
    let _DV := fun (i : Fin 2) (side : Bool) (z : Domain 2) j => (ε / 2) •
      Fin.addCases (motive := fun _ : Fin (1 + 1) => Ambient q)
        (fun _ : Fin 1 => (1 - (b (T z)).2 0 / ε) • g i side 0 ((b (T z)).1 0) +
          ((b (T z)).2 0 / ε) • g i side 1 ((b (T z)).1 0))
        (fun _ : Fin 1 => ε⁻¹ • (F i side 1 ((b (T z)).1 0) - F i side 0 ((b (T z)).1 0))) j
    let _E := fun z : Domain 3 =>
      (1 - (z 2 + 1) / 2) • U false (WithLp.toLp 2 ![z 0, z 1]) +
        ((z 2 + 1) / 2) • U true (WithLp.toLp 2 ![z 0, z 1])
    let Dedge := fun i side => ∫ s in Ioo (0 : ℝ) ε, ‖f i side 0 s - f i side 1 s‖ ^ 2
    let Aedge := fun i side => ∫ s in Ioo (0 : ℝ) ε, ‖g i side 0 s‖ ^ 2 + ‖g i side 1 s‖ ^ 2
    let Qface := cubicalSignedFaceIsometry 1 (0 : Fin 2) true
    let face := fun j : Fin 3 × Bool =>
      if j.1 = 0 then V 0 j.2 ∘ Qface else if j.1 = 1 then V 1 j.2 else U j.2
    (∀ t : Domain 2, (∀ j, t j ∈ Icc (0 : ℝ) ε) →
      ∀ j : Fin (n + 2), (embed y t) j ∈ Ioo (-1 : ℝ) 1) →
    ∃ (G : Domain 3 → Ambient q) (D : Domain 3 → Gradient 3 q),
      let W := fun z : Domain 3 => G (‖WithLp.ofLp z‖⁻¹ • z)
      (∀ j x, x ∈ B.val → G (cubicalSignedFaceIsometry 2 j.1 j.2
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = face j x) ∧
      MemW12 Ω W D ∧
      (∫ z in Ω.val, hsNormSq (D z)) ≤ 3 *
        ((∑ l : Fin 2, ∫ z in P.val, hsNormSq (Du l z)) +
          (∑ i : Fin 2, ∑ side : Bool,
            ((ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖g i side 0 s‖ ^ 2) +
              ∫ s in Ioo (0 : ℝ) ε, ‖g i side 1 s‖ ^ 2) + ε⁻¹ * Dedge i side))) ∧
      (∀ᵐ z ∂volume.restrict Ω.val, (infDist (W z) N) ^ 2 ≤
        ∑ i : Fin 2, ∑ side : Bool, (Dedge i side / ε + Real.sqrt (2 * Dedge i side * Aedge i side))) ∧
      ∃ K : Fin 3 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => W (cubicalSignedFaceIsometry 2 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
            K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (cubicalSignedFaceIsometry 2 i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i positive,
          (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
            by cases positive <;> norm_num⟩ : Domain 2 → Ambient q) =ᵐ[volume.restrict B.val] face (i, positive) := by
  intro coord vec p other₀ rep embed grid
  let Ssource : Set (Domain (n + 1)) :=
    ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
  let esource := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
  let Qsource := fun i : Fin 2 => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
  let face₁ : Fin 2 → (Fin 1 ↪ Fin (n + 2)) := fun i =>
    ⟨fun _ => coord (other₀ i), fun _ _ _ => Subsingleton.elim _ _⟩
  have hNormal (i : Fin 2) : p i (Fin.natAdd (n + 1) (0 : Fin 1)) = coord i :=
    Equiv.swap_apply_left _ _
  have hOther (i : Fin 2) : other₀ i ≠ i := by fin_cases i <;> decide
  have hFace : ∀ (i : Fin 2) (j : Fin 1), face₁ i j ≠ p i (Fin.natAdd (n + 1) (0 : Fin 1)) := by
    intro i j hij
    have h := coord.injective (hij.trans (hNormal i))
    exact hOther i h
  have hSsource : MeasurableSet Ssource := MeasurableSet.iInter fun j : Fin (n + 1) =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj j).continuous.measurable
  have hRect : ∀ (i : Fin 2) (x : Domain (n + 1)), x ∈ Ssource → ∀ t ∈ Ioo (-1 : ℝ) 1,
      Qsource i (esource.symm (x, EuclideanSpace.single (0 : Fin 1) t)) ∈
        ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by
    intro i x hx t ht
    have h := unit_coordinate_line_rectangle_mem_ball (p i) x (fun j => mem_iInter.mp hx j) ht
    have hRadius : (((n + 1 : ℕ) : ℝ) + 2) = (n : ℝ) + 3 := by push_cast; ring
    rw [hRadius] at h
    exact h
  obtain ⟨offset, hoffset, hweak, hACL, _hVertexN, hFiber, _hEnergy, _hDiscrepancy, hTrace⟩ :=
    exists_grid_translate_original_closed_target_face_joint (n := n + 1) (q := q)
      (ι := Fin 2) (J := Unit) (by positivity : 0 < (n : ℝ) + 3) w Dw hSob hN hTarget
      (fun _ => 1) p face₁ hFace (fun _ => Ssource) (fun _ => hSsource)
      (fun _ => -1) (fun _ => 1) (fun _ => by norm_num) hRect
      (fun _ => 2) (fun _ => coord) hε
  refine ⟨offset, hoffset, ?_⟩
  intro z y u Du F b e δ index other edgePoint f g P S₀ B S Ω A T U DU V DV E Dedge Aedge Qface face hCell
  have hAxis (i : Fin 2) (x : Domain 1) (t : ℝ) :
      embed y (cubicalSignedFaceIsometry 1 i true (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))) =
        (y + t • vec i) + x 0 • vec (other i) := by
    have h := two_vector_square_axis y (vec 0) (vec 1) i x t
    fin_cases i <;> simpa [embed, b, other] using h
  have hδ (side : Bool) : δ side ∈ Icc (0 : ℝ) ε := by cases side <;> simp [δ, hε.le]
  have hEdgeUnit (i : Fin 2) (side : Bool) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) ε) :
      ∀ j, (embed y (edgePoint i side s)) j ∈ Ioo (-1 : ℝ) 1 := by
    apply hCell
    intro j
    dsimp only [edgePoint]
    rw [positive_square_axis_coordinates]
    fin_cases i <;> fin_cases j <;> simp [hs, hδ side]
  have hEdgePath (i : Fin 2) (side : Bool) (s : ℝ) :
      embed y (edgePoint i side s) = y + δ side • vec i + s • vec (other i) := by
    simpa only [PiLp.single_apply, ite_true] using hAxis i (EuclideanSpace.single 0 s) (δ side)
  have hΩsource (i : Fin 2) (x : Domain (n + 2)) (hx : ∀ j, x j ∈ Ioo (-1 : ℝ) 1) :
      (esource ((Qsource i).symm x)).1 ∈ Ssource ∧
        (esource ((Qsource i).symm x)).2 0 ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · apply mem_iInter.mpr
      intro j
      change (esource ((Qsource i).symm x)).1 j ∈ Ioo (-1 : ℝ) 1
      rw [coordinate_split_first_eq]
      exact hx _
    · rw [coordinate_split_last_eq]
      exact hx _
  have hBall (t : Domain 2) (ht : t ∈ P.val) : embed y t ∈
      ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by
    have hc := hCell t (fun j => ⟨(mem_iInter.mp ht j).1.le, (mem_iInter.mp ht j).2.le⟩)
    rw [mem_ball_zero_iff]
    have hnorm := euclidean_norm_le_dim_of_coordinate_bound (embed y t)
      (fun j => abs_le.mpr ⟨(hc j).1.le, (hc j).2.le⟩)
    push_cast at hnorm
    linarith only [hnorm]
  have hNative (t : Domain 2) :
      y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ) = embed y t := by
    rw [Fin.sum_univ_two]
    dsimp only [embed, vec]
    abel
  have hSobLocal (l : Fin 2) : MemW12 P (u l) (Du l) := by
    have h := hweak z () P (fun t ht => by
      change y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ) ∈ _
      rw [hNative]
      exact hBall t ht)
    fin_cases l
    · have h₀ := h.1
      change MemW12 P (fun t => w (0 : Fin 2) (embed y t))
        (fun t s => Dw (0 : Fin 2) (embed y t) (coord s))
      change MemW12 P (fun t => w 0 (y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ)))
        (fun t s => Dw 0 (y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ)) (coord s)) at h₀
      simpa only [hNative] using h₀
    · have h₁ := h.2
      change MemW12 P (fun t => w (1 : Fin 2) (embed y t))
        (fun t s => Dw (1 : Fin 2) (embed y t) (coord s))
      change MemW12 P (fun t => w 1 (y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ)))
        (fun t s => Dw 1 (y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ)) (coord s)) at h₁
      simpa only [hNative] using h₁
  have hTargetLocal (l : Fin 2) : ∀ᵐ t ∂volume.restrict P.val, u l t ∈ N := by
    have hsub : P.val ⊆ ⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε := by
      intro t ht
      exact mem_iInter.mpr fun j => ⟨(mem_iInter.mp ht j).1.le, (mem_iInter.mp ht j).2⟩
    have h := (hFiber () z).filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
    filter_upwards [h, ae_restrict_mem P.property.measurableSet] with t ht htP
    have hBall' : y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ) ∈
        ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by rw [hNative]; exact hBall t htP
    have hN := ht.2 l hBall'
    change w l (y + ∑ j : Fin 2, t j • EuclideanSpace.single (coord j) (1 : ℝ)) ∈ N at hN
    rw [hNative] at hN
    exact hN
  have hStep := fun i : Fin 2 => exists_scaled_grid_neighbor hε offset z (coord i)
  choose zs hzs using hStep
  let ze := fun (i : Fin 2) (side : Bool) => if side then zs i else z
  let ye := fun i side => WithLp.toLp 2 (((ze i side : Submodule.span ℤ (Set.range grid)) : Fin (n + 2) → ℝ) + offset)
  have hYE (i : Fin 2) (side : Bool) : ye i side = y + δ side • vec i := by
    cases side
    · simp [ye, ze, δ, y]
    · exact hzs i
  have hPath (i : Fin 2) (side : Bool) (s : ℝ) :
      embed y (edgePoint i side s) = ye i side + s • vec (other i) := by rw [hYE, hEdgePath]
  have hEndStep := fun (i : Fin 2) (side : Bool) =>
    exists_scaled_grid_neighbor hε offset (ze i side) (coord (other i))
  choose zt hzt using hEndStep
  have hEndPoint (i : Fin 2) (side : Bool) :
      WithLp.toLp 2 (((zt i side : Submodule.span ℤ (Set.range grid)) : Fin (n + 2) → ℝ) + offset) =
        embed y (edgePoint i side ε) := by rw [hzt, hPath]
  have hEdgeData (i : Fin 2) (side : Bool) (l : Fin 2) :
      MemLp (f i side l) 2 (volume.restrict (Ioo (0 : ℝ) ε)) ∧
      MemLp (g i side l) 2 (volume.restrict (Ioo (0 : ℝ) ε)) ∧
      (F i side l) =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] f i side l ∧
      (∀ s ∈ Icc (0 : ℝ) ε, ∀ t ∈ Icc (0 : ℝ) ε,
        F i side l t - F i side l s = ∫ r in s..t, g i side l r) ∧
      (∀ s ∈ Icc (0 : ℝ) ε, F i side l s ∈ N) ∧
      ∀ positive : Bool, F i side l (δ positive) = f i side l (δ positive) := by
    have hyUnit : ∀ j, ye i side j ∈ Ioo (-1 : ℝ) 1 := by
      have h := hEdgeUnit i side 0 ⟨le_rfl, hε.le⟩
      simpa only [hPath, zero_smul, add_zero] using h
    have hSource := hACL (ze i side) l (other i) (hΩsource (other i) (ye i side) hyUnit)
    generalize hYdef : WithLp.toLp 2
      (((ze i side : Submodule.span ℤ (Set.range grid)) : Fin (n + 2) → ℝ) + offset) = y₀ at hSource
    have hy₀ : y₀ = ye i side := hYdef.symm
    have hEndRaw : rep l (other i) (ye i side + ε • vec (other i)) =
        w l (ye i side + ε • vec (other i)) := by
      have h := (hACL (zt i side) l (other i)
        (hΩsource (other i) _ (by rw [hEndPoint]; exact hEdgeUnit i side ε ⟨hε.le, le_rfl⟩))).1
      simpa only [hzt] using h
    have hLower : (-1 : ℝ) ≤ (ye i side) (p (other i) (Fin.natAdd (n + 1) (0 : Fin 1))) :=
      (hyUnit _).1.le
    have hUpper : (ye i side) (p (other i) (Fin.natAdd (n + 1) (0 : Fin 1))) + ε ≤ 1 := by
      have h := hEdgeUnit i side ε ⟨hε.le, le_rfl⟩ (coord (other i))
      rw [hPath] at h
      simp only [vec, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
        smul_eq_mul, mul_one] at h
      simpa only [hNormal] using h.2.le
    let line₀ := fun t : ℝ => Qsource (other i) (esource.symm
      ((esource ((Qsource (other i)).symm y₀)).1, EuclideanSpace.single (0 : Fin 1) t))
    have hAEfull : (rep l (other i) ∘ line₀) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
        (w l ∘ line₀) := by
      filter_upwards [hSource.2.2.2.2.1] with t ht
      simpa only [rep, line₀, Qsource, esource, Function.comp_def] using ht
    let γ := fun s : ℝ => embed y (edgePoint i side s)
    have hData := coordinate_edge_prism_inputs (n := n + 1) (q := q)
      (p (other i)) y₀ hε (w l) (rep l (other i)) (Dw l) γ (F i side l) (f i side l) (g i side l)
      (N := N) (by intro s; rw [hy₀, hNormal]; exact hPath i side s)
      (fun _ => rfl) (fun _ => rfl) (by intro s; simp only [hNormal]; rfl)
      (by rw [hy₀]; exact hLower) (by rw [hy₀]; exact hUpper) hSource.2.1 hSource.2.2.1 hAEfull
      (fun t ht => hSource.2.2.2.2.2.1 t ht)
      (fun s hs t ht => by simpa only [rep, Qsource, esource, Function.comp_def] using
        hSource.2.2.2.2.2.2 s hs t ht) hSource.1 (by simpa only [hy₀, hNormal, vec] using hEndRaw)
    exact hData
  let P₁ : OpenDomain 1 := ⟨S₀, isOpen_iInter_of_finite fun j : Fin 1 =>
    isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
  have hP₁finite : (volume : Measure (Domain 1)) P₁.val ≠ ⊤ := by
    rw [volume_native_positive_cube 1 hε]
    exact ENNReal.ofReal_ne_top
  have hOriginUnit : ∀ j, y j ∈ Ioo (-1 : ℝ) 1 := by
    have h := hCell 0 (by intro j; simp [hε.le])
    simpa only [embed, PiLp.zero_apply, zero_smul, add_zero] using h
  have hTraceData (l i : Fin 2) := hTrace z l i
    (by simpa only [hNormal] using hOriginUnit (coord i))
    (by
      have h := hEdgeUnit i true 0 ⟨le_rfl, hε.le⟩ (coord i)
      rw [hEdgePath] at h
      simpa only [δ, ite_true, zero_smul, add_zero, vec, PiLp.add_apply,
        PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one, hNormal] using h)
    P₁ hP₁finite (by
      intro x hx
      have hs : x 0 ∈ Icc (0 : ℝ) ε := ⟨(mem_iInter.mp hx 0).1.le, (mem_iInter.mp hx 0).2.le⟩
      have hUnit := hEdgeUnit i false (x 0) hs
      have hBase := (hΩsource i _ hUnit).1
      have hPoint : y + (∑ s : Fin 1, x s • EuclideanSpace.single (face₁ i s) (1 : ℝ)) =
          embed y (edgePoint i false (x 0)) := by
        rw [hEdgePath]
        simp only [δ, Bool.false_eq_true, ite_false, zero_smul, add_zero, Fin.sum_univ_one, face₁]
        rfl
      change (esource ((Qsource i).symm (y + ∑ s : Fin 1,
        x s • EuclideanSpace.single (face₁ i s) (1 : ℝ)))).1 ∈ Ssource
      rw [hPoint]
      exact hBase)
  choose H hHraw hHleft hHright _hHunique using hTraceData
  have hSourceH : ∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x : Domain 1 => w l (y + x 0 • vec (other i) + t • vec i))
        2 (volume.restrict S₀), H l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _ := by
    intro l i
    simpa only [Fin.sum_univ_one, face₁, Function.Embedding.coeFn_mk, hNormal,
      vec, other, other₀, y, P₁] using hHraw l i
  have hSourceEnd : ∀ l i positive,
      ∃ hs : MemLp (fun x : Domain 1 => w l (y + δ positive • vec i + x 0 • vec (other i)))
        2 (volume.restrict S₀),
      H l i ⟨δ positive, by cases positive <;> simp [δ, hε.le],
        by cases positive <;> simp [δ, hε.le]⟩ = hs.toLp _ := by
    intro l i positive
    cases positive
    · simpa only [δ, Bool.false_eq_true, ite_false, zero_smul, add_zero,
        Fin.sum_univ_one, face₁, Function.Embedding.coeFn_mk, vec, other, other₀, y, P₁] using hHleft l i
    · simpa only [δ, ite_true, Fin.sum_univ_one, face₁, Function.Embedding.coeFn_mk,
        hNormal, vec, other, other₀, y, P₁] using hHright l i
  obtain ⟨hH, hHEnd⟩ := two_vector_square_original_trace_transport hε w y vec H hSourceH hSourceEnd
  dsimp only [face, V, U]
  generalize hFdef : F = F₀ at hEdgeData ⊢
  have hResult := exists_positive_square_pair_prism_connector (q := q) hε u Du F₀ hN hSobLocal hTargetLocal
    (fun i side l => (hEdgeData i side l).1) (fun i side l => (hEdgeData i side l).2.1)
    (fun i side l => (hEdgeData i side l).2.2.1) (fun i side l s hs t ht => (hEdgeData i side l).2.2.2.1 s hs t ht)
    (fun i side l s hs => (hEdgeData i side l).2.2.2.2.1 s hs) (fun i side l positive => (hEdgeData i side l).2.2.2.2.2 positive)
    H hH hHEnd
  obtain ⟨G, D, hCap, hW, hEnergy, hDistance, K, hK, hKEnd⟩ := hResult
  refine ⟨G, D, ?_, hW, hEnergy, hDistance, K, ?_, ?_⟩
  · intro j x hx
    simpa only [Qface, b, T, A] using hCap j x hx
  · intro i
    exact hK i
  · intro i positive
    filter_upwards [hKEnd i positive] with x hx
    simpa only [Qface, b, T, A] using hx

end StratificationTheory
