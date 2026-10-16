module

public import StratificationTheory.Interpolation.OriginalAllRankBaseGrid
public import StratificationTheory.Interpolation.OriginalSelectedCoordinateFaceUnitData

public section

open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- One original selected grid retains the complete original qualifications,
actual rank-zero and rank-one bases, and the same normalized original face
graphs with all native signed-face endpoint classes in every positive rank. -/
theorem exists_original_ball_all_rank_unit_grid {n q : ℕ}
    (w : Fin 2 → Domain ((n + 1) + 1) → Ambient q)
    (Dw : Fin 2 → Domain ((n + 1) + 1) → Gradient ((n + 1) + 1) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3)) (w l) (Dw l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3)), w l x ∈ N)
    {ε : ℝ} (hε : 0 < ε) :
    let I := (r : Fin ((n + 1) + 1)) × {v : (Fin r.val ↪ Fin ((n + 1) + 1)) × Fin ((n + 1) + 1) //
      ∀ s, v.1 s ≠ v.2}
    let J := (r : Fin ((n + 1) + 2)) × (Fin r.val ↪ Fin ((n + 1) + 1))
    let k : I → ℕ := fun i => i.1.val
    let p : I → Equiv.Perm (Fin ((n + 1) + 1)) := fun i => Equiv.swap (Fin.last (n + 1)) i.2.val.2
    let face : (i : I) → Fin (k i) ↪ Fin ((n + 1) + 1) := fun i => i.2.val.1
    let S : I → Set (Domain (n + 1)) := fun _ => ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let a : I → ℝ := fun _ => -1
    let b : I → ℝ := fun _ => 1
    let d : J → ℕ := fun j => j.1.val
    let sampleFace : (j : J) → Fin (d j) ↪ Fin ((n + 1) + 1) := fun j => j.2
    let E := (ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let D := (ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3)).indicator (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := (n + 1)) (m := 1)
    let normal := fun i => p i (Fin.natAdd (n + 1) (0 : Fin 1))
    let v := fun i => EuclideanSpace.single (normal i) (1 : ℝ)
    let β := fun i (y : Domain ((n + 1) + 1)) => (e ((Q i).symm y)).1
    let B := fun i (t : Domain (k i)) =>
      ∑ s : Fin (k i), t s • EuclideanSpace.single (face i s) (1 : ℝ)
    let W := fun l i => coordinatePermACLRepresentative (p i) (a i) (b i) (w l) (Dw l)
    let line := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let Ω := fun i => {y : Domain ((n + 1) + 1) |
      β i y ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let L := fun (l : Fin 2) (i : I) (y : Domain ((n + 1) + 1)) => y ∈ Ω i →
      W l i y = w l y ∧
      MemLp (fun t => w l (line i (β i y) t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
      MemLp (fun t => Dw l (line i (β i y) t) (normal i))
        2 (volume.restrict (Ioo (a i) (b i))) ∧
      AbsolutelyContinuousOnInterval (fun t => W l i (line i (β i y) t)) (a i) (b i) ∧
      (fun t => W l i (line i (β i y) t)) =ᵐ[volume.restrict (Ioo (a i) (b i))]
        (fun t => w l (line i (β i y) t)) ∧
      (∀ t ∈ Icc (a i) (b i), W l i (line i (β i y) t) ∈ N) ∧
      ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
        W l i (line i (β i y) t) - W l i (line i (β i y) s) =
          ∫ r in s..t, Dw l (line i (β i y) r) (normal i)
    let A := fun j (y : Domain ((n + 1) + 1)) (t : Domain (d j)) =>
      y + ∑ s : Fin (d j), t s • EuclideanSpace.single (sampleFace j s) (1 : ℝ)
    let G : Domain ((n + 1) + 1) → Prop := fun y => ∀ (j : J) (U : OpenDomain (d j)),
      (∀ t ∈ U.val, A j y t ∈ ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3)) →
      MemW12 U (fun t => w 0 (A j y t)) (fun t s => Dw 0 (A j y t) (sampleFace j s)) ∧
      MemW12 U (fun t => w 1 (A j y t)) (fun t s => Dw 1 (A j y t) (sampleFace j s))
    let grid := (Pi.basisFun ℝ (Fin ((n + 1) + 1))).isUnitSMul
      (w := fun _j : Fin ((n + 1) + 1) => ε) (fun _j => hε.ne'.isUnit)
    let C := fun j => ⋂ s : Fin (d j), (EuclideanSpace.proj s) ⁻¹' Ico (0 : ℝ) ε
    ∃ offset : Fin ((n + 1) + 1) → ℝ,
      (∀ s, offset s ∈ Ico (0 : ℝ) ε) ∧
      (
    ∀ z : Submodule.span ℤ (Set.range grid),
    let y := WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)
    (∀ i, y i ∈ Ioo (-1 : ℝ) 1) →
    let B : OpenDomain 1 :=
      ⟨⋂ i : Fin 1, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let C : Set (Domain 0) := ⋂ i : Fin 0, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 0) (m := 1)
    (∀ l, w l y ∈ N) ∧
    MemW12 B (rawVertexUnitChord w y) (rawVertexUnitGradient w y) ∧
    (∀ M : ℝ, (∀ v ∈ N, ‖v‖ ≤ M) → ∀ x : Domain 1, x 0 ∈ Icc (-1 : ℝ) 1 →
      ‖rawVertexUnitChord w y x‖ ≤ M) ∧
    (∀ x : Domain 1, x 0 ∈ Icc (-1 : ℝ) 1 →
      (infDist (rawVertexUnitChord w y x) N) ^ 2 ≤ ‖w 0 y - w 1 y‖ ^ 2) ∧
    ∃ K : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ t : Icc (-1 : ℝ) 1, ∃ hs : MemLp
        (fun x : Domain 0 => rawVertexUnitChord w y (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
          2 (volume.restrict C), K t = hs.toLp
        (fun x : Domain 0 => rawVertexUnitChord w y (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      ∀ side : Bool, ∃ hs : MemLp (fun _ : Domain 0 => w (if side then 1 else 0) y)
          2 (volume.restrict C),
        K ⟨if side then 1 else -1, by cases side <;> norm_num, by cases side <;> norm_num⟩ =
          hs.toLp (fun _ : Domain 0 => w (if side then 1 else 0) y)) ∧
      (
    ∀ normal₀ : Fin ((n + 1) + 1),
    let p₀ := Equiv.swap (Fin.last (n + 1)) normal₀
    let j := p₀ (Fin.natAdd (n + 1) (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    ∀ z : Submodule.span ℤ (Set.range grid),
    let y := WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)
    (∀ s ∈ Icc (0 : ℝ) ε, ∀ i, (y + s • v) i ∈ Ioo (-1 : ℝ) 1) →
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let B : OpenDomain 2 :=
      ⟨⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin 2 =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let C : Set (Domain 1) := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let edge := fun (l : Fin 2) (x : Domain 1) => w l (y + (ε / 2 + (ε / 2) * x 0) • v)
    let V := coordinateEdgeUnitMap p₀ (-1) 1 ε w Dw y
    let DV := coordinateEdgeUnitGradient p₀ (-1) 1 ε w Dw y
    let D := ∫ s in Ioo (0 : ℝ) ε, ‖w 0 (y + s • v) - w 1 (y + s • v)‖ ^ 2
    let E := ∫ s in Ioo (0 : ℝ) ε, ‖Dw 0 (y + s • v) j‖ ^ 2 + ‖Dw 1 (y + s • v) j‖ ^ 2
    let face := fun (i : Fin 2) (side : Bool) => if i = 0 then
      rawVertexUnitChord w (y + (if side then ε else 0) • v) else edge (if side then 1 else 0)
    (MemW12 B V DV ∧
      (∫ z in B.val, hsNormSq (DV z)) ≤
        (ε / 2) * ((∫ s in Ioo (0 : ℝ) ε, ‖Dw 0 (y + s • v) j‖ ^ 2) +
          ∫ s in Ioo (0 : ℝ) ε, ‖Dw 1 (y + s • v) j‖ ^ 2) + ε⁻¹ * D ∧
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
            by cases side <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict C] face i side) ∧
    (∀ M : ℝ, (∀ v ∈ N, ‖v‖ ≤ M) → ∀ x : Domain 2,
      (∀ i, x i ∈ Icc (-1 : ℝ) 1) → ‖V x‖ ≤ M)) ∧
      (∀ z : Submodule.span ℤ (Set.range grid),
        G (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset))) ∧
      (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) (i : I),
        L l i (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset))) ∧
      (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2),
        WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset) ∈ ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3) →
          w l (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)) ∈ N) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range grid)),
        ∀ᵐ t ∂volume.restrict (C j),
          (∀ (l : Fin 2) (i : I), L l i (A j (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)) t)) ∧
          ∀ l : Fin 2,
            A j (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)) t ∈ ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3) →
              w l (A j (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)) t) ∈ N) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          E (A j (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ ((n + 1) + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
                ((∫ x in ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
                 (∫ x in ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)))) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          D (A j (WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ ((n + 1) + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal (∫ x in ball (0 : Domain ((n + 1) + 1)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2)) ∧
      (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) (i : I),
        let y := WithLp.toLp 2 ((z : Fin ((n + 1) + 1) → ℝ) + offset)
        y (normal i) ∈ Ioo (a i) (b i) →
        y (normal i) + ε ∈ Ioo (a i) (b i) →
        ∀ U : OpenDomain (k i), (volume : Measure (Domain (k i))) U.val ≠ ⊤ →
        (∀ s ∈ U.val, β i (y + B i s) ∈ S i) →
        ∃ H : C(Icc (0 : ℝ) ε,
            Lp (Ambient q) 2 ((volume : Measure (Domain (k i))).restrict U.val)),
          (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
            ∃ hslice : MemLp (fun s => w l (y + B i s + r • v i)) 2 (volume.restrict U.val),
              H ⟨r, hr.1.le, hr.2.le⟩ =
                hslice.toLp (fun s => w l (y + B i s + r • v i))) ∧
          (∃ hleft : MemLp (fun s => w l (y + B i s)) 2 (volume.restrict U.val),
            H ⟨0, le_rfl, hε.le⟩ = hleft.toLp (fun s => w l (y + B i s))) ∧
          (∃ hright : MemLp (fun s => w l (y + ε • v i + B i s)) 2 (volume.restrict U.val),
            H ⟨ε, hε.le, le_rfl⟩ = hright.toLp (fun s => w l (y + ε • v i + B i s))) ∧
          ∀ K : C(Icc (0 : ℝ) ε,
              Lp (Ambient q) 2 ((volume : Measure (Domain (k i))).restrict U.val)),
            (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
              ∃ hslice : MemLp (fun s => w l (y + B i s + r • v i)) 2 (volume.restrict U.val),
                K ⟨r, hr.1.le, hr.2.le⟩ =
                  hslice.toLp (fun s => w l (y + B i s + r • v i))) → K = H) ∧
      ∀ (r : Fin (n + 2)) (coord : Fin (r.val + 1) ↪ Fin (n + 2))
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
    (∀ l, ∀ᵐ z ∂volume.restrict B.val, U l z ∈ N) ∧
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
              (cubicalSignedFaceIsometry r.val i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  classical
  intro I J k p face S a b d sampleFace E D Q e normal v β B W line Ω L A G grid C
  have hRadius : (((n + 1 : ℕ) : ℝ) + 2) = (n : ℝ) + 3 := by push_cast; ring
  obtain ⟨offset, hoffset, hVertexBase, hEdgeBase, hWeak, hACL, hVertex, hFiber,
      hEnergy, hDiscrepancy, hTrace⟩ :=
    exists_original_ball_all_rank_base_grid (n := n + 1) w Dw
      (by simpa only [hRadius] using hSob) hN
      (by simpa only [hRadius] using hTarget) hε
  simp only [hRadius] at hWeak hVertex hFiber hEnergy hDiscrepancy
  refine ⟨offset, hoffset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_reducible exact hVertexBase
  · with_reducible exact hEdgeBase
  · with_reducible exact hWeak
  · with_reducible exact hACL
  · with_reducible exact hVertex
  · with_reducible exact hFiber
  · with_reducible exact hEnergy
  · with_reducible exact hDiscrepancy
  · with_reducible exact hTrace
  · intro r coord z y hCell P₀ B₀ C₀ e₀ source u Du T U DU
    let j : J := ⟨⟨r.val + 1, by omega⟩, coord⟩
    have hRawWeak := hWeak z j
    have hRawTarget := (hFiber j z).mono fun _ ht => ht.2
    have hRawHigher (base : Fin r.val ↪ Fin (n + 2)) (normal₀ : Fin (n + 2))
        (hbase : ∀ s, base s ≠ normal₀) (l : Fin 2) :=
      hTrace z l (⟨r, ⟨(base, normal₀), hbase⟩⟩ : I)
    apply original_selected_coordinate_face_unit_data (d := r.val) hε w Dw coord y
    · with_reducible simpa only [j, y, Function.comp_def] using hRawWeak
    · with_reducible simpa only [j, y, Function.comp_def] using hRawTarget
    · intro base normal₀ hbase
      have h := hRawHigher base normal₀ hbase
      dsimp only at h
      have hNormal : (Equiv.swap (Fin.last (n + 1)) normal₀)
          (Fin.natAdd (n + 1) (0 : Fin 1)) = normal₀ := Equiv.swap_apply_left _ _
      with_reducible simpa only [hNormal, y, mem_iInter, mem_preimage, PiLp.proj_apply] using h
    · exact hCell

end StratificationTheory
