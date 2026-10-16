module
public import StratificationTheory.Interpolation.OriginalAllRankQualifiedGrid
public import StratificationTheory.Interpolation.OriginalSelectedVertexChordBase
public import StratificationTheory.Interpolation.OriginalSelectedCoordinateEdgeBase
public import StratificationTheory.Interpolation.OriginalSelectedCoordinateEdgeNorm

/-!
# Actual vertex and edge bases on one original all-rank lattice

One original joint selection retains all native face and trace events and
produces the genuine rank-zero and rank-one connector families on that
same lattice, with the original common norm bound and raw boundary classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- One original source selection gives all original higher face data and
both actual induction bases without external qualification assumptions. -/
theorem exists_original_ball_all_rank_base_grid {n q : ℕ}
    (w : Fin 2 → Domain (n + 1) → Ambient q)
    (Dw : Fin 2 → Domain (n + 1) → Gradient (n + 1) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 1)) ((n : ℝ) + 2)) (w l) (Dw l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 1)) ((n : ℝ) + 2)), w l x ∈ N)
    {ε : ℝ} (hε : 0 < ε) :
    let I := (r : Fin (n + 1)) × {v : (Fin r.val ↪ Fin (n + 1)) × Fin (n + 1) //
      ∀ s, v.1 s ≠ v.2}
    let J := (r : Fin (n + 2)) × (Fin r.val ↪ Fin (n + 1))
    let k : I → ℕ := fun i => i.1.val
    let p : I → Equiv.Perm (Fin (n + 1)) := fun i => Equiv.swap (Fin.last n) i.2.val.2
    let face : (i : I) → Fin (k i) ↪ Fin (n + 1) := fun i => i.2.val.1
    let S : I → Set (Domain n) := fun _ => ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let a : I → ℝ := fun _ => -1
    let b : I → ℝ := fun _ => 1
    let d : J → ℕ := fun j => j.1.val
    let sampleFace : (j : J) → Fin (d j) ↪ Fin (n + 1) := fun j => j.2
    let E := (ball (0 : Domain (n + 1)) ((n : ℝ) + 2)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let D := (ball (0 : Domain (n + 1)) ((n : ℝ) + 2)).indicator (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let normal := fun i => p i (Fin.natAdd n (0 : Fin 1))
    let v := fun i => EuclideanSpace.single (normal i) (1 : ℝ)
    let β := fun i (y : Domain (n + 1)) => (e ((Q i).symm y)).1
    let B := fun i (t : Domain (k i)) =>
      ∑ s : Fin (k i), t s • EuclideanSpace.single (face i s) (1 : ℝ)
    let W := fun l i => coordinatePermACLRepresentative (p i) (a i) (b i) (w l) (Dw l)
    let line := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let Ω := fun i => {y : Domain (n + 1) |
      β i y ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let L := fun (l : Fin 2) (i : I) (y : Domain (n + 1)) => y ∈ Ω i →
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
    let A := fun j (y : Domain (n + 1)) (t : Domain (d j)) =>
      y + ∑ s : Fin (d j), t s • EuclideanSpace.single (sampleFace j s) (1 : ℝ)
    let G : Domain (n + 1) → Prop := fun y => ∀ (j : J) (U : OpenDomain (d j)),
      (∀ t ∈ U.val, A j y t ∈ ball (0 : Domain (n + 1)) ((n : ℝ) + 2)) →
      MemW12 U (fun t => w 0 (A j y t)) (fun t s => Dw 0 (A j y t) (sampleFace j s)) ∧
      MemW12 U (fun t => w 1 (A j y t)) (fun t s => Dw 1 (A j y t) (sampleFace j s))
    let grid := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _j : Fin (n + 1) => ε) (fun _j => hε.ne'.isUnit)
    let C := fun j => ⋂ s : Fin (d j), (EuclideanSpace.proj s) ⁻¹' Ico (0 : ℝ) ε
    ∃ offset : Fin (n + 1) → ℝ,
      (∀ s, offset s ∈ Ico (0 : ℝ) ε) ∧
      (
    ∀ z : Submodule.span ℤ (Set.range grid),
    let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
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
    ∀ normal₀ : Fin (n + 1),
    let p₀ := Equiv.swap (Fin.last n) normal₀
    let j := p₀ (Fin.natAdd n (0 : Fin 1))
    let v := EuclideanSpace.single j (1 : ℝ)
    ∀ z : Submodule.span ℤ (Set.range grid),
    let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
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
        G (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) ∧
      (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) (i : I),
        L l i (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset))) ∧
      (∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2),
        WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset) ∈ ball (0 : Domain (n + 1)) ((n : ℝ) + 2) →
          w l (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) ∈ N) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range grid)),
        ∀ᵐ t ∂volume.restrict (C j),
          (∀ (l : Fin 2) (i : I), L l i (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ∧
          ∀ l : Fin 2,
            A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t ∈ ball (0 : Domain (n + 1)) ((n : ℝ) + 2) →
              w l (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t) ∈ N) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          E (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
                ((∫ x in ball (0 : Domain (n + 1)) ((n : ℝ) + 2), hsNormSq (Dw 0 x)) +
                 (∫ x in ball (0 : Domain (n + 1)) ((n : ℝ) + 2), hsNormSq (Dw 1 x)))) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
          D (A j (WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ (n + 1)))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal (∫ x in ball (0 : Domain (n + 1)) ((n : ℝ) + 2), ‖w 0 x - w 1 x‖ ^ 2)) ∧
      ∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2) (i : I),
        let y := WithLp.toLp 2 ((z : Fin (n + 1) → ℝ) + offset)
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
                  hslice.toLp (fun s => w l (y + B i s + r • v i))) → K = H := by
  classical
  intro I J k p face S a b d sampleFace E D Q e normal v β B W line Ω L A G grid C
  obtain ⟨offset, hoffset, hWeak, hACL, hVertex, hFiber, hEnergy, hDiscrepancy, hTrace⟩ :=
    exists_original_ball_all_rank_qualified_grid w Dw hSob hN hTarget hε
  refine ⟨offset, hoffset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_reducible exact original_selected_vertex_chord_base w hε offset hVertex
  · intro normal₀ p₀ j v₀ z y hCell e₁ B₁ C₁ edge V DV D₁ E₁ face₁
    let emptyBase : Fin 0 ↪ Fin (n + 1) := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
    let index : I := ⟨⟨0, Nat.zero_lt_succ n⟩, ⟨(emptyBase, normal₀), by intro i; exact Fin.elim0 i⟩⟩
    refine ⟨?_, ?_⟩
    · with_reducible exact (original_selected_coordinate_edge_base w Dw hN.isClosed hε offset normal₀
        (fun z l => hACL z l index) z hCell)
    · with_reducible exact (original_selected_coordinate_edge_norm w Dw hε offset normal₀
        (fun z l => hACL z l index) z hCell)

  · with_reducible exact hWeak
  · with_reducible exact hACL
  · with_reducible exact hVertex
  · with_reducible exact hFiber
  · with_reducible exact hEnergy
  · with_reducible exact hDiscrepancy
  · with_reducible exact hTrace

end StratificationTheory
