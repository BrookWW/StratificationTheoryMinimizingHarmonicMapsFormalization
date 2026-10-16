module

public import StratificationTheory.Foundation.OriginalClosedTargetFaceGridJoint
public import StratificationTheory.Foundation.GridCubeBallContainment

public section

open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators

namespace StratificationTheory

/-- One original selected offset retains every native coordinate rank,
all original line qualifications including the zero-dimensional bases,
raw vertex values, and complete raw face-prism curves. -/
theorem exists_original_ball_all_rank_qualified_grid {n q : ℕ}
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
  have hface (i : I) (l : Fin (k i)) : face i l ≠ p i (Fin.natAdd n (0 : Fin 1)) := by
    change i.2.val.1 l ≠ (Equiv.swap (Fin.last n) i.2.val.2) (Fin.last n)
    rw [Equiv.swap_apply_left]
    exact i.2.property l
  have hS (i : I) : MeasurableSet (S i) := MeasurableSet.iInter fun j : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj j).continuous.measurable
  have hab (i : I) : a i < b i := by norm_num [a, b]
  have hrect (i : I) (x : Domain n) (hx : x ∈ S i) (t : ℝ) (ht : t ∈ Ioo (a i) (b i)) :
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) ∈
          ball (0 : Domain (n + 1)) ((n : ℝ) + 2) := by
    exact unit_coordinate_line_rectangle_mem_ball (p i) x (fun j => mem_iInter.mp hx j) ht
  obtain ⟨offset, hoffset, hWeak, hACL, hVertex, hFiber, hEnergy, hDiscrepancy, hTrace⟩ :=
    exists_grid_translate_original_closed_target_face_joint
    (ι := I) (J := J) (by positivity : 0 < (n : ℝ) + 2) w Dw hSob hN hTarget
      k p face hface S hS a b hab hrect d sampleFace hε
  dsimp only at hACL hFiber
  dsimp only [L, W]
  generalize hRep : (@coordinatePermACLRepresentative n q) = Rep at hACL hFiber ⊢
  refine ⟨offset, hoffset, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hWeak
  · exact hACL
  · exact hVertex
  · exact hFiber
  · exact hEnergy
  · exact hDiscrepancy
  · exact hTrace

end StratificationTheory
