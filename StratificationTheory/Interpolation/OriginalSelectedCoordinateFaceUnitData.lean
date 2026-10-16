module

public import StratificationTheory.Interpolation.OriginalCoordinateFaceUnitData
public import StratificationTheory.Foundation.GridCubeBallContainment
public import StratificationTheory.Foundation.TwoCoordinateSquareGeometry

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

private theorem coordinate_positive_cell_axis_mem {d : ℕ} {ε : ℝ}
    (i : Fin (d + 1)) (x : Domain d) (r : ℝ)
    (hx : ∀ k, x k ∈ Icc (0 : ℝ) ε) (hr : r ∈ Icc (0 : ℝ) ε) :
    ∀ k : Fin (d + 1),
      (cubicalSignedFaceIsometry d i true
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) r))) k ∈ Icc (0 : ℝ) ε := by
  intro k
  let σ := Equiv.swap (Fin.last d) i
  obtain ⟨j, rfl⟩ := σ.surjective k
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [cubicalSignedFaceIsometry_apply]
    simp only [ite_true]
    change ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1))
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) r))).2 0 ∈ Icc (0 : ℝ) ε
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hr
  · rw [cubicalSignedFaceIsometry_apply]
    simp only [Fin.castSucc_ne_last, ite_false]
    change ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1))
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) r))).1 j ∈ Icc (0 : ℝ) ε
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hx j

/-- Original weak, native-target and higher raw-trace events at the same
fixed source point produce the same unit coordinate-face pair and all its
original signed-face classes. No new lattice offset is chosen. -/
theorem original_selected_coordinate_face_unit_data {d n q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (coord : Fin (d + 1) ↪ Fin (n + 2)) (y : Domain (n + 2)) {N : Set (Ambient q)} :
    let P : OpenDomain (d + 1) := ⟨⋂ j : Fin (d + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
      isOpen_iInter_of_finite fun j : Fin (d + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let B : OpenDomain (d + 1) := ⟨⋂ j : Fin (d + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite fun j : Fin (d + 1) => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
    let C := ⋂ j : Fin d, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d) (m := 1)
    let source := fun z : Domain (d + 1) => y + ∑ j : Fin (d + 1), z j • EuclideanSpace.single (coord j) (1 : ℝ)
    let u := fun l => w l ∘ source
    let Du := fun l z j => Dw l (source z) (coord j)
    let T := fun z : Domain (d + 1) => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let U := fun l => u l ∘ T
    let DU := fun l z j => (ε / 2) • Du l (T z) j
    (∀ (Ω : OpenDomain (d + 1)),
      (∀ t ∈ Ω.val, source t ∈ ball (0 : Domain (n + 2)) ((n : ℝ) + 3)) →
      MemW12 Ω (u 0) (Du 0) ∧ MemW12 Ω (u 1) (Du 1)) →
    (∀ᵐ t ∂volume.restrict (⋂ j : Fin (d + 1), (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε),
      ∀ l : Fin 2, source t ∈ ball (0 : Domain (n + 2)) ((n : ℝ) + 3) → u l t ∈ N) →
    (∀ (base : Fin d ↪ Fin (n + 2))
          (normal : Fin (n + 2)) (hbaseNormal : ∀ s, base s ≠ normal),
        let p := Equiv.swap (Fin.last (n + 1)) normal
        let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
        let β := fun x : Domain (n + 2) => (e (Q.symm x)).1
        let v := EuclideanSpace.single normal (1 : ℝ)
        let B := fun t : Domain d => ∑ s, t s • EuclideanSpace.single (base s) (1 : ℝ)
        ∀ l : Fin 2,
        y normal ∈ Ioo (-1 : ℝ) 1 → y normal + ε ∈ Ioo (-1 : ℝ) 1 →
        ∀ U : OpenDomain d, (volume : Measure (Domain d)) U.val ≠ ⊤ →
        (∀ s ∈ U.val, ∀ j : Fin (n + 1), (β (y + B s)) j ∈ Ioo (-1 : ℝ) 1) →
        ∃ H : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U.val)),
          (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
            ∃ hs : MemLp (fun s => w l (y + B s + r • v)) 2 (volume.restrict U.val),
              H ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun s => w l (y + B s + r • v))) ∧
          (∃ hs : MemLp (fun s => w l (y + B s)) 2 (volume.restrict U.val),
            H ⟨0, le_rfl, hε.le⟩ = hs.toLp (fun s => w l (y + B s))) ∧
          (∃ hs : MemLp (fun s => w l (y + ε • v + B s)) 2 (volume.restrict U.val),
            H ⟨ε, hε.le, le_rfl⟩ = hs.toLp (fun s => w l (y + ε • v + B s))) ∧
          ∀ K : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U.val)),
            (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
              ∃ hs : MemLp (fun s => w l (y + B s + r • v)) 2 (volume.restrict U.val),
                K ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun s => w l (y + B s + r • v))) → K = H) →
    (∀ t : Domain (d + 1), (∀ j, t j ∈ Icc (0 : ℝ) ε) →
      ∀ j : Fin (n + 2), (source t) j ∈ Ioo (-1 : ℝ) 1) →
    (∀ l, MemW12 B (U l) (DU l)) ∧
    (∀ l, (∫ z in B.val, hsNormSq (DU l z)) =
      (ε / 2) ^ ((2 : ℤ) - (d + 1 : ℕ)) * ∫ z in P.val, hsNormSq (Du l z)) ∧
    (∀ l, ∀ᵐ z ∂volume.restrict B.val, U l z ∈ N) ∧
    ∃ Kh : Fin 2 → Fin (d + 1) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry d i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict C),
          Kh l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U l
            (cubicalSignedFaceIsometry d i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      ∀ l i (positive : Bool),
        ∃ hs : MemLp (fun x => U l (cubicalSignedFaceIsometry d i positive
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) 2 (volume.restrict C),
          Kh l i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
            by cases positive <;> norm_num⟩ = hs.toLp (fun x => U l
              (cubicalSignedFaceIsometry d i positive (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) := by
  intro P B C e source u Du T U DU hWeak hTargetFaces hHigherTrace hCell
  let pair := fun i : Fin (d + 1) =>
    (Fin.castSuccEmb.trans (Equiv.swap (Fin.last d) i).toEmbedding).trans coord
  let S : Set (Domain d) := ⋂ j : Fin d, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
  let P₂ : OpenDomain d := ⟨S, isOpen_iInter_of_finite fun j : Fin d =>
    isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous⟩
  have hP₂finite : (volume : Measure (Domain d)) P₂.val ≠ ⊤ := by
    rw [volume_native_positive_cube d hε]
    exact ENNReal.ofReal_ne_top
  have hBall (t : Domain (d + 1)) (ht : t ∈ P.val) : source t ∈
      ball (0 : Domain (n + 2)) ((n : ℝ) + 3) := by
    have hUnit := hCell t (fun j => ⟨(mem_iInter.mp ht j).1.le, (mem_iInter.mp ht j).2.le⟩)
    rw [mem_ball_zero_iff]
    have hNorm := euclidean_norm_le_dim_of_coordinate_bound (source t)
      (fun j => abs_le.mpr ⟨(hUnit j).1.le, (hUnit j).2.le⟩)
    push_cast at hNorm
    linarith only [hNorm]
  have hSobRaw (l : Fin 2) : MemW12 P (u l) (Du l) := by
    have h := hWeak P hBall
    fin_cases l
    · exact h.1
    · exact h.2
  have hTargetRaw (l : Fin 2) : ∀ᵐ t ∂volume.restrict P.val, u l t ∈ N := by
    have hSub : P.val ⊆ ⋂ j : Fin (d + 1), (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε := by
      intro t ht
      exact mem_iInter.mpr fun j => ⟨(mem_iInter.mp ht j).1.le, (mem_iInter.mp ht j).2⟩
    have h := hTargetFaces.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
    filter_upwards [h, ae_restrict_mem P.property.measurableSet] with t ht htP
    exact ht l (hBall t htP)
  have hOrigin : ∀ j, y j ∈ Ioo (-1 : ℝ) 1 := by
    have h := hCell 0 (by intro j; simp [hε.le])
    simpa only [source, PiLp.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] using h
  have hPair (i : Fin (d + 1)) (s : Fin d) : pair i s ≠ coord i := by
    intro h
    have hi := coord.injective h
    have heq : (Equiv.swap (Fin.last d) i) s.castSucc = (Equiv.swap (Fin.last d) i) (Fin.last d) := by
      simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Fin.castSuccEmb_apply, Equiv.swap_apply_left] using hi
    exact (Fin.castSucc_ne_last s) ((Equiv.swap (Fin.last d) i).injective heq)
  have hAxis (i : Fin (d + 1)) (x : Domain d) (r : ℝ) :
      source (cubicalSignedFaceIsometry d i true (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))) =
        y + ∑ j : Fin d, x j • EuclideanSpace.single (pair i j) (1 : ℝ) +
          r • EuclideanSpace.single (coord i) (1 : ℝ) :=
    coordinate_cell_native_normal_slice coord y i x r
  have hPointUnit (i : Fin (d + 1)) (x : Domain d) (hx : ∀ j, x j ∈ Icc (0 : ℝ) ε)
      (r : ℝ) (hr : r ∈ Icc (0 : ℝ) ε) : ∀ j,
      (y + ∑ j : Fin d, x j • EuclideanSpace.single (pair i j) (1 : ℝ) +
        r • EuclideanSpace.single (coord i) (1 : ℝ)) j ∈ Ioo (-1 : ℝ) 1 := by
    rw [← hAxis]
    exact hCell _ (coordinate_positive_cell_axis_mem i x r hx hr)
  have hNormalUpper (i : Fin (d + 1)) : y (coord i) + ε ∈ Ioo (-1 : ℝ) 1 := by
    have h := hPointUnit i 0 (by intro j; simp [hε.le]) ε ⟨hε.le, le_rfl⟩ (coord i)
    simpa only [PiLp.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
      PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one] using h
  have hCurves (l : Fin 2) (i : Fin (d + 1)) := hHigherTrace (pair i) (coord i) (hPair i) l
    (hOrigin _) (hNormalUpper i) P₂ hP₂finite (by
      intro x hx j
      rw [coordinate_split_first_eq]
      have h := hPointUnit i x (fun k => ⟨(mem_iInter.mp hx k).1.le, (mem_iInter.mp hx k).2.le⟩)
        0 ⟨le_rfl, hε.le⟩
      simpa only [zero_smul, add_zero] using h _)
  choose H hH hLeft hRight _hUnique using hCurves
  have hEnd : ∀ l i (positive : Bool),
      ∃ hs : MemLp (fun x : Domain d => w l
          (y + ∑ j : Fin d, x j • EuclideanSpace.single (pair i j) (1 : ℝ) +
            (if positive then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)))
        2 (volume.restrict S),
        H l i ⟨if positive then ε else 0, by cases positive <;> simp [hε.le],
          by cases positive <;> simp [hε.le]⟩ = hs.toLp _ := by
    intro l i positive
    cases positive
    · simpa only [Bool.false_eq_true, ite_false, zero_smul, add_zero] using hLeft l i
    · obtain ⟨hs, heq⟩ := hRight l i
      have hAE : (fun x : Domain d => w l
          (y + ε • EuclideanSpace.single (coord i) (1 : ℝ) +
            ∑ j : Fin d, x j • EuclideanSpace.single (pair i j) (1 : ℝ))) =ᵐ[volume.restrict S]
          (fun x : Domain d => w l
          (y + ∑ j : Fin d, x j • EuclideanSpace.single (pair i j) (1 : ℝ) +
            ε • EuclideanSpace.single (coord i) (1 : ℝ))) := by
        apply Eventually.of_forall
        intro x
        exact congrArg (w l) (add_right_comm _ _ _)
      have hnew := hs.ae_eq hAE
      exact ⟨hnew, heq.trans (hs.toLp_congr hnew hAE)⟩
  exact original_coordinate_face_unit_data hε w Dw coord y hSobRaw hTargetRaw H hH hEnd

end StratificationTheory
