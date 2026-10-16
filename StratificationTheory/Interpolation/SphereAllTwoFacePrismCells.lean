module

public import StratificationTheory.Interpolation.OriginalAllTwoFacePrismCells
public import StratificationTheory.Foundation.JointRadialPairData

/-!
# Original sphere pair and all selected coordinate two-face prism cells

The same radial ball extension retains the original sphere rays, gradient,
energy and discrepancy. One offset then supplies all coordinate-pair prism
cells and both native one/two-face channels with the original sphere A,D.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Original native sphere data give the same actual ball maps and one
joint lattice of all original coordinate two-face prism connectors. -/
theorem exists_sphere_pair_all_two_face_prism_cells {n q : ℕ} (hn : 1 ≤ n)
    (u : Fin 2 → sphere (0 : Domain (n + 2)) 1 → Ambient q)
    (hu : ∀ l, MemSphereW12 (by omega : 2 ≤ n + 2) (u l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hSphereTarget : ∀ l, ∀ᵐ θ ∂(Measure.euclideanHausdorffMeasure (n + 1) :
      Measure (sphere (0 : Domain (n + 2)) 1)), u l θ ∈ N)
    {ε : ℝ} (hε : 0 < ε) :
    let R : ℝ := (n : ℝ) + 3
    let A_S : ℝ :=
      (∫ θ : sphere (0 : Domain (n + 2)) 1,
        hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ n + 2) (u 0) (hu 0) i) θ)
          ∂Measure.euclideanHausdorffMeasure (n + 1)) +
      (∫ θ : sphere (0 : Domain (n + 2)) 1,
        hsNormSq (fun i => (sphereGradient (by omega : 2 ≤ n + 2) (u 1) (hu 1) i) θ)
          ∂Measure.euclideanHausdorffMeasure (n + 1))
    let D_S : ℝ := ∫ θ : sphere (0 : Domain (n + 2)) 1, ‖u 0 θ - u 1 θ‖ ^ 2
      ∂Measure.euclideanHausdorffMeasure (n + 1)
    ∃ (w : Fin 2 → Domain (n + 2) → Ambient q)
      (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q),
      (∀ l, MemW12 (ballDomain 0 R) (w l) (Dw l)) ∧
      (∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) R), w l x ∈ N) ∧
      (∀ (l : Fin 2) (ρ : PositiveRadius) (θ : sphere (0 : Domain (n + 2)) 1),
        w l (ρ.val • θ.val) = u l θ) ∧
      (∀ (l : Fin 2) (ρ : PositiveRadius) (i : Fin (n + 2)),
        (fun θ : sphere (0 : Domain (n + 2)) 1 => ρ.val • Dw l (ρ.val • θ.val) i) =ᵐ[
          Measure.euclideanHausdorffMeasure (n + 1)]
            (fun θ => (sphereGradient (by omega : 2 ≤ n + 2) (u l) (hu l) i) θ)) ∧
      ((∫ x in ball (0 : Domain (n + 2)) R, hsNormSq (Dw 0 x)) +
        (∫ x in ball (0 : Domain (n + 2)) R, hsNormSq (Dw 1 x))) = (R ^ n / n) * A_S ∧
      (∫ x in ball (0 : Domain (n + 2)) R, ‖w 0 x - w 1 x‖ ^ 2) =
        (R ^ (n + 2) / (n + 2)) * D_S ∧
    let J := (Fin 2 ↪ Fin (n + 2)) ⊕ Fin (n + 2)
    let d : J → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)
    let sampleFace : (j : J) → (Fin (d j) ↪ Fin (n + 2)) :=
      Sum.rec (motive := fun j : J => Fin (d j) ↪ Fin (n + 2)) (fun c => c)
        (fun i => (⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin (n + 2)))
    let C := fun j : J => ⋂ k : Fin (d j), (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) R).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 2)) R).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Asample := fun (j : J) (y : Domain (n + 2)) (t : Domain (d j)) =>
      y + ∑ k : Fin (d j), t k • EuclideanSpace.single (sampleFace j k) (1 : ℝ)
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    ∃ offset : Fin (n + 2) → ℝ,
      (∀ j, offset j ∈ Ico (0 : ℝ) ε) ∧
      (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
        Eraw (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t)) ≤
          2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
            ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
              ((R ^ n / n) * A_S)) ∧
      (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
        Draw (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t)) ≤
          2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
            ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
              ((R ^ (n + 2) / (n + 2)) * D_S)) ∧
      ∀ coord : Fin 2 ↪ Fin (n + 2),
      let vec := fun i : Fin 2 => EuclideanSpace.single (coord i) (1 : ℝ)
      let p := fun i : Fin 2 => Equiv.swap (Fin.last (n + 1)) (coord i)
      let other₀ := fun i : Fin 2 => (Equiv.swap (0 : Fin 2) 1) i
      let rep := fun (l : Fin 2) (i : Fin 2) => coordinatePermACLRepresentative (p i) (-1) 1 (w l) (Dw l)
      let embed := fun (y : Domain (n + 2)) (t : Domain 2) => y + t 0 • vec 0 + t 1 • vec 1
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
  intro R A_S D_S
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨w, Dw, hW, hRaw, hGradient, hEnergy, hDiscrepancy, hValues⟩ :=
    exists_joint_radial_pair_ball_data (n := n + 2) (q := q) (by omega) u hu hR
  have hTarget (l : Fin 2) : ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) R), w l x ∈ N :=
    hValues l (fun x => x ∈ N) (hSphereTarget l)
  have hEnergy' : ((∫ x in ball (0 : Domain (n + 2)) R, hsNormSq (Dw 0 x)) +
      (∫ x in ball (0 : Domain (n + 2)) R, hsNormSq (Dw 1 x))) = (R ^ n / n) * A_S := by
    simpa only [Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega,
      Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right] using hEnergy
  have hDiscrepancy' : (∫ x in ball (0 : Domain (n + 2)) R, ‖w 0 x - w 1 x‖ ^ 2) =
      (R ^ (n + 2) / (n + 2)) * D_S := by
    simpa only [show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_ofNat] using hDiscrepancy
  refine ⟨w, Dw, hW, hTarget, hRaw, hGradient, hEnergy', hDiscrepancy', ?_⟩
  have hGrid := exists_original_ball_all_two_face_prism_cells (n := n) (q := q)
    w Dw hW hN hTarget hε
  have hEnergy₀ : ((∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x))) =
      (((n : ℝ) + 3) ^ n / n) * A_S := hEnergy'
  have hDiscrepancy₀ : (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2) =
      (((n : ℝ) + 3) ^ (n + 2) / (n + 2)) * D_S := hDiscrepancy'
  intro J d sampleFace C Eraw Draw Asample grid
  obtain ⟨offset, hoffset, hE, hD, hCells⟩ := hGrid
  refine ⟨offset, hoffset, ?_, ?_, ?_⟩
  · intro j
    have h := hE j
    rw [hEnergy₀] at h
    simpa only [J, d, sampleFace, C, Eraw, Asample, grid, R] using h
  · intro j
    have h := hD j
    rw [hDiscrepancy₀] at h
    simpa only [J, d, sampleFace, C, Draw, Asample, grid, R] using h
  · intro coord vec p other₀ rep embed z y u₂ Du₂ F b e δ index other edgePoint f g P S₀ B S Ω A T U DU V DV E Dedge Aedge Qface face hCell
    have hOne := hCells coord z hCell
    obtain ⟨G, D, hCap, hWcell, hEnergyCell, hDistanceCell, K, hK, hKEnd⟩ := hOne
    refine ⟨G, D, ?_, hWcell, hEnergyCell, hDistanceCell, K, ?_, ?_⟩
    · intro j x hx
      with_reducible exact hCap j x hx
    · intro i
      exact hK i
    · intro i positive
      filter_upwards [hKEnd i positive] with x hx
      with_reducible exact hx

end StratificationTheory
