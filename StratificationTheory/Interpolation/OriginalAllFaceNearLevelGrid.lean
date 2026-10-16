module

public import StratificationTheory.Interpolation.OriginalGridNearLevelEdgeComplex
public import StratificationTheory.Foundation.OriginalClosedTargetFaceGridJoint
public import StratificationTheory.Foundation.CoordinateEdgePrismInputs
public import StratificationTheory.Foundation.TwoVectorSquareTraceTransport
public import StratificationTheory.Foundation.GridCubeBallContainment

/-!
# All original faces and quantitative near-level edges on one lattice

One original ball pair determines a single offset for all native coordinate
faces, the original full-face trace curves, and every contained coordinate
square prism. The scalar channels retain the original paired ball energy
and discrepancy. Every subsequent finite-energy a.e. level event can be
selected jointly with the actual nearby edge channels on this same lattice.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- One original selected lattice supports all original face data and the
actual first prism cells, followed by joint quantitative level selection
for any supplied finite-energy a.e. level event. -/
theorem exists_original_ball_all_face_near_level_grid {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 2)) ((n : ℝ) + 3)) (w l) (Dw l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)), w l x ∈ N)
    {ε a b : ℝ} (hε : 0 < ε) (hab : a < b) :
    let J₀ := (Fin 2 ↪ Fin (n + 2)) ⊕ Fin (n + 2)
    let J₁ := (k : Fin n) × (Fin (k.val + 3) ↪ Fin (n + 2))
    let J := J₀ ⊕ J₁
    let d₀ : J₀ → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)
    let d : J → ℕ := Sum.elim d₀ (fun c => c.1.val + 3)
    let sampleFace₀ : (j : J₀) → (Fin (d₀ j) ↪ Fin (n + 2)) :=
      Sum.rec (motive := fun j : J₀ => Fin (d₀ j) ↪ Fin (n + 2)) (fun c => c)
        (fun i => (⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin (n + 2)))
    let sampleFace : (j : J) → (Fin (d j) ↪ Fin (n + 2)) :=
      Sum.rec (motive := fun j : J => Fin (d j) ↪ Fin (n + 2)) sampleFace₀ (fun c => c.2)
    let C := fun j : J => ⋂ k : Fin (d j), (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let Eraw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
    let Draw := (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)).indicator
      (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
    let Asample := fun (j : J) (y : Domain (n + 2)) (t : Domain (d j)) =>
      y + ∑ k : Fin (d j), t k • EuclideanSpace.single (sampleFace j k) (1 : ℝ)
    let grid := (Pi.basisFun ℝ (Fin (n + 2))).isUnitSMul
      (w := fun _j : Fin (n + 2) => ε) (fun _j => hε.ne'.isUnit)
    let samplingCount : ℕ := Fintype.card J
    let L : Submodule ℤ (Fin (n + 2) → ℝ) := Submodule.span ℤ (Set.range grid)
    let I : Type := Fin (n + 2) × (Fin (n + 1) → Bool)
    let Cline : Set (Domain 1) := ⋂ k : Fin 1, (EuclideanSpace.proj k) ⁻¹' Ico (0 : ℝ) ε
    let A₀ : ℝ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
        ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ : ℝ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    let c : ℝ≥0∞ := 2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ * ((samplingCount : ℝ≥0∞) * ENNReal.ofReal ε)
    let B : ℝ≥0∞ := 6 * ENNReal.ofReal ε * (ENNReal.ofReal (b - a))⁻¹ * (Fintype.card I : ℝ≥0∞) * c
    let vertex := fun i : I =>
      (WithLp.toLp 2 (fun j : Fin (n + 1) => if i.2 j then ε else 0) : Domain (n + 1))
    let edgeSplit := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    ∃ offset : Fin (n + 2) → ℝ,
      (∀ j, offset j ∈ Ico (0 : ℝ) ε) ∧
      (    let y : L → Domain (n + 2) := fun z : L => WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
    let Eline : Fin (n + 2) → L → ℝ≥0∞ := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in Cline, Eraw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let Dline : Fin (n + 2) → L → ℝ≥0∞ := fun (k : Fin (n + 2)) (z : L) =>
      ∫⁻ t in Cline, Draw (y z + t 0 • EuclideanSpace.single k (1 : ℝ))
    let er : I → L → ℝ := fun (i : I) (z : L) => ∫ s in Ioo (0 : ℝ) ε,
      ‖Dw 0 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) i.1‖ ^ 2 +
        ‖Dw 1 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) i.1‖ ^ 2
    let dr : I → L → ℝ := fun (i : I) (z : L) => ∫ s in Ioo (0 : ℝ) ε,
      ‖w 0 (y z + s • EuclideanSpace.single i.1 (1 : ℝ)) -
        w 1 (y z + s • EuclideanSpace.single i.1 (1 : ℝ))‖ ^ 2
    ∀ energy : ℝ → ℝ≥0∞,
    AEMeasurable energy (volume.restrict (Ioo a b)) →
    (∫⁻ r in Ioo a b, energy r) ≠ ⊤ →
    ∀ P : ℝ → Prop, (∀ᵐ r ∂volume.restrict (Ioo a b), P r) →
    ∃ (shift : I → L) (r : ℝ),
      r ∈ Ioo a b ∧ P r ∧
      energy r ≤ 3 * (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ s in Ioo a b, energy s ∧
      (∀ (i : I) (z : L) (s : ℝ),
        y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ) =
          y z + cubicalSignedFaceIsometry (n + 1) i.1 true
            (edgeSplit.symm (vertex i, EuclideanSpace.single (0 : Fin 1) s))) ∧
      (∀ (i : I) (z : L) (s : ℝ), s ∈ Icc (0 : ℝ) ε → ∀ j,
        (y (z + shift i) + s • EuclideanSpace.single i.1 (1 : ℝ)) j - (y z) j ∈ Icc (0 : ℝ) ε) ∧
      ∀ z : L,
        (∀ x : Domain (n + 2), (∀ j, x j - (y z) j ∈ Icc (0 : ℝ) ε) →
          x ∈ ball (0 : Domain (n + 2)) ((n : ℝ) + 3)) →
        (∃ x : Domain (n + 2), (∀ j, x j - (y z) j ∈ Icc (0 : ℝ) ε) ∧ ‖WithLp.ofLp x‖ = r) →
        (∑ i : I, (dr i (z + shift i) / ε + Real.sqrt (2 * dr i (z + shift i) * er i (z + shift i)))) ≤
          (Fintype.card I : ℝ) * B.toReal * (D₀ / ε + Real.sqrt (2 * D₀ * A₀))) ∧
      (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
        Eraw (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t)) ≤
          2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
            ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
              ((∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
                ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x))) ∧
      (∀ j : J, (∑' z : Submodule.span ℤ (Set.range grid), ∫⁻ t in C j,
        Draw (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t)) ≤
          2 * (ENNReal.ofReal (ε ^ (n + 2)))⁻¹ *
            ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ENNReal.ofReal
              (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2)) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range grid)) (U : OpenDomain (d j)),
        (∀ t ∈ U.val, Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t ∈
          ball (0 : Domain (n + 2)) ((n : ℝ) + 3)) →
        MemW12 U (fun t => w 0 (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t))
          (fun t s => Dw 0 (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t) (sampleFace j s)) ∧
        MemW12 U (fun t => w 1 (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t))
          (fun t s => Dw 1 (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t) (sampleFace j s))) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range grid)),
        ∀ᵐ t ∂volume.restrict (C j), ∀ l : Fin 2,
          Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t ∈
            ball (0 : Domain (n + 2)) ((n : ℝ) + 3) →
          w l (Asample j (WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)) t) ∈ N) ∧
      (∀ (k : Fin n) (base : Fin (k.val + 2) ↪ Fin (n + 2))
          (normal : Fin (n + 2)) (hbaseNormal : ∀ s, base s ≠ normal),
        let p := Equiv.swap (Fin.last (n + 1)) normal
        let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
        let β := fun x : Domain (n + 2) => (e (Q.symm x)).1
        let v := EuclideanSpace.single normal (1 : ℝ)
        let B := fun t : Domain (k.val + 2) => ∑ s, t s • EuclideanSpace.single (base s) (1 : ℝ)
        ∀ (z : Submodule.span ℤ (Set.range grid)) (l : Fin 2),
        let y := WithLp.toLp 2 ((z : Fin (n + 2) → ℝ) + offset)
        y normal ∈ Ioo (-1 : ℝ) 1 → y normal + ε ∈ Ioo (-1 : ℝ) 1 →
        ∀ U : OpenDomain (k.val + 2), (volume : Measure (Domain (k.val + 2))) U.val ≠ ⊤ →
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
                K ⟨r, hr.1.le, hr.2.le⟩ = hs.toLp (fun s => w l (y + B s + r • v))) → K = H) ∧
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
  intro J₀ J₁ J d₀ d sampleFace₀ sampleFace C Eraw Draw Asample grid samplingCount L I Cline A₀ D₀ c B vertex edgeSplit
  obtain ⟨offset, hoffset, hEnergy, hD, hWeak, hRawTarget, hHigherH, hPrisms⟩ :=
    exists_original_ball_all_face_prism_grid w Dw hSob hN hTarget hε
  refine ⟨offset, hoffset, ?_, hEnergy, hD, hWeak, hRawTarget, hHigherH, ?_⟩
  · intro y Eline Dline er dr energy hEnergyMeas hEnergyFinite P hP
    have hE1 (k : Fin (n + 2)) : (∑' z : L, Eline k z) ≤ c * ENNReal.ofReal A₀ := by
      have h := hEnergy (Sum.inl (Sum.inr k))
      dsimp only [d, d₀, Sum.elim, sampleFace, sampleFace₀, Asample, C] at h
      simp only [pow_one] at h
      change (∑' z : L, ∫⁻ t in Cline,
        Eraw (y z + ∑ s : Fin 1, t s • EuclideanSpace.single k (1 : ℝ))) ≤ c * ENNReal.ofReal A₀ at h
      simpa only [Fin.sum_univ_one] using h
    have hD1 (k : Fin (n + 2)) : (∑' z : L, Dline k z) ≤ c * ENNReal.ofReal D₀ := by
      have h := hD (Sum.inl (Sum.inr k))
      dsimp only [d, d₀, Sum.elim, sampleFace, sampleFace₀, Asample, C] at h
      simp only [pow_one] at h
      change (∑' z : L, ∫⁻ t in Cline,
        Draw (y z + ∑ s : Fin 1, t s • EuclideanSpace.single k (1 : ℝ))) ≤ c * ENNReal.ofReal D₀ at h
      simpa only [Fin.sum_univ_one] using h
    exact original_selected_grid_joint_near_level_edge_complex w Dw hε hab
      (Fintype.card J) offset hE1 hD1 energy hEnergyMeas hEnergyFinite P hP
  · with_reducible exact hPrisms

end StratificationTheory
