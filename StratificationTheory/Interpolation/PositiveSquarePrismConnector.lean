module

public import StratificationTheory.Interpolation.CubicalSixFaceAssembler
public import StratificationTheory.Interpolation.CubicalEdgeUnitConnector
public import StratificationTheory.Foundation.UnitSquareCoordinateTraces
public import StratificationTheory.Foundation.IntervalSobolevTranslation
public import StratificationTheory.Foundation.RawPairPrismEdges

/-!
# A three-dimensional connector from the original qualified square data

The two original square maps and their four original closed edge pairs
produce all six actual boundary faces. The common raw affine edge map
identifies all twelve lower edges before the radial cube filling is used.
The same filling retains the resulting energy and target-distance bounds.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

private theorem positive_prism_cap_coordinates (x : Domain 1) (t : ℝ) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
      (x, EuclideanSpace.single (0 : Fin 1) t) = WithLp.toLp 2 ![x 0, t] := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  apply e.injective
  rw [e.apply_symm_apply]
  apply Prod.ext <;> ext j <;> fin_cases j <;> rfl

private theorem norm_affine_pair_le {q : ℕ} {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    {F G : Ambient q} {M : ℝ} (hF : ‖F‖ ≤ M) (hG : ‖G‖ ≤ M) :
    ‖(1 - a) • F + a • G‖ ≤ M := by
  calc
    ‖(1 - a) • F + a • G‖ ≤ ‖(1 - a) • F‖ + ‖a • G‖ := norm_add_le _ _
    _ = (1 - a) * ‖F‖ + a * ‖G‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ha₁), abs_of_nonneg ha₀]
    _ ≤ (1 - a) * M + a * M := add_le_add
      (mul_le_mul_of_nonneg_left hF (sub_nonneg.mpr ha₁)) (mul_le_mul_of_nonneg_left hG ha₀)
    _ = M := by ring

private theorem positive_prism_signed_cap_coordinates (i : Fin 2) (positive : Bool)
    (x : Domain 1) :
    cubicalSignedFaceIsometry 1 i positive
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
        (x, EuclideanSpace.single (0 : Fin 1) 1)) =
      if i = 0 then WithLp.toLp 2 ![if positive then (1 : ℝ) else -1, x 0]
      else WithLp.toLp 2 ![x 0, if positive then (1 : ℝ) else -1] := by
  rw [positive_prism_cap_coordinates]
  ext j
  fin_cases i <;> fin_cases j <;> cases positive <;>
    simp [cubicalSignedFaceIsometry_coordinate, Fin.last]

/-- Original finite square/edge data yield an actual first prism filling.
The four vertical face graphs and all twelve shared edge identities are
proved internally, rather than assumed as three-dimensional boundary data. -/
theorem exists_positive_square_pair_prism_connector {q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (u : Fin 2 → Domain 2 → Ambient q) (Du : Fin 2 → Domain 2 → Gradient 2 q)
    (F : Fin 2 → Bool → Fin 2 → ℝ → Ambient q)
    {N : Set (Ambient q)} (hN : IsCompact N) :
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
    let S₀ := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
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
    (∀ l, MemW12 P (u l) (Du l)) →
    (∀ l, ∀ᵐ z ∂volume.restrict P.val, u l z ∈ N) →
    (∀ i side l, MemLp (f i side l) 2 (volume.restrict (Ioo (0 : ℝ) ε))) →
    (∀ i side l, MemLp (g i side l) 2 (volume.restrict (Ioo (0 : ℝ) ε))) →
    (∀ i side l, (F i side l) =ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] f i side l) →
    (∀ i side l s, s ∈ Icc (0 : ℝ) ε → ∀ t, t ∈ Icc (0 : ℝ) ε →
      F i side l t - F i side l s = ∫ r in s..t, g i side l r) →
    (∀ i side l s, s ∈ Icc (0 : ℝ) ε → F i side l s ∈ N) →
    (∀ i side l positive, F i side l (δ positive) = f i side l (δ positive)) →
    ∀ H : Fin 2 → Fin 2 → C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S₀)),
    (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
      ∃ hs : MemLp (fun x => u l (cubicalSignedFaceIsometry 1 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S₀),
        H l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => u l (cubicalSignedFaceIsometry 1 i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ l i positive,
      ∃ hs : MemLp (fun x : Domain 1 => f i positive l (x 0)) 2 (volume.restrict S₀),
        H l i ⟨δ positive, by cases positive <;> simp [δ, hε.le],
          by cases positive <;> simp [δ, hε.le]⟩ = hs.toLp (fun x : Domain 1 => f i positive l (x 0))) →
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
  intro b e δ index other edgePoint f g P S₀ B S Ω A T U DU V DV E Dedge Aedge Qface face
    hSob hTarget hf hg hAE hInc hLineTarget hLineEnds H hH hHEnd
  have hNorm (side : Bool) := memW12_unit_cube_normalization_energy (n := 2) (q := q)
    hε (hSob (index side))
  have hU (side : Bool) : MemW12 B (U side) (DU side) := (hNorm side).1
  have hUTarget (side : Bool) : ∀ᵐ z ∂volume.restrict B.val, U side z ∈ N :=
    (hNorm side).2.2.2 (fun z => z ∈ N) (hTarget (index side))
  have hLineAC (i : Fin 2) (side : Bool) (l : Fin 2) :
      AbsolutelyContinuousOnInterval (F i side l) 0 ε :=
    absolutelyContinuousOnInterval_of_integral_increments hε.le (hg i side l) (hInc i side l)
  have hfN (i : Fin 2) (side : Bool) (l : Fin 2) :
      ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ε), f i side l s ∈ N := by
    filter_upwards [hAE i side l, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    rw [← hs]
    exact hLineTarget i side l s ⟨hsI.1.le, hsI.2.le⟩
  have hVert (i : Fin 2) (side : Bool) := exists_unit_affine_edge_connector
    (F := F i side 0) (G := F i side 1)
    (f := f i side 0) (h := f i side 1) (g := g i side 0) (k := g i side 1)
    hε (hf i side 0) (hf i side 1) (hg i side 0) (hg i side 1)
    (hLineAC i side 0) (hLineAC i side 1) (hAE i side 0) (hAE i side 1)
    (hInc i side 0) (hInc i side 1) hN.isClosed (hfN i side 0) (hfN i side 1)
  choose HT HS hHT hHT₀ hHT₁ hHS hHS₀ hHS₁ using fun i side => (hVert i side).2.2.2
  have hV (i : Fin 2) (side : Bool) : MemW12 B (V i side) (DV i side) := (hVert i side).1
  have hsingle (x : Domain 1) : EuclideanSpace.single (0 : Fin 1) (x 0) = x := by
    ext j
    fin_cases j
    simp
  have hKH (side : Bool) := exists_unit_square_coordinate_traces hε (u (index side))
    (H (index side)) (hH (index side)) (by
      intro i positive
      simpa only [f, edgePoint, δ, hsingle] using hHEnd (index side) i positive)
  choose KH hKHraw hKHend using hKH
  obtain ⟨M, hM⟩ := hN.isBounded.exists_norm_le
  have hBU (side : Bool) : ∀ᵐ z ∂volume.restrict B.val, ‖U side z‖ ≤ M :=
    (hUTarget side).mono fun _ hz => hM _ hz
  have hBV (i : Fin 2) (side : Bool) : ∀ᵐ z ∂volume.restrict B.val, ‖V i side z‖ ≤ M := by
    filter_upwards [ae_restrict_mem B.property.measurableSet] with z hz
    have hc (j : Fin 2) : 0 ≤ ε / 2 + (ε / 2) * z j ∧ ε / 2 + (ε / 2) * z j ≤ ε := by
      have hj := mem_iInter.mp hz j
      change z j ∈ Ioo (-1 : ℝ) 1 at hj
      constructor <;> nlinarith only [half_pos hε, hj.1, hj.2]
    have hsp : (b (T z)).1 0 ∈ Icc (0 : ℝ) ε := hc 0
    have ht : 0 ≤ (b (T z)).2 0 / ε ∧ (b (T z)).2 0 / ε ≤ 1 :=
      ⟨div_nonneg (hc 1).1 hε.le, (div_le_one hε).mpr (hc 1).2⟩
    exact norm_affine_pair_le ht.1 ht.2 (hM _ (hLineTarget i side 0 _ hsp))
      (hM _ (hLineTarget i side 1 _ hsp))
  have hPointEH (side : Bool) (i : Fin 2) (positive : Bool) (x : Domain 1) :
      U side (cubicalSignedFaceIsometry 1 i positive
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) =
      E (if i = 0 then WithLp.toLp 2 ![if positive then 1 else -1, x 0, if side then 1 else -1]
        else WithLp.toLp 2 ![x 0, if positive then 1 else -1, if side then 1 else -1]) := by
    rw [positive_prism_signed_cap_coordinates]
    fin_cases i <;> cases side <;> cases positive <;> simp [E]
  have hPhysical (i : Fin 2) (side : Bool) (x : Domain 1) :
      edgePoint i side (ε / 2 + (ε / 2) * x 0) =
        T (cubicalSignedFaceIsometry 1 i side
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) := by
    have h := affine_unit_square_axis_endpoint i side ε x
    have hbase : (WithLp.toLp 2 (fun _ : Fin 1 => ε / 2)) + (ε / 2) • x =
        EuclideanSpace.single (0 : Fin 1) (ε / 2 + (ε / 2) * x 0) := by
      ext j
      fin_cases j
      rfl
    simpa only [edgePoint, δ, hbase] using h.symm
  have hPointES (i : Fin 2) (side positive : Bool) (x : Domain 1) :
      (1 - (ε / 2 + (ε / 2) * x 0) / ε) • f i side 0 (δ positive) +
        ((ε / 2 + (ε / 2) * x 0) / ε) • f i side 1 (δ positive) =
      E (if i = 0 then WithLp.toLp 2 ![if side then 1 else -1, if positive then 1 else -1, x 0]
        else WithLp.toLp 2 ![if positive then 1 else -1, if side then 1 else -1, x 0]) := by
    let xv : Domain 1 := EuclideanSpace.single (0 : Fin 1) (if positive then (1 : ℝ) else -1)
    have hτsign : ε / 2 + (ε / 2) * xv 0 = δ positive := by
      cases positive <;> dsimp [xv, δ] <;> simp
    have hCorner := hPhysical i side xv
    rw [hτsign, positive_prism_signed_cap_coordinates] at hCorner
    have hτ : (ε / 2 + (ε / 2) * x 0) / ε = (x 0 + 1) / 2 := by
      field_simp [hε.ne']
      ring
    simp only [f, hCorner, hτ]
    fin_cases i <;> cases positive <;> simp [E, U, index, xv]
  have hEH : ∀ side i (positive : Bool),
      (KH side i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
        by cases positive <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict S]
        (fun x => E (if i = 0 then WithLp.toLp 2 ![if positive then 1 else -1, x 0, if side then 1 else -1]
          else WithLp.toLp 2 ![x 0, if positive then 1 else -1, if side then 1 else -1])) := by
    intro side i positive
    obtain ⟨hs, heq⟩ := hKHend side i positive
    have hEq := heq ▸ hs.coeFn_toLp
    filter_upwards [hEq] with x hx
    exact hx.trans (hPointEH side i positive x)
  have hET : ∀ i side (positive : Bool),
      (HT i side ⟨if positive then 1 else -1, by cases positive <;> norm_num,
        by cases positive <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict S]
        (fun x => E (if i = 0 then WithLp.toLp 2 ![if side then 1 else -1, x 0, if positive then 1 else -1]
          else WithLp.toLp 2 ![x 0, if side then 1 else -1, if positive then 1 else -1])) := by
    intro i side positive
    have hEndpoint : ∃ hs : MemLp
        ((fun x : Domain 1 => f i side (index positive) (x 0)) ∘
          fun x => (WithLp.toLp 2 (fun _ : Fin 1 => ε / 2)) + (ε / 2) • x)
        2 (volume.restrict S),
        HT i side ⟨if positive then 1 else -1, by cases positive <;> norm_num,
          by cases positive <;> norm_num⟩ = hs.toLp _ := by
      cases positive
      · exact hHT₀ i side
      · exact hHT₁ i side
    obtain ⟨hs, heq⟩ := hEndpoint
    have hEq := heq ▸ hs.coeFn_toLp
    filter_upwards [hEq] with x hx
    rw [hx]
    change u (index positive) (edgePoint i side (ε / 2 + (ε / 2) * x 0)) = _
    rw [hPhysical]
    exact hPointEH positive i side x
  have hES : ∀ i side (positive : Bool),
      (HS i side ⟨if positive then 1 else -1, by cases positive <;> norm_num,
        by cases positive <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict S]
        (fun x => E (if i = 0 then WithLp.toLp 2 ![if side then 1 else -1, if positive then 1 else -1, x 0]
          else WithLp.toLp 2 ![if positive then 1 else -1, if side then 1 else -1, x 0])) := by
    intro i side positive
    have hEndpoint : ∃ hs : MemLp
        ((fun x : Domain 1 => (1 - x 0 / ε) • F i side 0 (δ positive) +
          (x 0 / ε) • F i side 1 (δ positive)) ∘
          fun x => (WithLp.toLp 2 (fun _ : Fin 1 => ε / 2)) + (ε / 2) • x)
        2 (volume.restrict S),
        HS i side ⟨if positive then 1 else -1, by cases positive <;> norm_num,
          by cases positive <;> norm_num⟩ = hs.toLp _ := by
      cases positive
      · exact hHS₀ i side
      · exact hHS₁ i side
    obtain ⟨hs, heq⟩ := hEndpoint
    have hEq := heq ▸ hs.coeFn_toLp
    filter_upwards [hEq] with x hx
    rw [hx]
    simp only [Function.comp_apply, hLineEnds]
    exact hPointES i side positive x
  obtain ⟨G, D, hCap, hW, hEnergy, hTrace, hProp⟩ :=
    exists_cubical_six_face_filling U DU V DV E hU hV M hBU hBV KH HT HS
      hKHraw hHT hHS hEH hET hES
  refine ⟨G, D, hCap, hW, ?_, ?_, hTrace⟩
  · apply hEnergy.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
    apply add_le_add
    · have hEE (side : Bool) : (∫ z in B.val, hsNormSq (DU side z)) =
          ∫ z in P.val, hsNormSq (Du (index side) z) := by
        simpa only [show (2 - ((2 : ℕ) : ℤ)) = (0 : ℤ) by norm_num, zpow_zero, one_mul]
          using (hNorm side).2.1
      change (∑ side : Bool, ∫ z in B.val, hsNormSq (DU side z)) ≤
        ∑ l : Fin 2, ∫ z in P.val, hsNormSq (Du l z)
      rw [Fintype.sum_bool, hEE true, hEE false, Fin.sum_univ_two]
      change (∫ z in P.val, hsNormSq (Du 1 z)) + (∫ z in P.val, hsNormSq (Du 0 z)) ≤
        (∫ z in P.val, hsNormSq (Du 0 z)) + (∫ z in P.val, hsNormSq (Du 1 z))
      linarith
    · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun side _ => (hVert i side).2.1
  · have hNonneg (i : Fin 2) (side : Bool) : 0 ≤ Dedge i side / ε +
        Real.sqrt (2 * Dedge i side * Aedge i side) :=
      add_nonneg (div_nonneg (integral_nonneg fun _ => sq_nonneg _) hε.le) (Real.sqrt_nonneg _)
    apply hProp (fun z => (infDist z N) ^ 2 ≤
      ∑ i : Fin 2, ∑ side : Bool, (Dedge i side / ε + Real.sqrt (2 * Dedge i side * Aedge i side)))
    · intro side
      filter_upwards [hUTarget side] with z hz
      rw [infDist_zero_of_mem hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun side _ => hNonneg i side
    · intro i side
      filter_upwards [ae_restrict_mem B.property.measurableSet] with z hz
      have hc : ∀ j, z j ∈ Icc (-1 : ℝ) 1 := fun j =>
        ⟨(mem_iInter.mp hz j).1.le, (mem_iInter.mp hz j).2.le⟩
      exact ((hVert i side).2.2.1 z hc).trans
        ((Finset.single_le_sum (fun b _ => hNonneg i b) (Finset.mem_univ side)).trans
          (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun b _ => hNonneg j b) (Finset.mem_univ i)))

end StratificationTheory
