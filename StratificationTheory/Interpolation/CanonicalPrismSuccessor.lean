module

public import StratificationTheory.Foundation.PrismUnitPhysicalEnergy
public import StratificationTheory.Foundation.CanonicalSourcePrismCharts
public import StratificationTheory.Foundation.CanonicalSortedPrismFacetFamily
public import StratificationTheory.Foundation.SortedPrismLowerCellLookup
public import StratificationTheory.Foundation.CanonicalHorizontalBoundaryLookup
public import StratificationTheory.Foundation.CanonicalVerticalBoundaryLookup
public import StratificationTheory.Foundation.CanonicalLowerBoundaryCharts
public import StratificationTheory.Foundation.CanonicalPrismTimeCap
public import StratificationTheory.Foundation.OriginalCanonicalFaceClasses
public import StratificationTheory.Foundation.CubicalReorderedFaceClasses
public import StratificationTheory.Foundation.CubicalSuccessorFromGlobalLowerData

public section

open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- Original horizontal faces and one coherent global family of lower
prisms produce the next prism, with its actual weak graph, complete original
trace classes, physical energy recurrence, distance bound, and value inheritance. -/
theorem exists_canonical_prism_successor {k N q : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (w : Fin 2 → Domain N → Ambient q) (Dw : Fin 2 → Domain N → Gradient N q)
    (Target : Set (Ambient q)) (hTargetCompact : IsCompact Target) :
    let Cell := fun r : ℕ => {c : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (c.val.1 : Fin r → Fin N)}
    let e := fun r : ℕ => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := r) (m := 1)
    let B := fun r : ℕ => (⟨⋂ i : Fin r, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
      isOpen_iInter_of_finite fun i : Fin r => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous⟩ : OpenDomain r)
    let Pos := fun r : ℕ => ⋂ i : Fin r, (EuclideanSpace.proj i) ⁻¹' Ioo (0 : ℝ) ε
    let source := fun (r : ℕ) (c : Cell r) (z : Domain r) =>
      c.val.val.2 + ∑ j : Fin r, z j • EuclideanSpace.single (c.val.val.1 j) (1 : ℝ)
    let T : (r : ℕ) → Domain r → Domain r := fun r z =>
      WithLp.toLp 2 (fun _ : Fin r => ε / 2) + (ε / 2) • z
    let U := fun (r : ℕ) (c : Cell r) (l : Fin 2) => w l ∘ source r c ∘ T r
    let DU := fun (r : ℕ) (c : Cell r) (l : Fin 2) (z : Domain r) (j : Fin r) =>
      (ε / 2) • Dw l (source r c (T r z)) (c.val.val.1 j)
    let sourceEnergy := fun (r : ℕ) (c : Cell r) => ∑ l : Fin 2, ∫ z in Pos r,
      hsNormSq (fun j => Dw l (source r c z) (c.val.val.1 j))
    let physical := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1)
    let P := fun (r : ℕ) (c : Cell r) (z : Domain (r + 1)) => physical.symm
      (source r c (T r ((e r z).1)), EuclideanSpace.single (0 : Fin 1)
        (ε / 2 + (ε / 2) * (e r z).2 0))
    ∀ (child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r)
      (frame : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Equiv.Perm (Fin (r + 1))),
    (∀ r c i side, (child r c i side).val.val.1 = i.succAboveEmb.trans c.val.val.1) →
    (∀ r c i side, (child r c i side).val.val.2 = c.val.val.2 +
      (if side then ε else 0) • EuclideanSpace.single (c.val.val.1 i) (1 : ℝ)) →
    (∀ r c i, frame r c i i = Fin.last r) →
    (∀ r c i (a : Fin r), frame r c i (i.succAbove a) = a.castSucc) →
    (∀ r c i side (z : Domain (r + 1)), P (r + 1) c
      (cubicalSignedFaceIsometry (r + 1) i.castSucc side
        ((e (r + 1)).symm (z, EuclideanSpace.single (0 : Fin 1) 1))) =
      P r (child r c i side) ((cubicalSignedPermutation (r + 1) (frame r c i) (fun _ => true)) z)) →
    ∀ (parent : Cell (k + 2))
      (V : Cell (k + 1) → Domain (k + 2) → Ambient q)
      (DV : Cell (k + 1) → Domain (k + 2) → Gradient (k + 2) q)
      (Vlower : Cell k → Domain (k + 1) → Ambient q)
      (Tube : Cell (k + 1) → ℝ)
      (H : Cell (k + 1) → Fin (k + 2) →
        C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B (k + 1)).val)))
      (Ksource : Fin 2 → Fin (k + 2) →
        C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B (k + 1)).val))),
    (∀ c, MemW12 (B (k + 2)) (V c) (DV c)) →
    (∀ c, 0 ≤ Tube c) →
    (∀ c, ∀ᵐ z ∂volume.restrict (B (k + 2)).val, (infDist (V c z) Target) ^ 2 ≤ Tube c) →
    (∀ c i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => V c (cubicalSignedFaceIsometry (k + 1) i true
        ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B (k + 1)).val),
      H c i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => V c (cubicalSignedFaceIsometry (k + 1) i true
        ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ c (side : Bool),
      (H c (Fin.last (k + 1)) ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
          U (k + 1) c (if side then 1 else 0)) →
    (∀ c (i : Fin (k + 1)) (side : Bool),
      (H c i.castSucc ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
          Vlower (child k c i side) ∘ (cubicalSignedPermutation (k + 1) (frame k c i) (fun _ => true))) →
    (∀ l, MemW12 (B (k + 2)) (U (k + 2) parent l) (DU (k + 2) parent l)) →
    (∀ l, (∫ z in (B (k + 2)).val, hsNormSq (DU (k + 2) parent l z)) =
      (ε / 2) ^ ((2 : ℤ) - (k + 2 : ℕ)) * ∫ z in Pos (k + 2),
        hsNormSq (fun j => Dw l (source (k + 2) parent z) (parent.val.val.1 j))) →
    (∀ l, ∀ᵐ z ∂volume.restrict (B (k + 2)).val, U (k + 2) parent l z ∈ Target) →
    (∀ l i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => U (k + 2) parent l (cubicalSignedFaceIsometry (k + 1) i true
        ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B (k + 1)).val),
      Ksource l i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => U (k + 2) parent l
        (cubicalSignedFaceIsometry (k + 1) i true ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ l i (side : Bool),
      (Ksource l i ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
        (fun x => U (k + 2) parent l (cubicalSignedFaceIsometry (k + 1) i side
          ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) 1))))) →
    ∃ (G : Domain (k + 3) → Ambient q) (D : Domain (k + 3) → Gradient (k + 3) q)
      (K : Fin (k + 3) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (B (k + 2)).val))),
      let W := fun z : Domain (k + 3) => G (‖WithLp.ofLp z‖⁻¹ • z)
      let A := fun i : Fin (k + 2) => cubicalSignedPermutation (k + 2) (frame (k + 1) parent i) (fun _ => true)
      MemW12 (B (k + 3)) W D ∧
      (∫ z in (B (k + 3)).val, hsNormSq (D z)) ≤
        (((k : ℝ) + 3) / ((k : ℝ) + 1)) *
          ((∑ l : Fin 2, ∫ z in (B (k + 2)).val, hsNormSq (DU (k + 2) parent l z)) +
            ∑ i : Fin (k + 2), ∑ side : Bool, ∫ z in (B (k + 2)).val,
              hsNormSq (DV (child (k + 1) parent i side) z)) ∧
      (ε / 2) ^ ((k + 1 : ℕ) : ℤ) * (∫ z in (B (k + 3)).val, hsNormSq (D z)) ≤
        (((k : ℝ) + 3) / ((k : ℝ) + 1)) * (ε / 2) *
          (sourceEnergy (k + 2) parent + ∑ i : Fin (k + 2), ∑ side : Bool,
            (ε / 2) ^ (k : ℤ) * ∫ z in (B (k + 2)).val, hsNormSq (DV (child (k + 1) parent i side) z)) ∧
      (∀ᵐ z ∂volume.restrict (B (k + 3)).val, (infDist (W z) Target) ^ 2 ≤
        ∑ i : Fin (k + 2), ∑ side : Bool, Tube (child (k + 1) parent i side)) ∧
      (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => W (cubicalSignedFaceIsometry (k + 2) i true
          ((e (k + 2)).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B (k + 2)).val),
        K i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (cubicalSignedFaceIsometry (k + 2) i true
          ((e (k + 2)).symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
      (∀ side : Bool,
        (K (Fin.last (k + 2)) ⟨if side then 1 else -1, by cases side <;> norm_num,
          by cases side <;> norm_num⟩ : Domain (k + 2) → Ambient q) =ᵐ[volume.restrict (B (k + 2)).val]
            U (k + 2) parent (if side then 1 else 0)) ∧
      (∀ (i : Fin (k + 2)) (side : Bool),
        (K i.castSucc ⟨if side then 1 else -1, by cases side <;> norm_num,
          by cases side <;> norm_num⟩ : Domain (k + 2) → Ambient q) =ᵐ[volume.restrict (B (k + 2)).val]
            V (child (k + 1) parent i side) ∘ A i) ∧
      ∀ PropValue : Ambient q → Prop,
        (∀ l, ∀ᵐ z ∂volume.restrict (B (k + 2)).val, PropValue (U (k + 2) parent l z)) →
        (∀ (i : Fin (k + 2)) (side : Bool), ∀ᵐ z ∂volume.restrict (B (k + 2)).val,
          PropValue (V (child (k + 1) parent i side) z)) →
        ∀ᵐ z ∂volume.restrict (B (k + 3)).val, PropValue (W z)
 := by
  classical
  intro Cell e B Pos source T U DU sourceEnergy physical P child frame hAxes hOrigin
    hFrameTime hFrameSpatial hPhysical parent V DV Vlower Tube H Ksource
    hV hTube hDist hH hEndTime hEndSpatial hU hUEnergy hUTarget hK hKEnd
  let oldFace := fun (c : Cell (k + 1)) (j : Fin (k + 2) × Bool) =>
    Fin.lastCases (motive := fun _ : Fin (k + 2) => Domain (k + 1) → Ambient q)
      (U (k + 1) c (if j.2 then 1 else 0))
      (fun a => Vlower (child k c a j.2) ∘
        (cubicalSignedPermutation (k + 1) (frame k c a) (fun _ => true))) j.1
  have hOldEnd (c : Cell (k + 1)) (j : Fin (k + 2)) (side : Bool) :
      (H c j ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
        oldFace c (j, side) := by
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simpa only [oldFace, Fin.lastCases_last] using hEndTime c side
    · simpa only [oldFace, Fin.lastCases_castSucc] using hEndSpatial c a side
  let A := fun i : Fin (k + 2) => cubicalSignedPermutation (k + 2)
    (frame (k + 1) parent i) (fun _ => true)
  have hVertical (i : Fin (k + 2)) (side : Bool) :=
    exists_cubical_reordered_pair_of_face_classes
      (V (child (k + 1) parent i side)) (DV (child (k + 1) parent i side))
      (oldFace (child (k + 1) parent i side)) (frame (k + 1) parent i) (fun _ => true)
      (hV _) (H _) (hH _) (hOldEnd _)
  have hVerticalCurves (i : Fin (k + 2)) (side : Bool) := (hVertical i side).2.2.1
  choose r t KH hData using hVerticalCurves
  have hVW (i : Fin (k + 2)) (side : Bool) := (hVertical i side).1
  have hVE (i : Fin (k + 2)) (side : Bool) := (hVertical i side).2.1
  have hVP (i : Fin (k + 2)) (side : Bool) := (hVertical i side).2.2.2
  let RV := fun i side j => cubicalSignedPermutation (k + 1) (r i side j) (t i side j)
  let L := (Cell (k + 1) × Bool) ⊕ Cell k
  let sourceChart := fun (r : ℕ) (c : Cell r) (side : Bool) (x : Domain r) =>
    physical.symm (source r c (T r x),
      EuclideanSpace.single (0 : Fin 1) (if side then ε else 0))
  let lowerChart : L → Domain (k + 1) → Domain (N + 1) :=
    Sum.elim (fun c => sourceChart (k + 1) c.1 c.2) (P k)
  let lowerValue : L → Domain (k + 1) → Ambient q :=
    Sum.elim (fun c => U (k + 1) c.1 (if c.2 then 1 else 0)) Vlower
  obtain ⟨lookup, rs, hLookupTime, hLookupSpace, hLowerInjective, hTimeChart,
      hSourcePoint, hHorizontalEmbedding⟩ :=
    exists_canonical_source_prism_charts (k := k) grid offset hε child hAxes hOrigin parent
  let RS := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (rs i)
  have hHorizontalEnd (l : Fin 2) (i : Fin (k + 2)) (side : Bool) :
      (Ksource l i ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
      (fun x => U (k + 1) (child (k + 1) parent i side) l (RS i x)) := by
    filter_upwards [hKEnd l i side] with x hx
    exact hx.trans (congrArg (w l) (hSourcePoint i side x))
  let argV := fun (i : Fin (k + 2)) (side : Bool) (j : Fin (k + 2)) (_t : Bool)
      (x : Domain (k + 1)) => Fin.insertNth (α := fun _ : Fin (k + 2) => Domain (k + 1)) i
        (RV i side j x) (fun a => (cubicalSignedPermutation (k + 1)
          (frame k (child (k + 1) parent i side) a) (fun _ => true)) (RV i side j x)) j
  have hVerticalBlock (i : Fin (k + 2)) (side : Bool) (j : Fin (k + 2))
      (x : Domain (k + 1)) (η : ℝ) : A i
      (cubicalSignedFaceIsometry (k + 1) j true
        ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) η))) =
      cubicalSignedFaceIsometry (k + 1) ((frame (k + 1) parent i) j) true
        ((e (k + 1)).symm (RV i side j x, EuclideanSpace.single (0 : Fin 1) η)) := by
    exact (hData i side j).1 x η
  have hVerticalEmbedding (i : Fin (k + 2)) (side : Bool) (j : Fin (k + 2))
      (t : Bool) (x : Domain (k + 1)) : P (k + 2) parent
      (cubicalSignedFaceIsometry (k + 2) i.castSucc side
        ((e (k + 2)).symm (cubicalSignedFaceIsometry (k + 1) j t
          ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
          EuclideanSpace.single (0 : Fin 1) 1))) =
      lowerChart (lookup {(i.castSucc, side),
        ((Equiv.swap (Fin.last (k + 2)) i.castSucc) j.castSucc, t)}) (argV i side j t x) := by
    exact canonical_vertical_boundary_lookup_chart child frame parent i side
      (frame (k + 1) parent i) (hFrameTime _ _ _) (hFrameSpatial _ _ _)
      (fun j => RV i side j) (sourceChart (k + 1)) (P k) lookup (hLookupTime i side)
      (fun a t => hLookupSpace i a side t) (P (k + 1)) (P (k + 2) parent)
      (hPhysical (k + 1) parent i side) (hTimeChart (k + 1) _) (hPhysical k _)
      (hVerticalBlock i side) j t x
  have hVerticalEnd (i : Fin (k + 2)) (side : Bool) (j : Fin (k + 2)) (positive : Bool) :
      (KH i side j ⟨if positive then 1 else -1, by cases positive <;> norm_num,
        by cases positive <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
      (fun x => lowerValue (lookup {(i.castSucc, side),
        ((Equiv.swap (Fin.last (k + 2)) i.castSucc) j.castSucc, positive)})
          (argV i side j positive x)) := by
    have hEnd := (hData i side j).2.2 positive
    have hRaw : (KH i side j ⟨if positive then 1 else -1, by cases positive <;> norm_num,
        by cases positive <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
        (fun x => oldFace (child (k + 1) parent i side)
          ((frame (k + 1) parent i) j, positive) (RV i side j x)) := by
      cases positive <;> simpa only [B, RV, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] using hEnd
    filter_upwards [hRaw] with x hx
    exact hx.trans (canonical_vertical_boundary_lookup_value child frame parent i side
      (frame (k + 1) parent i) (hFrameTime _ _ _) (hFrameSpatial _ _ _)
      (fun j => RV i side j) (fun c side => U (k + 1) c (if side then 1 else 0)) Vlower
      lookup (hLookupTime i side) (fun a t => hLookupSpace i a side t) j positive x)
  have hHorizontalEndLookup (t : Bool) (j : Fin (k + 2)) (side : Bool) :
      (Ksource (if t then 1 else 0) j ⟨if side then 1 else -1, by cases side <;> norm_num,
        by cases side <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
      (fun x => lowerValue (lookup {(Fin.last (k + 2), t), (j.castSucc, side)}) (RS j x)) := by
    have hLook : lookup {(Fin.last (k + 2), t), (j.castSucc, side)} =
        Sum.inl (child (k + 1) parent j side, t) := by rw [Finset.pair_comm, hLookupTime]
    simpa only [hLook, lowerValue, Sum.elim_inl] using
      hHorizontalEnd (if t then 1 else 0) j side
  let J := Fin (k + 3) × Bool
  let f : J → Domain (k + 2) → Ambient q := fun j => Fin.lastCases
    (motive := fun _ : Fin (k + 3) => Domain (k + 2) → Ambient q)
      (U (k + 2) parent (if j.2 then 1 else 0))
      (fun i => V (child (k + 1) parent i j.2) ∘ A i) j.1
  let Df : J → Domain (k + 2) → Gradient (k + 2) q := fun j => Fin.lastCases
    (motive := fun _ : Fin (k + 3) => Domain (k + 2) → Gradient (k + 2) q)
      (DU (k + 2) parent (if j.2 then 1 else 0))
      (fun i z a => ∑ b : Fin (k + 2), (A i (EuclideanSpace.single a 1)) b •
        DV (child (k + 1) parent i j.2) (A i z) b) j.1
  let KF : J → Fin (k + 2) → C(Icc (-1 : ℝ) 1,
      Lp (Ambient q) 2 (volume.restrict (B (k + 1)).val)) := fun j => Fin.lastCases
    (motive := fun _ : Fin (k + 3) => Fin (k + 2) → C(Icc (-1 : ℝ) 1,
      Lp (Ambient q) 2 (volume.restrict (B (k + 1)).val)))
      (Ksource (if j.2 then 1 else 0)) (fun i => KH i j.2) j.1
  let norms := fun l : J × (Fin (k + 2) × Bool) =>
    ({l.1, ((Equiv.swap (Fin.last (k + 2)) l.1.1) l.2.1.castSucc, l.2.2)} : Finset (Fin (k + 3) × Bool))
  let arg := fun (l : J × (Fin (k + 2) × Bool)) (x : Domain (k + 1)) =>
    Fin.lastCases (motive := fun _ : Fin (k + 3) => Domain (k + 1))
      (RS l.2.1 x) (fun i => argV i l.1.2 l.2.1 l.2.2 x) l.1.1
  have hFace (j : Fin (k + 3)) (side : Bool) : MemW12 (B (k + 2)) (f (j, side)) (Df (j, side)) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [f, Df, Fin.lastCases_last] using hU (if side then 1 else 0)
    · simpa only [f, Df, Fin.lastCases_castSucc, A, B] using hVW i side
  have hKF (j : Fin (k + 3)) (side : Bool) (a : Fin (k + 2)) :
      ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
        ∃ hs : MemLp (fun x => f (j, side) (cubicalSignedFaceIsometry (k + 1) a true
          ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict (B (k + 1)).val),
          KF (j, side) a ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f (j, side)
            (cubicalSignedFaceIsometry (k + 1) a true ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) t)))) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [f, KF, Fin.lastCases_last] using hK (if side then 1 else 0) a
    · simpa only [f, KF, Fin.lastCases_castSucc, B, e, A] using (hData i side a).2.1
  have hKFEnd (j : Fin (k + 3)) (side : Bool) (a : Fin (k + 2)) (t : Bool) :
      (KF (j, side) a ⟨if t then 1 else -1, by cases t <;> norm_num,
        by cases t <;> norm_num⟩ : Domain (k + 1) → Ambient q) =ᵐ[volume.restrict (B (k + 1)).val]
        (fun x => lowerValue (lookup (norms ((j, side), a, t))) (arg ((j, side), a, t) x)) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [KF, norms, arg, Fin.lastCases_last, Equiv.swap_self, Equiv.refl_apply] using
        hHorizontalEndLookup side a t
    · simpa only [KF, norms, arg, Fin.lastCases_castSucc] using hVerticalEnd i side a t
  have hEmbedding (j : Fin (k + 3)) (side : Bool) (a : Fin (k + 2)) (t : Bool) (x : Domain (k + 1)) :
      lowerChart (lookup (norms ((j, side), a, t))) (arg ((j, side), a, t) x) =
      P (k + 2) parent (cubicalSignedFaceIsometry (k + 2) j side
        ((e (k + 2)).symm (cubicalSignedFaceIsometry (k + 1) a t
          ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
          EuclideanSpace.single (0 : Fin 1) 1))) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [norms, arg, Fin.lastCases_last, Equiv.swap_self, Equiv.refl_apply] using
        (hHorizontalEmbedding side a t x).symm
    · simpa only [norms, arg, Fin.lastCases_castSucc] using (hVerticalEmbedding i side a t x).symm
  let Cface : J → ℝ := fun j => Fin.lastCases (motive := fun _ : Fin (k + 3) => ℝ)
    0 (fun i => Tube (child (k + 1) parent i j.2)) j.1
  have hCface (j : J) : 0 ≤ Cface j := by
    rcases j with ⟨j, side⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Cface, Fin.lastCases_last, le_refl]
    · simpa only [Cface, Fin.lastCases_castSucc] using hTube (child (k + 1) parent i side)
  have hFaceDist (j : Fin (k + 3)) (side : Bool) :
      ∀ᵐ z ∂volume.restrict (B (k + 2)).val, (infDist (f (j, side) z) Target) ^ 2 ≤ Cface (j, side) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have h : ∀ᵐ z ∂volume.restrict (B (k + 2)).val,
          (infDist (U (k + 2) parent (if side then 1 else 0) z) Target) ^ 2 ≤ 0 :=
        (hUTarget _).mono fun z hz => by rw [infDist_zero_of_mem hz]; norm_num
      simpa only [f, Cface, Fin.lastCases_last] using h
    · have h := hVP i side (fun v => (infDist v Target) ^ 2 ≤ Tube (child (k + 1) parent i side)) (hDist _)
      simpa only [f, Cface, Fin.lastCases_castSucc, A, B] using h
  have hOriginal : ∃ j : J, ∀ᵐ x ∂volume.restrict (B (k + 2)).val, f j x ∈ Target := by
    refine ⟨(Fin.last (k + 2), false), ?_⟩
    simpa only [f, Fin.lastCases_last, Bool.false_eq_true, ite_false] using hUTarget 0
  obtain ⟨G, D, _hCap, hW, _hExact, hEnergy, hDistance, hTrace, hProperty⟩ :=
    exists_cubical_successor_from_global_lower_data f Df lowerValue lookup arg lowerChart
      (P (k + 2) parent) hTargetCompact Cface (fun j => hFace j.1 j.2) hOriginal
      (fun j => hFaceDist j.1 j.2) hLowerInjective
      (fun l x _ => hEmbedding l.1.1 l.1.2 l.2.1 l.2.2 x)
      KF (fun j a => hKF j.1 j.2 a) (fun j a t => hKFEnd j.1 j.2 a t)
  obtain ⟨K, hKraw, hKend⟩ := hTrace
  have hEnergyV (i : Fin (k + 2)) (side : Bool) :
      (∫ z in (B (k + 2)).val, hsNormSq (Df (i.castSucc, side) z)) =
      ∫ z in (B (k + 2)).val, hsNormSq (DV (child (k + 1) parent i side) z) := by
    simpa only [Df, Fin.lastCases_castSucc, A, B] using hVE i side
  have hEnergyTime (side : Bool) :
      (∫ z in (B (k + 2)).val, hsNormSq (Df (Fin.last (k + 2), side) z)) =
      ∫ z in (B (k + 2)).val, hsNormSq (DU (k + 2) parent (if side then 1 else 0) z) := by
    simp only [Df, Fin.lastCases_last]
  have hEnergyFaces : (∑ j : J, ∫ z in (B (k + 2)).val, hsNormSq (Df j z)) =
      (∑ l : Fin 2, ∫ z in (B (k + 2)).val, hsNormSq (DU (k + 2) parent l z)) +
      ∑ i : Fin (k + 2), ∑ side : Bool, ∫ z in (B (k + 2)).val,
        hsNormSq (DV (child (k + 1) parent i side) z) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
    simp_rw [hEnergyV, hEnergyTime]
    rw [Fintype.sum_bool, Fin.sum_univ_two]
    simp only [Bool.false_eq_true, ite_true, ite_false]
    ring
  have hCoefficient : (((k + 2 : ℕ) + (1 : ℝ)) / ((k + 2 : ℕ) - (1 : ℝ))) =
      ((k : ℝ) + 3) / ((k : ℝ) + 1) := by congr 1 <;> push_cast <;> ring
  rw [hCoefficient, hEnergyFaces] at hEnergy
  have hTubeSum : (∑ j : J, max (Cface j) 0) =
      ∑ i : Fin (k + 2), ∑ side : Bool, Tube (child (k + 1) parent i side) := by
    simp_rw [max_eq_left (hCface _)]
    rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
    simp only [Cface, Fin.lastCases_last, Fin.lastCases_castSucc, Finset.sum_const_zero, add_zero]
  refine ⟨G, D, K, hW, hEnergy, ?_, ?_, hKraw, ?_, ?_, ?_⟩
  · have hSourceSum : (∑ l : Fin 2, ∫ z in (B (k + 2)).val,
          hsNormSq (DU (k + 2) parent l z)) =
        (ε / 2) ^ ((2 : ℤ) - (k + 2 : ℕ)) * sourceEnergy (k + 2) parent := by
      simp only [hUEnergy, sourceEnergy, Finset.mul_sum]
    have hNormalized : (∫ z in (B (k + 3)).val, hsNormSq (D z)) ≤
        (((k : ℝ) + 3) / ((k : ℝ) + 1)) *
          ((ε / 2) ^ ((2 : ℤ) - (k + 2 : ℕ)) * sourceEnergy (k + 2) parent +
            ∑ j : Fin (k + 2) × Bool, ∫ z in (B (k + 2)).val,
              hsNormSq (DV (child (k + 1) parent j.1 j.2) z)) := by
      simpa only [Fintype.sum_prod_type, hSourceSum] using hEnergy
    have hScaled := prism_unit_energy_to_physical k (by positivity : 0 < ε / 2)
      (fun j : Fin (k + 2) × Bool => ∫ z in (B (k + 2)).val,
        hsNormSq (DV (child (k + 1) parent j.1 j.2) z)) hNormalized
    simpa only [Fintype.sum_prod_type] using hScaled
  · exact hDistance.mono fun z hz => hz.trans_eq hTubeSum
  · intro side
    simpa only [f, Fin.lastCases_last] using hKend (Fin.last (k + 2)) side
  · intro i side
    simpa only [f, Fin.lastCases_castSucc] using hKend i.castSucc side
  · intro PropValue hSourceProp hOldProp
    apply hProperty PropValue
    rintro ⟨j, side⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [f, B, Fin.lastCases_last] using hSourceProp (if side then 1 else 0)
    · simpa only [f, Fin.lastCases_castSucc, A, B] using hVP i side PropValue (hOldProp i side)

end StratificationTheory
