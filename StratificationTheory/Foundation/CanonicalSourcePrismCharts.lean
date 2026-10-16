module

public import StratificationTheory.Foundation.CanonicalLowerBoundaryCharts
public import StratificationTheory.Foundation.SortedPrismLowerCellLookup
public import StratificationTheory.Foundation.CanonicalPrismTimeCap
public import StratificationTheory.Foundation.OrderedCoordinateFacetEmbedding

public section
open HarmonicMaps Set
open scoped BigOperators
namespace StratificationTheory

/-- One actual canonical source-cell family determines the same unordered
lower-cell lookup, injective physical charts, and finite native horizontal
facet coordinates. All chart identities hold on their entire carriers. -/
theorem exists_canonical_source_prism_charts {k N : ℕ}
    (grid : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (offset : Fin N → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    let Cell := fun r : ℕ => {c : originalPhysicalCellCarrier r grid offset ε //
      StrictMono (c.val.1 : Fin r → Fin N)}
    let e := fun r : ℕ => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := r) (m := 1)
    let source := fun (r : ℕ) (c : Cell r) (z : Domain r) => c.val.val.2 +
      ∑ j : Fin r, z j • EuclideanSpace.single (c.val.val.1 j) (1 : ℝ)
    let T : (r : ℕ) → Domain r → Domain r := fun r z =>
      WithLp.toLp 2 (fun _ : Fin r => ε / 2) + (ε / 2) • z
    let physical := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 1)
    let P := fun (r : ℕ) (c : Cell r) (z : Domain (r + 1)) => physical.symm
      (source r c (T r ((e r z).1)), EuclideanSpace.single (0 : Fin 1)
        (ε / 2 + (ε / 2) * (e r z).2 0))
    let sourceChart := fun (r : ℕ) (c : Cell r) (side : Bool) (x : Domain r) =>
      physical.symm (source r c (T r x), EuclideanSpace.single (0 : Fin 1) (if side then ε else 0))
    let L := (Cell (k + 1) × Bool) ⊕ Cell k
    let lowerChart : L → Domain (k + 1) → Domain (N + 1) :=
      Sum.elim (fun c => sourceChart (k + 1) c.1 c.2) (P k)
    ∀ child : (r : ℕ) → Cell (r + 1) → Fin (r + 1) → Bool → Cell r,
    (∀ r c i side, (child r c i side).val.val.1 = i.succAboveEmb.trans c.val.val.1) →
    (∀ r c i side, (child r c i side).val.val.2 = c.val.val.2 +
      (if side then ε else 0) • EuclideanSpace.single (c.val.val.1 i) (1 : ℝ)) →
    ∀ parent : Cell (k + 2),
    ∃ (lookup : Finset (Fin (k + 3) × Bool) → L) (rs : Fin (k + 2) → Equiv.Perm (Fin (k + 1))),
      let R := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (rs i)
      (∀ i s t, lookup {(i.castSucc, s), (Fin.last (k + 2), t)} = Sum.inl (child (k + 1) parent i s, t)) ∧
      (∀ i a s t, lookup {(i.castSucc, s), ((i.succAbove a).castSucc, t)} =
        Sum.inr (child k (child (k + 1) parent i s) a t)) ∧
      (∀ l : L, Function.Injective (lowerChart l)) ∧
      (∀ r (c : Cell r) side (x : Domain r), P r c (cubicalSignedFaceIsometry r (Fin.last r) side
        ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = sourceChart r c side x) ∧
      (∀ i side (x : Domain (k + 1)), source (k + 2) parent
        (T (k + 2) (cubicalSignedFaceIsometry (k + 1) i side
          ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) =
        source (k + 1) (child (k + 1) parent i side) (T (k + 1) (R i x))) ∧
      ∀ t j side (x : Domain (k + 1)), P (k + 2) parent
        (cubicalSignedFaceIsometry (k + 2) (Fin.last (k + 2)) t
          ((e (k + 2)).symm (cubicalSignedFaceIsometry (k + 1) j side
            ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) 1)),
            EuclideanSpace.single (0 : Fin 1) 1))) =
        lowerChart (lookup {(Fin.last (k + 2), t), (j.castSucc, side)}) (R j x) := by
  classical
  intro Cell e source T physical P sourceChart L lowerChart child hAxes hOrigin parent
  obtain ⟨lookup, hLookupTime, hLookupSpace⟩ :=
    exists_sorted_prism_lower_cell_lookup grid offset ε child hAxes hOrigin parent
  have hGeometry (i : Fin (k + 2)) :=
    exists_ordered_coordinate_facet_affine_embedding parent.val.val.1 ε parent.val.val.2 i
  choose rs _hSlots hCap _hLift using hGeometry
  let R := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (rs i)
  have hTime (r : ℕ) (c : Cell r) (side : Bool) (x : Domain r) :
      P r c (cubicalSignedFaceIsometry r (Fin.last r) side
        ((e r).symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = sourceChart r c side x := by
    have h := canonical_prism_time_cap_physical_embedding c.val.val.1 ε c.val.val.2 side x
    with_reducible simpa only [P, sourceChart, source, T, PiLp.add_apply, PiLp.smul_apply,
      PiLp.toLp_apply, smul_eq_mul] using h
  have hPoint (i : Fin (k + 2)) (side : Bool) (x : Domain (k + 1)) :
      source (k + 2) parent (T (k + 2) (cubicalSignedFaceIsometry (k + 1) i side
        ((e (k + 1)).symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) =
      source (k + 1) (child (k + 1) parent i side) (T (k + 1) (R i x)) := by
    have h := hCap i side x
    have hEmb : (Fin.succAboveOrderEmb i).toEmbedding = i.succAboveEmb := by
      apply Function.Embedding.ext
      intro a
      rfl
    dsimp only at h
    rw [hEmb] at h
    with_reducible simpa only [source, T, hAxes, hOrigin, R, e, PiLp.add_apply,
      PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul] using h
  refine ⟨lookup, rs, hLookupTime, hLookupSpace, ?_, hTime, hPoint, ?_⟩
  · have h := canonical_lower_boundary_charts_injective (d := k) grid offset hε
    with_reducible simpa only [lowerChart, sourceChart, P, source, T,
      PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul] using h
  · intro t j side x
    rw [hTime, Finset.pair_comm, hLookupTime]
    exact congrArg (fun v : Domain N => physical.symm
      (v, EuclideanSpace.single (0 : Fin 1) (if t then ε else 0))) (hPoint j side x)

end StratificationTheory
