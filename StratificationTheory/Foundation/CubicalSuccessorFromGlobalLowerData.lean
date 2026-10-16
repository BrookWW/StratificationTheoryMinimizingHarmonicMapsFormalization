module

public import StratificationTheory.Foundation.CubicalFaceFamilyExtension
public import StratificationTheory.Foundation.CompatibleChartValueExtension
public import StratificationTheory.Foundation.CompactDistanceNormBound
public import StratificationTheory.Foundation.CubicalDoubleFacetGeometry

public section

open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology BigOperators

namespace StratificationTheory

/-- Original face graphs and complete raw coordinate curves with endpoint
classes in one global lower family produce the next-dimensional cube.
The actual lower-chart parameterizations are injective geometric data.
Recovery of the signed normal pair and original native arguments gives the
common codimension-two representative, new graph, energy, distance bound
and all complete original face traces are constructed internally. -/
theorem exists_cubical_successor_from_global_lower_data {n q : ℕ} {L Y : Type*}
    (f : (Fin (n + 3) × Bool) → Domain (n + 2) → Ambient q)
    (Df : (Fin (n + 3) × Bool) → Domain (n + 2) → Gradient (n + 2) q)
    (R : L → Domain (n + 1) → Ambient q)
    (lookup : Finset (Fin (n + 3) × Bool) → L)
    (arg : ((Fin (n + 3) × Bool) × (Fin (n + 2) × Bool)) → Domain (n + 1) → Domain (n + 1))
    (lowerChart : L → Domain (n + 1) → Y) (parentChart : Domain (n + 3) → Y)
    {N : Set (Ambient q)} (hN : IsCompact N) (C : (Fin (n + 3) × Bool) → ℝ) :
    let J := Fin (n + 3) × Bool
    let I := J × (Fin (n + 2) × Bool)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 2) (m := 1)
    let S := ⋂ k : Fin (n + 1), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain (n + 2) :=
      ⟨⋂ k : Fin (n + 2), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 2) => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let Ω : OpenDomain (n + 3) :=
      ⟨⋂ k : Fin (n + 3), (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun k : Fin (n + 3) => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous)⟩
    let chart := fun (l : I) (x : Domain (n + 1)) => cubicalSignedFaceIsometry (n + 2) l.1.1 l.1.2
      (e.symm (cubicalSignedFaceIsometry (n + 1) l.2.1 l.2.2
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) 1)), EuclideanSpace.single (0 : Fin 1) 1))
    let normals := fun l : I => ({l.1, ((Equiv.swap (Fin.last (n + 2)) l.1.1) l.2.1.castSucc, l.2.2)} :
      Finset (Fin (n + 3) × Bool))
    let key := lookup ∘ normals
    (∀ j : J, MemW12 B (f j) (Df j)) →
    (∃ j : J, ∀ᵐ x ∂volume.restrict B.val, f j x ∈ N) →
    (∀ j : J, ∀ᵐ x ∂volume.restrict B.val, (infDist (f j x) N) ^ 2 ≤ C j) →
    (∀ l : L, Function.Injective (lowerChart l)) →
    (∀ (l : I) (x : Domain (n + 1)), x ∈ S →
      lowerChart (key l) (arg l x) = parentChart (chart l x)) →
    ∀ K : J → Fin (n + 2) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict S)),
    (∀ j i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => f j (cubicalSignedFaceIsometry (n + 1) i true
        (b.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict S),
        K j i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => f j (cubicalSignedFaceIsometry (n + 1) i true
          (b.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) →
    (∀ j i positive,
      (K j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 1) → Ambient q)
        =ᵐ[volume.restrict S] (fun x => R (key (j, i, positive)) (arg (j, i, positive) x))) →
    ∃ (G : Domain (n + 3) → Ambient q) (D : Domain (n + 3) → Gradient (n + 3) q),
      let W := fun z : Domain (n + 3) => G (‖WithLp.ofLp z‖⁻¹ • z)
      (∀ j x, x ∈ B.val → G (cubicalSignedFaceIsometry (n + 2) j.1 j.2
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1))) = f j x) ∧
      MemW12 Ω W D ∧
      (∫ z in Ω.val, hsNormSq (D z)) =
        ((n + 2 : ℕ) - (1 : ℝ))⁻¹ * ∑ j : J, ∫ x in B.val,
          hsNormSq (Df j x) + ‖∑ i : Fin (n + 2), x i • Df j x i‖ ^ 2 ∧
      (∫ z in Ω.val, hsNormSq (D z)) ≤
        (((n + 2 : ℕ) + (1 : ℝ)) / ((n + 2 : ℕ) - (1 : ℝ))) *
          ∑ j : J, ∫ x in B.val, hsNormSq (Df j x) ∧
      (∀ᵐ z ∂volume.restrict Ω.val, (infDist (W z) N) ^ 2 ≤ ∑ j : J, max (C j) 0) ∧
      (∃ H : Fin (n + 3) → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B.val)),
        (∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hs : MemLp (fun x => W (cubicalSignedFaceIsometry (n + 2) i true
            (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) 2 (volume.restrict B.val),
            H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x => W (cubicalSignedFaceIsometry (n + 2) i true
              (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))))) ∧
        ∀ i positive,
          (H i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 2) → Ambient q)
            =ᵐ[volume.restrict B.val] f (i, positive)) ∧
      ∀ P : Ambient q → Prop, (∀ j : J, ∀ᵐ x ∂volume.restrict B.val, P (f j x)) →
        ∀ᵐ z ∂volume.restrict Ω.val, P (W z) := by
  classical
  intro J I b e S B Ω chart normals key hFace hOriginal hDist hInjective hEmbedding K hK hEnd
  have hPhysical (l l' : I) (x : Domain (n + 1)) (hx : x ∈ S)
      (z : Domain (n + 1)) (hz : z ∈ S) (hPoint : chart l x = chart l' z) :
      key l = key l' ∧ arg l x = arg l' z := by
    have hNormals : normals l = normals l' :=
      cubical_double_facet_signed_normals_unique (k := n + 1) l.1.1 l'.1.1 l.2.1 l'.2.1
        l.1.2 l.2.2 l'.1.2 l'.2.2 x z ((mem_unit_coordinate_face_iff x).mp hx)
          ((mem_unit_coordinate_face_iff z).mp hz) hPoint
    have hKey : key l = key l' := congrArg lookup hNormals
    refine ⟨hKey, ?_⟩
    apply hInjective (key l')
    have h := (hEmbedding l x hx).trans ((congrArg parentChart hPoint).trans (hEmbedding l' z hz).symm)
    rwa [hKey] at h
  let lower := fun (l : I) (x : Domain (n + 1)) => R (key l) (arg l x)
  have hCompat : ∀ (l l' : I) (x : Domain (n + 1)), x ∈ S → ∀ z : Domain (n + 1), z ∈ S →
      chart l x = chart l' z → lower l x = lower l' z := by
    intro l l' x hx z hz hPoint
    obtain ⟨hKey, hArg⟩ := hPhysical l l' x hx z hz hPoint
    change R (key l) (arg l x) = R (key l') (arg l' z)
    rw [hKey, hArg]
  obtain ⟨E, hE⟩ := exists_ambient_representative_of_compatible_charts (fun _ : I => S) chart lower hCompat
  have hEndE j i (positive : Bool) :
      (K j i ⟨if positive then 1 else -1, by cases positive <;> norm_num, by cases positive <;> norm_num⟩ : Domain (n + 1) → Ambient q)
        =ᵐ[volume.restrict S] (fun x => E (chart (j, i, positive) x)) := by
    filter_upwards [hEnd j i positive, ae_restrict_mem (MeasurableSet.iInter fun k : Fin (n + 1) =>
      measurableSet_Ioo.preimage (EuclideanSpace.proj k).continuous.measurable)] with x hx hxS
    exact hx.trans (hE (j, i, positive) x hxS).symm
  obtain ⟨j₀, hj₀⟩ := hOriginal
  obtain ⟨M, hM⟩ := exists_uniform_norm_bound_of_compact_distance (volume.restrict B.val) f hN
    (target_nonempty_of_ae_unit_cube (f j₀) hj₀) C hDist
  obtain ⟨G, D, hCap, hW, hExact, hEnergy, hTrace, hProp⟩ :=
    exists_cubical_face_family_extension f Df E hFace M hM K hK hEndE
  refine ⟨G, D, hCap, hW, hExact, hEnergy, ?_, hTrace, hProp⟩
  apply hProp (fun z => (infDist z N) ^ 2 ≤ ∑ j : J, max (C j) 0)
  intro j
  exact (hDist j).mono fun _ hz => hz.trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun k _ => le_max_right (C k) 0) (Finset.mem_univ j)))

end StratificationTheory
