module

public import StratificationTheory.Foundation.CoordinateBallFiberSobolev
public import StratificationTheory.Foundation.CubicalFaceSampling

/-!
# One grid with original weak graphs on mixed-dimensional faces

The same grid offset controls two scalar face channels and qualifies the
original Sobolev pair on every member of a countable family of coordinate
rectangles. Dimensions and coordinate orderings may vary. Qualifications are
derived from the original ball data before the offset is chosen.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
namespace StratificationTheory

/-- One offset simultaneously retains the original two weak graphs in all
prescribed coordinate dimensions and both native scalar sampling bounds.
The coordinate rectangles must be contained in the original Sobolev ball;
their weak-graph qualifications are conclusions of the original ball data. -/
theorem exists_grid_translate_qualified_cubical_face_pair_energy
    {N q : ℕ} {ι J : Type*} [Countable ι] [Fintype J]
    {z₀ : Domain N} {R : ℝ} (hR : 0 < R)
    {u v : Domain N → Ambient q}
    {Du Dv : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z₀ R) u Du)
    (hv : MemW12 (ballDomain z₀ R) v Dv)
    (m k : ι → ℕ) (p : ∀ i, Fin (m i + k i) ≃ Fin N)
    (S : ∀ i, Set (Domain (m i))) (hS : ∀ i, MeasurableSet (S i))
    (U : ∀ i, OpenDomain (k i))
    (hrect : ∀ i x, x ∈ S i → ∀ y ∈ (U i).val,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)).symm
          (x, y)) ∈ ball z₀ R)
    (d : J → ℕ) (face : ∀ j, Fin (d j) ↪ Fin N)
    {ε : ℝ} (hε : 0 < ε)
    {f g : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hfFinite : (∫⁻ x, f x) ≠ ⊤)
    (hgFinite : (∫⁻ x, g x) ≠ ⊤) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)
    let X := fun i (y : Domain N) => (e i ((Q i).symm y)).1
    let F := fun i (y : Domain N) (t : Domain (k i)) =>
      Q i ((e i).symm (X i y, t))
    let b := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _j : Fin N => ε) (fun _j => hε.ne'.isUnit)
    let shift := fun (j : J) (t : Fin (d j) → ℝ) (l : Fin N) =>
      ∑ s : Fin (d j), if face j s = l then t s else 0
    let cube := fun j : J => Set.univ.pi (fun _ : Fin (d j) => Ico (0 : ℝ) ε)
    ∃ a : Fin N → ℝ,
      (∀ l, a l ∈ Ico (0 : ℝ) ε) ∧
      (∀ (z : Submodule.span ℤ (Set.range b)) (i : ι),
        X i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) ∈ S i →
        MemW12 (U i)
          (fun t => u (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t))
          (fun t s => Du (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t)
            (p i (Fin.natAdd (m i) s))) ∧
        MemW12 (U i)
          (fun t => v (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t))
          (fun t s => Dv (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t)
            (p i (Fin.natAdd (m i) s)))) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range b)),
        ∀ᵐ t ∂volume.restrict (cube j), ∀ i : ι,
          X i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) ∈ S i →
          MemW12 (U i)
            (fun s => u (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s))
            (fun s l => Du (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s)
              (p i (Fin.natAdd (m i) l))) ∧
          MemW12 (U i)
            (fun s => v (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s))
            (fun s l => Dv (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s)
              (p i (Fin.natAdd (m i) l)))) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube j,
          f (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t))) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ∫⁻ x, f x) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube j,
          g (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t))) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ∫⁻ x, g x) := by
  intro Q e X F b shift cube
  have hqu := ae_memW12_coordinate_face_family_of_memW12_ball hR hu m k p S hS U hrect
  have hqv := ae_memW12_coordinate_face_family_of_memW12_ball hR hv m k p S hS U hrect
  let P : Domain N → Prop := fun y => ∀ i, X i y ∈ S i →
    MemW12 (U i) (fun t => u (F i y t))
      (fun t s => Du (F i y t) (p i (Fin.natAdd (m i) s))) ∧
    MemW12 (U i) (fun t => v (F i y t))
      (fun t s => Dv (F i y t) (p i (Fin.natAdd (m i) s)))
  have hP : ∀ᵐ y ∂volume, P y := by
    filter_upwards [hqu, hqv] with y hyu hyv
    exact fun i hi => ⟨hyu i hi, hyv i hi⟩
  obtain ⟨a, ha, hvertex, hfiber, henergy, hdiscrepancy⟩ :=
    exists_grid_translate_cubical_face_pair_energy d face hε hf hg hfFinite hgFinite hP
  exact ⟨a, ha, hvertex, hfiber, henergy, hdiscrepancy⟩

/-- The same offset gives both native mixed-face scalar bounds and full
original weak graphs on every contained open coordinate face through every
grid vertex. Each open face may be chosen after the offset, so this applies
to the actual translated grid faces without a weak-graph input premise. -/
theorem exists_grid_translate_full_coordinate_face_pair_energy
    {N q : ℕ} {ι J : Type*} [Countable ι] [Fintype J]
    {z₀ : Domain N} {R : ℝ} (hR : 0 < R)
    {u v : Domain N → Ambient q}
    {Du Dv : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z₀ R) u Du)
    (hv : MemW12 (ballDomain z₀ R) v Dv)
    (m k : ι → ℕ) (p : ∀ i, Fin (m i + k i) ≃ Fin N)
    (d : J → ℕ) (face : ∀ j, Fin (d j) ↪ Fin N)
    {ε : ℝ} (hε : 0 < ε)
    {f g : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hfFinite : (∫⁻ x, f x) ≠ ⊤)
    (hgFinite : (∫⁻ x, g x) ≠ ⊤) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)
    let F := fun i (y : Domain N) (t : Domain (k i)) =>
      Q i ((e i).symm ((e i ((Q i).symm y)).1, t))
    let b := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _j : Fin N => ε) (fun _j => hε.ne'.isUnit)
    let shift := fun (j : J) (t : Fin (d j) → ℝ) (l : Fin N) =>
      ∑ s : Fin (d j), if face j s = l then t s else 0
    let cube := fun j : J => Set.univ.pi (fun _ : Fin (d j) => Ico (0 : ℝ) ε)
    ∃ a : Fin N → ℝ,
      (∀ l, a l ∈ Ico (0 : ℝ) ε) ∧
      (∀ (z : Submodule.span ℤ (Set.range b)) (i : ι) (U : OpenDomain (k i)),
        (∀ t ∈ U.val, F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t ∈ ball z₀ R) →
        MemW12 U
          (fun t => u (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t))
          (fun t s => Du (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t)
            (p i (Fin.natAdd (m i) s))) ∧
        MemW12 U
          (fun t => v (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t))
          (fun t s => Dv (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t)
            (p i (Fin.natAdd (m i) s)))) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range b)),
        ∀ᵐ t ∂volume.restrict (cube j), ∀ (i : ι) (U : OpenDomain (k i)),
          (∀ s ∈ U.val,
            F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s ∈ ball z₀ R) →
          MemW12 U
            (fun s => u (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s))
            (fun s l => Du (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s)
              (p i (Fin.natAdd (m i) l))) ∧
          MemW12 U
            (fun s => v (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s))
            (fun s l => Dv (F i (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) s)
              (p i (Fin.natAdd (m i) l)))) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube j,
          f (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t))) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ∫⁻ x, f x) ∧
      (∀ j : J,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in cube j,
          g (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t))) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card J : ℝ≥0∞) * ENNReal.ofReal (ε ^ d j)) * ∫⁻ x, g x) := by
  intro Q e F b shift cube
  have hqu := ae_memW12_all_coordinate_faces_of_memW12_ball hR hu m k p
  have hqv := ae_memW12_all_coordinate_faces_of_memW12_ball hR hv m k p
  let P : Domain N → Prop := fun y => ∀ (i : ι) (U : OpenDomain (k i)),
    (∀ t ∈ U.val, F i y t ∈ ball z₀ R) →
    MemW12 U (fun t => u (F i y t))
      (fun t s => Du (F i y t) (p i (Fin.natAdd (m i) s))) ∧
    MemW12 U (fun t => v (F i y t))
      (fun t s => Dv (F i y t) (p i (Fin.natAdd (m i) s)))
  have hP : ∀ᵐ y ∂volume, P y := by
    filter_upwards [hqu, hqv] with y hyu hyv
    exact fun i U hU => ⟨hyu i U hU, hyv i U hU⟩
  obtain ⟨a, ha, hvertex, hfiber, henergy, hdiscrepancy⟩ :=
    exists_grid_translate_cubical_face_pair_energy d face hε hf hg hfFinite hgFinite hP
  exact ⟨a, ha, hvertex, hfiber, henergy, hdiscrepancy⟩

end StratificationTheory
