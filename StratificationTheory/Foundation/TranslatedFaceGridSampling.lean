module

public import StratificationTheory.Foundation.TranslatedCoordinateFaceSobolev
public import StratificationTheory.Foundation.CubicalFaceSampling

/-!
# One qualified grid in native translated-face coordinates

The original Sobolev pair produces every contained coordinate-face weak
graph. One offset retains those qualifications, a preassigned ambient
almost-everywhere property, and both mixed-dimensional scalar face bounds.
The ambient property is fixed before selection.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
namespace StratificationTheory

/-- A preassigned original ambient a.e. event and all native translated-face
weak graphs share the same offset and both mixed-dimensional scalar bounds.
The open domains in the weak-graph conclusion may depend on the chosen grid.
The preassigned event itself may not be chosen after the offset. -/
theorem exists_grid_translate_translated_coordinate_face_pair_energy
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
    (hgFinite : (∫⁻ x, g x) ≠ ⊤)
    {P : Domain N → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := fun i => EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m i) (m := k i)
    let A := fun i (y : Domain N) (t : Domain (k i)) =>
      y + Q i ((e i).symm (0, t))
    let G : Domain N → Prop := fun y => ∀ (i : ι) (U : OpenDomain (k i)),
      (∀ t ∈ U.val, A i y t ∈ ball z₀ R) →
      MemW12 U (fun t => u (A i y t))
        (fun t s => Du (A i y t) (p i (Fin.natAdd (m i) s))) ∧
      MemW12 U (fun t => v (A i y t))
        (fun t s => Dv (A i y t) (p i (Fin.natAdd (m i) s)))
    let b := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _j : Fin N => ε) (fun _j => hε.ne'.isUnit)
    let shift := fun (j : J) (t : Fin (d j) → ℝ) (l : Fin N) =>
      ∑ s : Fin (d j), if face j s = l then t s else 0
    let cube := fun j : J => Set.univ.pi (fun _ : Fin (d j) => Ico (0 : ℝ) ε)
    ∃ a : Fin N → ℝ,
      (∀ l, a l ∈ Ico (0 : ℝ) ε) ∧
      (∀ z : Submodule.span ℤ (Set.range b),
        P (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) ∧
        G (WithLp.toLp 2 ((z : Fin N → ℝ) + a))) ∧
      (∀ (j : J) (z : Submodule.span ℤ (Set.range b)),
        ∀ᵐ t ∂volume.restrict (cube j),
          P (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t)) ∧
          G (WithLp.toLp 2 ((z : Fin N → ℝ) + a + shift j t))) ∧
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
  intro Q e A G b shift cube
  have hqu := ae_memW12_all_translated_coordinate_faces_of_memW12_ball hR hu m k p
  have hqv := ae_memW12_all_translated_coordinate_faces_of_memW12_ball hR hv m k p
  have hPG : ∀ᵐ y ∂volume, P y ∧ G y := by
    filter_upwards [hP, hqu, hqv] with y hPy hyu hyv
    exact ⟨hPy, fun i U hU => ⟨hyu i U hU, hyv i U hU⟩⟩
  exact exists_grid_translate_cubical_face_pair_energy d face hε hf hg hfFinite hgFinite hPG

end StratificationTheory
