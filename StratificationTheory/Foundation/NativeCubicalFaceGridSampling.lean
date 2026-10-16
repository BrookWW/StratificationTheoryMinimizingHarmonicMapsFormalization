module

public import StratificationTheory.Foundation.CoordinateFaceNativeMeasure

/-!
# A common grid with native mixed-dimensional face weak graphs

One original offset gives both quantitative scalar channels and full weak
graphs of the original pair on all contained faces. Every face uses the same
literal native translated-coordinate map in its weak graph, raw a.e.
qualifications and nonnegative integrals.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology BigOperators
namespace StratificationTheory

/-- The original Sobolev pair produces all selected face weak graphs in the
same literal native parameterization as both scalar channels. A preassigned
ambient a.e. property is retained at all vertices and on every selected face.
That property is fixed before the grid choice. -/
theorem exists_grid_translate_native_cubical_face_pair_energy
    {N q : ℕ} {ι : Type*} [Fintype ι]
    {z₀ : Domain N} {R : ℝ} (hR : 0 < R)
    {u v : Domain N → Ambient q}
    {Du Dv : Domain N → Gradient N q}
    (hu : MemW12 (ballDomain z₀ R) u Du)
    (hv : MemW12 (ballDomain z₀ R) v Dv)
    (k : ι → ℕ) (face : ∀ i, Fin (k i) ↪ Fin N)
    {ε : ℝ} (hε : 0 < ε)
    {f g : Domain N → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hfFinite : (∫⁻ x, f x) ≠ ⊤)
    (hgFinite : (∫⁻ x, g x) ≠ ⊤)
    {P : Domain N → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    let A := fun i (y : Domain N) (t : Domain (k i)) =>
      y + ∑ j : Fin (k i), t j • EuclideanSpace.single (face i j) (1 : ℝ)
    let G : Domain N → Prop := fun y => ∀ (i : ι) (U : OpenDomain (k i)),
      (∀ t ∈ U.val, A i y t ∈ ball z₀ R) →
      MemW12 U (fun t => u (A i y t)) (fun t j => Du (A i y t) (face i j)) ∧
      MemW12 U (fun t => v (A i y t)) (fun t j => Dv (A i y t) (face i j))
    let b := (Pi.basisFun ℝ (Fin N)).isUnitSMul
      (w := fun _j : Fin N => ε) (fun _j => hε.ne'.isUnit)
    let C := fun i =>
      ⋂ j : Fin (k i), (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) ε
    ∃ a : Fin N → ℝ,
      (∀ l, a l ∈ Ico (0 : ℝ) ε) ∧
      (∀ z : Submodule.span ℤ (Set.range b),
        P (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) ∧
        G (WithLp.toLp 2 ((z : Fin N → ℝ) + a))) ∧
      (∀ (i : ι) (z : Submodule.span ℤ (Set.range b)),
        ∀ᵐ t ∂volume.restrict (C i),
          P (A i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t) ∧
          G (A i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t)) ∧
      (∀ i : ι,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in C i,
          f (A i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (ε ^ k i)) * ∫⁻ x, f x) ∧
      (∀ i : ι,
        (∑' z : Submodule.span ℤ (Set.range b), ∫⁻ t in C i,
          g (A i (WithLp.toLp 2 ((z : Fin N → ℝ) + a)) t)) ≤
            2 * (ENNReal.ofReal (ε ^ N))⁻¹ *
              ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (ε ^ k i)) * ∫⁻ x, g x) := by
  intro A G b C
  have hqu := ae_memW12_cubical_face_family_of_memW12_ball hR hu k face
  have hqv := ae_memW12_cubical_face_family_of_memW12_ball hR hv k face
  have hPG : ∀ᵐ y ∂volume, P y ∧ G y := by
    filter_upwards [hP, hqu, hqv] with y hPy hyu hyv
    exact ⟨hPy, fun i U hU => ⟨hyu i U hU, hyv i U hU⟩⟩
  obtain ⟨a, ha, hvertex, hfiber, henergy, hdiscrepancy⟩ :=
    exists_grid_translate_cubical_face_pair_energy k face hε hf hg hfFinite hgFinite hPG
  refine ⟨a, ha, hvertex, ?_, ?_, ?_⟩
  · intro i z
    exact (ae_native_coordinate_face_iff_pi (face i) ((z : Fin N → ℝ) + a) ε
      (fun y => P y ∧ G y)).mpr (hfiber i z)
  · intro i
    calc
      _ = ∑' z : Submodule.span ℤ (Set.range b),
          ∫⁻ t in Set.univ.pi (fun _ : Fin (k i) => Ico (0 : ℝ) ε),
            f (WithLp.toLp 2 (((z : Fin N → ℝ) + a) +
              fun l : Fin N => ∑ j : Fin (k i), if face i j = l then t j else 0)) :=
        tsum_congr fun z => lintegral_native_coordinate_face_eq_pi (face i) ((z : Fin N → ℝ) + a) ε f
      _ ≤ _ := henergy i
  · intro i
    calc
      _ = ∑' z : Submodule.span ℤ (Set.range b),
          ∫⁻ t in Set.univ.pi (fun _ : Fin (k i) => Ico (0 : ℝ) ε),
            g (WithLp.toLp 2 (((z : Fin N → ℝ) + a) +
              fun l : Fin N => ∑ j : Fin (k i), if face i j = l then t j else 0)) :=
        tsum_congr fun z => lintegral_native_coordinate_face_eq_pi (face i) ((z : Fin N → ℝ) + a) ε g
      _ ≤ _ := hdiscrepancy i

end StratificationTheory
