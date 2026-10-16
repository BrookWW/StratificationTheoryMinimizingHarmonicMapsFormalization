module

public import StratificationTheory.Foundation.RawVertexUnitChord
public import StratificationTheory.Interpolation.CoordinateEdgeUnitMaps
public import StratificationTheory.Foundation.CubicalConeGeometry

/-!
# The native weak graph and canonical trace of a vertex chord

One literal chord has its actual constant weak column and one continuous
native zero-dimensional slice curve, with the two original vertex classes.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- A raw coordinate connector endpoint is the same global vertex chord,
independently of its coordinate direction and physical edge length. -/
theorem coordinateEdgeRawUnitChord_eq_rawVertexUnitChord {n q : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) {ε : ℝ} (hε : 0 < ε)
    (u : Fin 2 → Domain (n + 1) → Ambient q) (y : Domain (n + 1)) (side : ℝ) :
    coordinateEdgeRawUnitChord p ε u y side =
      rawVertexUnitChord u (y + side • EuclideanSpace.single (p (Fin.natAdd n (0 : Fin 1))) (1 : ℝ)) := by
  funext x
  have hc : (ε / 2 + (ε / 2) * x 0) / ε = (x 0 + 1) / 2 := by
    field_simp [hε.ne']
    ring
  simp only [coordinateEdgeRawUnitChord, rawVertexUnitChord, hc]

/-- The literal vertex chord is a genuine native finite weak graph. -/
theorem rawVertexUnitChord_memW12 {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m) :
    let B : OpenDomain 1 :=
      ⟨⋂ i : Fin 1, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    MemW12 B (rawVertexUnitChord u y) (rawVertexUnitGradient u y) := by
  intro B
  let F : ℝ → Ambient q := fun t =>
    (1 - (t + 1) / 2) • u 0 y + ((t + 1) / 2) • u 1 y
  let g : ℝ → Ambient q := fun _ => (1 / 2 : ℝ) • (u 1 y - u 0 y)
  have hFcont : Continuous F :=
    ((continuous_const.sub ((continuous_id.add continuous_const).div_const 2)).smul continuous_const).add
      (((continuous_id.add continuous_const).div_const 2).smul continuous_const)
  have hF : MemLp F 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    apply MemLp.of_bound hFcont.aestronglyMeasurable (‖u 0 y‖ + ‖u 1 y‖)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ha : 0 ≤ (t + 1) / 2 := by linarith [ht.1]
    have hb : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
    calc
      ‖F t‖ ≤ ‖(1 - (t + 1) / 2) • u 0 y‖ + ‖((t + 1) / 2) • u 1 y‖ := norm_add_le _ _
      _ = (1 - (t + 1) / 2) * ‖u 0 y‖ + ((t + 1) / 2) * ‖u 1 y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg ha]
      _ ≤ ‖u 0 y‖ + ‖u 1 y‖ := by
        nlinarith [norm_nonneg (u 0 y), norm_nonneg (u 1 y)]
  have hg : MemLp g 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := memLp_const _
  have hinc : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      F t - F s = ∫ z in s..t, g z := by
    intro s _ t _
    simp only [F, g, intervalIntegral.integral_const, smul_smul]
    module
  have hweak := memW12_domainOne_of_integral_increments (by norm_num : (-1 : ℝ) < 1)
    hF hg (Filter.EventuallyEq.rfl) hinc
  have hB : B = ⟨{x : Domain 1 | x 0 ∈ Ioo (-1 : ℝ) 1},
      isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous⟩ := by
    apply Subtype.ext
    change (⋂ i : Fin 1, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1) =
      {x : Domain 1 | x 0 ∈ Ioo (-1 : ℝ) 1}
    ext x
    simp only [mem_iInter, mem_preimage, mem_setOf_eq]
    constructor
    · intro h
      exact h 0
    · intro h i
      change x i ∈ Ioo (-1 : ℝ) 1
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using h
  rw [hB]
  exact hweak

/-- All zero-dimensional slices of the chord form one continuous L2 curve,
whose two endpoint classes are the original raw vertex values. -/
theorem exists_rawVertexUnitChord_trace {m q : ℕ}
    (u : Fin 2 → Domain m → Ambient q) (y : Domain m) :
    let C : Set (Domain 0) := ⋂ i : Fin 0, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 0) (m := 1)
    ∃ K : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict C)),
      (∀ t : Icc (-1 : ℝ) 1, ∃ hs : MemLp
        (fun x : Domain 0 => rawVertexUnitChord u y (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
          2 (volume.restrict C), K t = hs.toLp
        (fun x : Domain 0 => rawVertexUnitChord u y (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
      ∀ side : Bool, ∃ hs : MemLp (fun _ : Domain 0 => u (if side then 1 else 0) y)
          2 (volume.restrict C),
        K ⟨if side then 1 else -1, by cases side <;> norm_num, by cases side <;> norm_num⟩ =
          hs.toLp (fun _ : Domain 0 => u (if side then 1 else 0) y) := by
  intro C e
  letI : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.mpr (volume_unit_coordinate_face_ne_top 0)
  have h₀ : MemLp (fun _ : Domain 0 => u 0 y) 2 (volume.restrict C) := memLp_const _
  have h₁ : MemLp (fun _ : Domain 0 => u 1 y) 2 (volume.restrict C) := memLp_const _
  obtain ⟨K, hformula, hraw, hleft, hright, _⟩ :=
    affine_pair_continuous_lp_trace (volume.restrict C) (by norm_num : (-1 : ℝ) < 1)
      h₀ h₁ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
  have hpoint (x : Domain 0) (t : ℝ) :
      e.symm (x, EuclideanSpace.single (0 : Fin 1) t) 0 = t := rfl
  refine ⟨K, ?_, ?_⟩
  · intro t
    simpa only [rawVertexUnitChord, hpoint, sub_neg_eq_add, show (1 : ℝ) + 1 = 2 by norm_num] using hraw t
  · intro side
    cases side
    · exact ⟨h₀, hleft⟩
    · exact ⟨h₁, hright⟩

end StratificationTheory
