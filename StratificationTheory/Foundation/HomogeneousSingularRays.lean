module

public import StratificationTheory.Foundation.RegularPointAffine
public import StratificationTheory.Frozen.SingularSetNull

/-!
# Singular rays of homogeneous maps

Almost-everywhere invariance under positive dilation preserves the literal
regular and singular loci. A nonzero singular point therefore produces an
actual segment of positive native one-dimensional Hausdorff measure in the
ambient singular set. In dimension three this contradicts the Hausdorff
nullity theorem for locally energy-minimizing maps.
-/

public section

open HarmonicMaps MeasureTheory MeasureTheory.Measure Set

namespace StratificationTheory

/-- Positive dilation preserves regularity for an a.e. homogeneous global map. -/
theorem isRegularPoint_ae_homogeneous_smul_iff {n q : ℕ}
    {u : Domain n → Ambient q}
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (l : ℝ) (hl : 0 < l) (x : Domain n) :
    IsRegularPoint ⟨univ, isOpen_univ⟩ u ⟨l • x, mem_univ _⟩ ↔
      IsRegularPoint ⟨univ, isOpen_univ⟩ u ⟨x, mem_univ _⟩ := by
  have hdomain : (univ : Set (Domain n)) =
      (fun z => (0 : Domain n) + l • z) ⁻¹' univ := by
    ext z
    simp only [mem_univ, mem_preimage]
  have haffine := isRegularPoint_affine_preimage_iff
    ⟨univ, isOpen_univ⟩ ⟨univ, isOpen_univ⟩ u 0 ⟨l, hl⟩ hdomain
    ⟨x, mem_univ _⟩
  have hae := isRegularPoint_congr_ae
    (Ω := ⟨univ, isOpen_univ⟩) (ae_restrict_of_ae (hhom l hl)) ⟨x, mem_univ _⟩
  simp only [zero_add] at haffine
  exact haffine.symm.trans hae

/-- The singular-point predicate is invariant under the same positive dilation. -/
theorem mem_singularSet_ae_homogeneous_smul_iff {n q : ℕ}
    {u : Domain n → Ambient q}
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (l : ℝ) (hl : 0 < l) (x : Domain n) :
    (⟨l • x, mem_univ _⟩ : (univ : Set (Domain n))) ∈
      singularSet ⟨univ, isOpen_univ⟩ u ↔
      (⟨x, mem_univ _⟩ : (univ : Set (Domain n))) ∈
        singularSet ⟨univ, isOpen_univ⟩ u :=
  not_congr (isRegularPoint_ae_homogeneous_smul_iff hhom l hl x)

/-- A singular point generates a genuine segment in the ambient singular locus. -/
theorem segment_subset_singularSet_image_of_ae_homogeneous {n q : ℕ}
    {u : Domain n → Ambient q}
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (x : Domain n)
    (hx : (⟨x, mem_univ _⟩ : (univ : Set (Domain n))) ∈
      singularSet ⟨univ, isOpen_univ⟩ u) :
    segment ℝ x ((2 : ℝ) • x) ⊆
      Subtype.val '' singularSet ⟨univ, isOpen_univ⟩ u := by
  rintro y ⟨a, b, ha, hb, hab, hxy⟩
  have hl : 0 < a + b * 2 := by linarith only [ha, hb, hab]
  have hy : y = (a + b * 2) • x := by
    rw [← hxy, smul_smul, ← add_smul]
  refine ⟨⟨y, mem_univ _⟩, ?_, rfl⟩
  rw [hy]
  exact (mem_singularSet_ae_homogeneous_smul_iff hhom (a + b * 2) hl x).mpr hx

/-- A ray segment starting at a nonzero point has positive native Hausdorff measure. -/
theorem hausdorffMeasure_ray_segment_pos {n : ℕ} (x : Domain n) (hx : x ≠ 0) :
    0 < (μH[1] : Measure (Domain n)) (segment ℝ x ((2 : ℝ) • x)) := by
  rw [hausdorffMeasure_segment]
  apply edist_pos.mpr
  intro heq
  rw [two_smul] at heq
  have hzero : (0 : Domain n) = x :=
    add_left_cancel (by simpa only [add_zero] using heq)
  exact hx hzero.symm

/-- Every nonzero point is regular for a global homogeneous three-dimensional minimizer. -/
theorem isRegularPoint_of_ae_homogeneous_minimizer_three {q : ℕ}
    {N : CompactSmoothEmbeddedTarget q}
    {u : Domain 3 → Ambient q} {Du : Domain 3 → Gradient 3 q}
    (hmin : IsLocallyEnergyMinimizing N ⟨univ, isOpen_univ⟩ u Du)
    (hu : MemW12Loc ⟨univ, isOpen_univ⟩ u Du)
    (hN : TakesValuesIn N ⟨univ, isOpen_univ⟩ u)
    (hhom : ∀ l : ℝ, 0 < l → (fun x => u (l • x)) =ᵐ[volume] u)
    (x : Domain 3) (hx : x ≠ 0) :
    IsRegularPoint ⟨univ, isOpen_univ⟩ u ⟨x, mem_univ _⟩ := by
  by_contra hsing
  have hsubset := segment_subset_singularSet_image_of_ae_homogeneous hhom x hsing
  have hnull : (μH[1] : Measure (Domain 3))
      (Subtype.val '' singularSet ⟨univ, isOpen_univ⟩ u) = 0 := by
    simpa only [Nat.cast_ofNat, show (3 : ℝ) - 2 = 1 by norm_num] using
      singularSet_hausdorffMeasure_zero (by norm_num : 2 ≤ 3) hmin hu hN
  exact (hausdorffMeasure_ray_segment_pos x hx).ne'
    (measure_mono_null hsubset hnull)

end StratificationTheory
