module

public import StratificationTheory.Foundation.FiniteDisjointSobolevData
public import HarmonicMaps.Analysis.SobolevAECongruence

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators

namespace StratificationTheory

private theorem indicator_sum_at_original_cell {n : ℕ} {I E : Type*} [Fintype I] [AddCommMonoid E]
    (C : I → OpenDomain n) (hdisj : Pairwise fun i j => Disjoint (C i).val (C j).val)
    (f : I → Domain n → E) (j : I) (x : Domain n) (hx : x ∈ (C j).val) :
      (∑ k : I, (C k).val.indicator (f k) x) = f j x := by
    classical
    rw [Finset.sum_eq_single j]
    · exact indicator_of_mem hx _
    · intro k _hku hkj
      apply indicator_of_notMem
      intro hxk
      exact disjoint_left.mp (hdisj hkj) hxk hx
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))

/-- Original maps and columns on a finite disjoint open mesh give their
literal common indicator-sum fields, full native L2 data, original cell
graphs, exact additive energy and original a.e. value constraints. -/
theorem finite_piecewise_sobolev_fields {n q : ℕ} {I : Type*} [Fintype I]
    (Ω : Set (Domain n)) (C : I → OpenDomain n)
    (hdisj : Pairwise fun i j => Disjoint (C i).val (C j).val)
    (hsub : ∀ j, (C j).val ⊆ Ω)
    (hcover : ∀ᵐ x ∂volume.restrict Ω, ∃ j : I, x ∈ (C j).val)
    (u : I → Domain n → Ambient q) (A : I → Domain n → Gradient n q)
    (hu : ∀ j, MemW12 (C j) (u j) (A j)) :
    let W : Domain n → Ambient q := fun x => ∑ j : I, (C j).val.indicator (u j) x
    let D : Domain n → Gradient n q := fun x => ∑ j : I, (C j).val.indicator (A j) x
    MemLp W 2 (volume.restrict Ω) ∧
      (∀ i : Fin n, MemLp (fun x => D x i) 2 volume) ∧
      (∀ j, MemW12 (C j) W D) ∧
      (∀ j x, x ∈ (C j).val → W x = u j x ∧ D x = A j x) ∧
      (∫ x in Ω, hsNormSq (D x)) = ∑ j : I, ∫ x in (C j).val, hsNormSq (A j x) ∧
      ∀ P : Ambient q → Prop, (∀ j, ∀ᵐ x ∂volume.restrict (C j).val, P (u j x)) →
        ∀ᵐ x ∂volume.restrict Ω, P (W x) := by
  classical
  intro W D
  have hPoint (j : I) (x : Domain n) (hx : x ∈ (C j).val) : W x = u j x ∧ D x = A j x :=
    ⟨indicator_sum_at_original_cell C hdisj u j x hx, indicator_sum_at_original_cell C hdisj A j x hx⟩
  have hEach (j : I) : MemW12 (C j) W (A j) := by
    apply (hu j).congr_ae _ (EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem (C j).property.measurableSet] with x hx
    exact (hPoint j x hx).1.symm
  have hData := finite_disjoint_sobolev_data Ω C hdisj hsub hcover W A hEach
  refine ⟨hData.1, hData.2.1, hData.2.2.1, hPoint, hData.2.2.2, ?_⟩
  intro P hP
  have hEachP (j : I) : ∀ᵐ x : Domain n ∂volume, x ∈ (C j).val → P (u j x) :=
    (ae_restrict_iff' (C j).property.measurableSet).mp (hP j)
  filter_upwards [hcover, ae_restrict_of_ae (ae_all_iff.mpr hEachP)] with x hx hPx
  obtain ⟨j, hj⟩ := hx
  rw [(hPoint j x hj).1]
  exact hPx j hj

end StratificationTheory
