module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import HarmonicMaps.Analysis.SobolevAECongruence

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped BigOperators

namespace StratificationTheory

private theorem finite_disjoint_indicator_sum_at {α E J : Type*}
    [AddCommMonoid E] [Fintype J] [DecidableEq J]
    (U : J → Set α) (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (f : J → α → E) {x : α} (i : J) (hxi : x ∈ U i) :
    (∑ j : J, (U j).indicator (f j) x) = f i x := by
  classical
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hxi _
  · intro j _hju hji
    apply indicator_of_notMem
    intro hxj
    exact disjoint_left.mp (hdisj hji) hxj hxi
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Finite disjoint actual weak pairs supply one literal indicator-sum
gradient, full L2 data and exact additive energy. This asserts Sobolev
membership on each original open piece; seams still require weak gluing. -/
theorem finite_disjoint_sobolev_data {n q : ℕ} {J : Type*} [Fintype J]
    (Ω : Set (Domain n)) (U : J → OpenDomain n)
    (hdisj : Pairwise fun i j => Disjoint (U i).val (U j).val)
    (hsub : ∀ j, (U j).val ⊆ Ω)
    (hcover : ∀ᵐ x ∂volume.restrict Ω, ∃ j : J, x ∈ (U j).val)
    (w : Domain n → Ambient q) (A : J → Domain n → Gradient n q)
    (hW : ∀ j, MemW12 (U j) w (A j)) :
    let D : Domain n → Gradient n q := fun x => ∑ j : J, (U j).val.indicator (A j) x
    MemLp w 2 (volume.restrict Ω) ∧
      (∀ i : Fin n, MemLp (fun x => D x i) 2 volume) ∧
      (∀ j, MemW12 (U j) w D) ∧
      (∫ x in Ω, hsNormSq (D x)) = ∑ j : J, ∫ x in (U j).val, hsNormSq (A j x) := by
  classical
  intro D
  have hDAt (j : J) (x : Domain n) (hx : x ∈ (U j).val) : D x = A j x :=
    finite_disjoint_indicator_sum_at (fun j => (U j).val) hdisj A j hx
  let wsum : Domain n → Ambient q := fun x => ∑ j : J, (U j).val.indicator w x
  have hWsum : MemLp wsum 2 volume :=
    memLp_finsetSum Finset.univ fun j _ =>
      (memLp_indicator_iff_restrict (U j).property.measurableSet).mpr (hW j).2.1
  have hWeq : wsum =ᵐ[volume.restrict Ω] w := by
    filter_upwards [hcover] with x hx
    obtain ⟨j, hj⟩ := hx
    exact finite_disjoint_indicator_sum_at (fun j => (U j).val) hdisj (fun _ => w) j hj
  have hwΩ : MemLp w 2 (volume.restrict Ω) :=
    (hWsum.mono_measure Measure.restrict_le_self).ae_eq hWeq
  have hDL (i : Fin n) : MemLp (fun x => D x i) 2 volume := by
    have hsum : MemLp (fun x => ∑ j : J, (U j).val.indicator (fun y => A j y i) x) 2 volume :=
      memLp_finsetSum Finset.univ fun j _ =>
        (memLp_indicator_iff_restrict (U j).property.measurableSet).mpr ((hW j).2.2 i)
    convert hsum using 1
    funext x
    dsimp only [D]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hx : x ∈ (U j).val <;> simp [Set.indicator, hx]
  have hWpiece (j : J) : MemW12 (U j) w D := by
    apply (hW j).congr_ae (EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem (U j).property.measurableSet] with x hx
    exact (hDAt j x hx).symm
  have hEpoint : (fun x => hsNormSq (D x)) =
      fun x => ∑ j : J, (U j).val.indicator (fun y => hsNormSq (A j y)) x := by
    funext x
    by_cases hx : ∃ j : J, x ∈ (U j).val
    · obtain ⟨j, hj⟩ := hx
      rw [hDAt j x hj]
      exact (finite_disjoint_indicator_sum_at (fun j => (U j).val) hdisj
        (fun j y => hsNormSq (A j y)) j hj).symm
    · have hxall : ∀ j : J, x ∉ (U j).val := by simpa only [not_exists] using hx
      simp only [D, indicator_of_notMem (hxall _), Finset.sum_const_zero, hsNormSq,
        Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hEindicator (j : J) : Integrable ((U j).val.indicator (fun y => hsNormSq (A j y))) volume :=
    (integrable_indicator_iff (U j).property.measurableSet).mpr (hW j).integrable_hsNormSq
  refine ⟨hwΩ, hDL, hWpiece, ?_⟩
  rw [hEpoint, integral_finsetSum Finset.univ
    (fun j _ => (hEindicator j).mono_measure Measure.restrict_le_self)]
  apply Finset.sum_congr rfl
  intro j _
  rw [setIntegral_indicator (U j).property.measurableSet, inter_eq_right.mpr (hsub j)]

end StratificationTheory
