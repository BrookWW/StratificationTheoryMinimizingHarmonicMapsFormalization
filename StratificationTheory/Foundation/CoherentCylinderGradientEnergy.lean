module

public import StratificationTheory.Foundation.CoherentNativeCylinderL2
public import HarmonicMaps.EnergyLemmas

/-!
# Native full-column energy of a coherent ambient family

Actual ambient L2 columns and the original real-radius coherence recover
every native cylinder column and the true Hilbert--Schmidt integral. The
ambient energy splits into the spatial and independent-time native energies
with their exact weighted radial moments.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- The complete same coherent family has native column L2, genuine HS
integrability and the exact spatial/time radial energy identity. -/
theorem native_cylinder_gradient_energy_of_real_radial_coherence {n q : ℕ}
    (hn : 0 < n) {ε R a b : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (DW : Domain (n + 1) → Gradient (n + 1) q)
    (g : unitCylinder n a b → Gradient (n + 1) q)
    (hDW : ∀ i : Fin (n + 1), MemLp (fun y => DW y i) 2
      (volume.restrict {y : Domain (n + 1) |
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b})) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let η := (Measure.volumeIoiPow (n - 1)).restrict {ρ | ε < ρ.val ∧ ρ.val < R}
    let μ : Measure (unitCylinder n a b) := Measure.euclideanHausdorffMeasure n
    (∀ᵐ r ∂volume.restrict (Ioo ε R), ∀ᵐ c ∂μ, (e c.val).2 0 ∈ Ioo a b →
      (∀ i : Fin n, DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
        r⁻¹ • g c (Fin.castAdd 1 i)) ∧
      DW (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
        g c (Fin.natAdd n (0 : Fin 1))) →
    (∀ i : Fin (n + 1), MemLp (fun c => g c i) 2 μ) ∧
      Integrable (fun c => hsNormSq (g c)) μ ∧
      (∫ y in {y : Domain (n + 1) |
        (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}, hsNormSq (DW y)) =
        (∫ ρ, (ρ.val⁻¹) ^ 2 ∂η) *
          (∫ c, hsNormSq (fun i : Fin n => g c (Fin.castAdd 1 i)) ∂μ) +
        (∫ _ρ, (1 : ℝ) ∂η) *
          ∫ c, ‖g c (Fin.natAdd n (0 : Fin 1))‖ ^ 2 ∂μ := by
  intro e η μ hcoh
  let ν : Measure (Domain (n + 1)) := volume.restrict {y : Domain (n + 1) |
    (ε < ‖(e y).1‖ ∧ ‖(e y).1‖ < R) ∧ (e y).2 0 ∈ Ioo a b}
  let S : ℝ := ∫ ρ, (ρ.val⁻¹) ^ 2 ∂η
  let T : ℝ := ∫ _ρ, (1 : ℝ) ∂η
  have hspace (i : Fin n) : MemLp (fun c => g c (Fin.castAdd 1 i)) 2 μ ∧
      (∫ y, ‖DW y (Fin.castAdd 1 i)‖ ^ 2 ∂ν) =
        S * ∫ c, ‖g c (Fin.castAdd 1 i)‖ ^ 2 ∂μ := by
    apply native_cylinder_L2_energy_of_real_radial_column_coherence hn hε hεR true
      (fun y => DW y (Fin.castAdd 1 i)) (fun c => g c (Fin.castAdd 1 i))
      (hDW (Fin.castAdd 1 i))
    filter_upwards [hcoh] with r hr
    filter_upwards [hr] with c hc
    intro hct
    exact (hc hct).1 i
  have htime : MemLp (fun c => g c (Fin.natAdd n (0 : Fin 1))) 2 μ ∧
      (∫ y, ‖DW y (Fin.natAdd n (0 : Fin 1))‖ ^ 2 ∂ν) =
        T * ∫ c, ‖g c (Fin.natAdd n (0 : Fin 1))‖ ^ 2 ∂μ := by
    have h := native_cylinder_L2_energy_of_real_radial_column_coherence hn hε hεR false
      (fun y => DW y (Fin.natAdd n (0 : Fin 1)))
      (fun c => g c (Fin.natAdd n (0 : Fin 1))) (hDW (Fin.natAdd n (0 : Fin 1)))
    simp only [Bool.false_eq_true, ↓reduceIte, one_pow, one_smul] at h
    apply h
    filter_upwards [hcoh] with r hr
    filter_upwards [hr] with c hc
    intro hct
    exact (hc hct).2
  have hg : ∀ i : Fin (n + 1), MemLp (fun c => g c i) 2 μ := by
    intro i
    refine Fin.addCases (fun j => (hspace j).1) (fun j => ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact htime.1
  have hgI (i : Fin (n + 1)) : Integrable (fun c => ‖g c i‖ ^ 2) μ :=
    (hg i).integrable_norm_pow (by norm_num)
  refine ⟨hg, integrable_finsetSum Finset.univ (fun i _ => hgI i), ?_⟩
  change (∫ y, ∑ i : Fin (n + 1), ‖DW y i‖ ^ 2 ∂ν) = _
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (hDW i).integrable_norm_pow (by norm_num)), Fin.sum_univ_add, Fin.sum_univ_one]
  change (∑ i : Fin n, ∫ y, ‖DW y (Fin.castAdd 1 i)‖ ^ 2 ∂ν) +
    (∫ y, ‖DW y (Fin.natAdd n (0 : Fin 1))‖ ^ 2 ∂ν) =
      S * (∫ c, hsNormSq (fun i : Fin n => g c (Fin.castAdd 1 i)) ∂μ) +
      T * ∫ c, ‖g c (Fin.natAdd n (0 : Fin 1))‖ ^ 2 ∂μ
  simp_rw [(hspace _).2, htime.2]
  rw [← Finset.mul_sum]
  congr 1
  congr 1
  exact (integral_finsetSum Finset.univ (fun i _ => hgI (Fin.castAdd 1 i))).symm

end StratificationTheory
