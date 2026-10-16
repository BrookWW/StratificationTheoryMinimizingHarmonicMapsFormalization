module

public import StratificationTheory.Foundation.AnnularCylinderL2
public import HarmonicMaps.EnergyLemmas

/-!
# Column energy under annular coordinate transport

The upper bound on the annular Jacobian compares the actual sum of squared
column norms with its unweighted sphere-time pullback. Each original column
also retains its L2 membership. The statement applies to column fields and
does not prescribe a weak gradient.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal BigOperators
namespace StratificationTheory

theorem annular_column_energy_of_cylinder_pullback {n q : ℕ} (hn : 0 < n)
    {s a b : ℝ} (hs : 0 < s) (ha : -1 < a) (hab : a < b)
    (D : Domain n → Gradient n q)
    (hD : ∀ i : Fin n, MemLp
      (fun p : sphere (0 : Domain n) 1 × ℝ => D ((s * (1 + p.2)) • p.1.val) i) 2
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)).prod
        (volume.restrict (Ioo a b)))) :
    let A := {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}
    let μ := (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Ioo a b))
    (∀ i : Fin n, MemLp (fun x => D x i) 2 (volume.restrict A)) ∧
    Integrable (fun x => hsNormSq (D x)) (volume.restrict A) ∧
    (∫ x in A, hsNormSq (D x)) ≤
      (s * (s * (1 + b)) ^ (n - 1)) *
        ∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (D ((s * (1 + p.2)) • p.1.val)) ∂μ := by
  intro A μ
  have htransfer (i : Fin n) :=
    memLp_two_annulus_of_cylinder_pullback hn hs ha hab (fun x => D x i) (hD i)
  have hInt (i : Fin n) : Integrable (fun x => ‖D x i‖ ^ 2) (volume.restrict A) :=
    (htransfer i).1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hIntP (i : Fin n) : Integrable
      (fun p : sphere (0 : Domain n) 1 × ℝ => ‖D ((s * (1 + p.2)) • p.1.val) i‖ ^ 2) μ :=
    (hD i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  refine ⟨fun i => (htransfer i).1, ?_, ?_⟩
  · exact integrable_finsetSum Finset.univ fun i _ => hInt i
  · simp only [hsNormSq]
    rw [integral_finsetSum _ (fun i _ => hInt i),
      integral_finsetSum _ (fun i _ => hIntP i), Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (htransfer i).2

end StratificationTheory
