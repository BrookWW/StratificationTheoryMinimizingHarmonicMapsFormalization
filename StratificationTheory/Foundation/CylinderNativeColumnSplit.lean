module

public import StratificationTheory.Foundation.CylinderNativePullback
public import HarmonicMaps.EnergyLemmas

/-!
# Native cylinder column splitting

A field with actual native L2 columns determines spatial and temporal L2
pieces from its interior almost-everywhere column formula. Their squared
norm integral equals the native Hilbert--Schmidt integral of the same field.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal BigOperators
namespace StratificationTheory

theorem native_cylinder_split_columns_l2_and_energy {n q : ℕ} (hn : 0 < n)
    {a b : ℝ} (D : Domain (n + 1) → Gradient (n + 1) q)
    (A : sphere (0 : Domain n) 1 × ℝ → Gradient n q)
    (B : sphere (0 : Domain n) 1 × ℝ → Ambient q)
    (hD : ∀ i : Fin (n + 1), MemLp (fun c : unitCylinder n a b => D c.val i) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b)))
    (hunit : ∀ᵐ θ : sphere (0 : Domain n) 1 ∂Measure.euclideanHausdorffMeasure (n - 1),
      ∀ t ∈ Ioo a b,
        D ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (θ.val, EuclideanSpace.single (0 : Fin 1) t)) =
          Fin.addCases (A (θ, t)) (fun _ : Fin 1 => B (θ, t))) :
    let μ := (Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Ioo a b))
    (∀ i : Fin n, MemLp (fun p => A p i) 2 μ) ∧ MemLp B 2 μ ∧
      (∫ p : sphere (0 : Domain n) 1 × ℝ, hsNormSq (A p) + ‖B p‖ ^ 2 ∂μ) =
        ∫ c : unitCylinder n a b, hsNormSq (D c.val) ∂Measure.euclideanHausdorffMeasure n := by
  intro μ
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  have htime : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ, p.2 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  have hθ := (Measure.quasiMeasurePreserving_fst
    (μ := (Measure.euclideanHausdorffMeasure (n - 1) : Measure (sphere (0 : Domain n) 1)))
    (ν := volume.restrict (Ioo a b))).ae hunit
  have hEq : (fun p : sphere (0 : Domain n) 1 × ℝ =>
      D (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))) =ᵐ[μ]
      (fun p => Fin.addCases (A p) (fun _ : Fin 1 => B p)) := by
    filter_upwards [hθ, htime] with p hp ht
    exact hp p.2 ht
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hL := memLp_two_cylinder_pullback_of_native hn (fun y => D y (Fin.castAdd 1 i)) (hD _)
    apply hL.ae_eq
    filter_upwards [hEq] with p hp
    simpa only [Fin.addCases_left] using congrFun hp (Fin.castAdd 1 i)
  · have hL := memLp_two_cylinder_pullback_of_native hn
      (fun y => D y (Fin.natAdd n (0 : Fin 1))) (hD _)
    apply hL.ae_eq
    filter_upwards [hEq] with p hp
    simpa only [Fin.addCases_right] using congrFun hp (Fin.natAdd n (0 : Fin 1))
  · calc
      _ = ∫ p : sphere (0 : Domain n) 1 × ℝ,
          hsNormSq (D (e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hEq] with p hp
        rw [hp]
        simp only [hsNormSq, Fin.sum_univ_add, Fin.addCases_left,
          Fin.addCases_right, Fin.sum_univ_one]
      _ = _ := integral_cylinder_pullback_eq_native hn (fun y => hsNormSq (D y))

end StratificationTheory
