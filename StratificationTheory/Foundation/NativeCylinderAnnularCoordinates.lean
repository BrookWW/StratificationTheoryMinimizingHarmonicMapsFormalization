module

public import StratificationTheory.Foundation.NativeCylinderAECoordinates
public import HarmonicMaps.EnergyLemmas

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal BigOperators
namespace StratificationTheory

/-- Original native cylinder columns determine actual sphere-time spatial
and temporal fields with the same total energy and normalized-collar coherence. -/
theorem exists_native_cylinder_annular_coordinates {n q : ℕ} (hn : 0 < n)
    {a b δ : ℝ} (hδsmall : δ < 1 / 2)
    (Dw : Domain (n + 1) → Gradient (n + 1) q)
    (g : unitCylinder n a b → Gradient (n + 1) q)
    (hg : ∀ i : Fin (n + 1), MemLp (fun c => g c i) 2
      (Measure.euclideanHausdorffMeasure n : Measure (unitCylinder n a b))) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let μ := σ.prod (volume.restrict (Ioo a b))
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    (∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      ∀ᵐ c : unitCylinder n a b ∂Measure.euclideanHausdorffMeasure n,
        (e c.val).2 0 ∈ Ioo a b →
          (∀ i : Fin n, Dw (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.castAdd 1 i) =
            r⁻¹ • g c (Fin.castAdd 1 i)) ∧
          Dw (e.symm (r • (e c.val).1, (e c.val).2)) (Fin.natAdd n (0 : Fin 1)) =
            g c (Fin.natAdd n (0 : Fin 1))) →
    ∃ (A : sphere (0 : Domain n) 1 × ℝ → Gradient n q)
      (B : sphere (0 : Domain n) 1 × ℝ → Ambient q),
      (∀ (θ : sphere (0 : Domain n) 1) (τ : Icc a b),
        let c : unitCylinder n a b :=
          ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) τ.val), unitCylinder_param_mem θ τ⟩
        (∀ i : Fin n, A (θ, τ.val) i = g c (Fin.castAdd 1 i)) ∧
          B (θ, τ.val) = g c (Fin.natAdd n (0 : Fin 1))) ∧
      (∀ i : Fin n, MemLp (fun p => A p i) 2 μ) ∧ MemLp B 2 μ ∧
      Integrable (fun p => hsNormSq (A p) + ‖B p‖ ^ 2) μ ∧
      (∫ p, hsNormSq (A p) + ‖B p‖ ^ 2 ∂μ) =
        ∫ c : unitCylinder n a b, hsNormSq (g c) ∂Measure.euclideanHausdorffMeasure n ∧
      ∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
        ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
          (∀ i : Fin n, Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
            (Fin.castAdd 1 i) = ρ.val⁻¹ • A p i) ∧
          Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
            (Fin.natAdd n (0 : Fin 1)) = B p := by
  classical
  intro e σ μ η P hCoherence
  let c := fun z : sphere (0 : Domain n) 1 × Icc a b =>
    (⟨e.symm (z.1.val, EuclideanSpace.single (0 : Fin 1) z.2.val),
      unitCylinder_param_mem z.1 z.2⟩ : unitCylinder n a b)
  let G : sphere (0 : Domain n) 1 × ℝ → Gradient (n + 1) q := fun p =>
    if ht : p.2 ∈ Icc a b then g (c (p.1, ⟨p.2, ht⟩)) else 0
  let A := fun (p : sphere (0 : Domain n) 1 × ℝ) (i : Fin n) => G p (Fin.castAdd 1 i)
  let B := fun p : sphere (0 : Domain n) 1 × ℝ => G p (Fin.natAdd n (0 : Fin 1))
  have hG (θ : sphere (0 : Domain n) 1) (τ : Icc a b) : G (θ, τ.val) = g (c (θ, τ)) := by
    simp only [G, dif_pos τ.property]
  have hCoords (θ : sphere (0 : Domain n) 1) (τ : Icc a b) :
      (∀ i : Fin n, A (θ, τ.val) i = g (c (θ, τ)) (Fin.castAdd 1 i)) ∧
        B (θ, τ.val) = g (c (θ, τ)) (Fin.natAdd n (0 : Fin 1)) := by
    exact ⟨fun i => congrFun (hG θ τ) (Fin.castAdd 1 i), congrFun (hG θ τ) (Fin.natAdd n (0 : Fin 1))⟩
  have hA (i : Fin n) : MemLp (fun p => A p i) 2 μ :=
    memLp_cylinder_param_coordinates hn (fun c => g c (Fin.castAdd 1 i)) (fun p => A p i)
      (hg _) (fun θ τ => (hCoords θ τ).1 i)
  have hB : MemLp B 2 μ :=
    memLp_cylinder_param_coordinates hn (fun c => g c (Fin.natAdd n (0 : Fin 1))) B
      (hg _) (fun θ τ => (hCoords θ τ).2)
  have hIntA : Integrable (fun p => hsNormSq (A p)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hA i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hIntB : Integrable (fun p => ‖B p‖ ^ 2) μ := hB.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hEnergy : (∫ p, hsNormSq (A p) + ‖B p‖ ^ 2 ∂μ) =
      ∫ z : unitCylinder n a b, hsNormSq (g z) ∂Measure.euclideanHausdorffMeasure n := by
    apply integral_cylinder_param_coordinates hn (fun z => hsNormSq (g z))
      (fun p => hsNormSq (A p) + ‖B p‖ ^ 2)
    intro θ τ
    change (∑ i : Fin n, ‖A (θ, τ.val) i‖ ^ 2) + ‖B (θ, τ.val)‖ ^ 2 = _
    simp only [(hCoords θ τ).1, (hCoords θ τ).2, hsNormSq,
      Fin.sum_univ_add, Fin.sum_univ_one]
    rfl
  refine ⟨A, B, hCoords, hA, hB, hIntA.add hIntB, hEnergy, ?_⟩
  have hP := ae_normalized_spatial_collar_of_ae_real_collar (n := n) hδsmall _ hCoherence
  filter_upwards [hP] with ρ hρ
  have hParam : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ,
      p.2 ∈ Ioo a b →
        (∀ i : Fin n, Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
          (Fin.castAdd 1 i) = ρ.val⁻¹ • A p i) ∧
        Dw (e.symm (ρ.val • p.1.val, EuclideanSpace.single (0 : Fin 1) p.2))
          (Fin.natAdd n (0 : Fin 1)) = B p := by
    apply ae_cylinder_param_coordinates hn _ _ ?_ hρ
    intro θ τ
    simp only [(hCoords θ τ).1, (hCoords θ τ).2, c, e,
      ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true]
  have hTime : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ, p.2 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hParam, hTime] with p hp ht
  exact hp ht

end StratificationTheory
