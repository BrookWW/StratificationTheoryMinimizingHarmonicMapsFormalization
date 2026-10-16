module

public import StratificationTheory.Interpolation.CylinderAnnularTransport
public import StratificationTheory.Foundation.AnnularGradientEnergy

/-!
# Coherent cylinder columns under annular radial averaging

Reciprocal radial spatial columns and constant temporal columns give an exact
formula for the actual averaged annular field. Its Hilbert--Schmidt square is
then bounded with the distinct spatial and temporal scale factors. These are
conditional column identities; weak membership and ray coherence are supplied
by the caller.
-/

public section
open HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators
namespace StratificationTheory

theorem annularAveragedColumns_param_of_coherent_columns {n q : ℕ}
    {s t : ℝ} (hs : 0 < s) (ht : -1 < t)
    (β : ℝ → ℝ) (P : Measure (Ioi (0 : ℝ)))
    (Dw : Domain (n + 1) → Gradient (n + 1) q)
    (θ : sphere (0 : Domain n) 1) (A : Gradient n q) (B : Ambient q)
    (hmass : (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) = 1)
    (hD : ∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let Z := e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)
      (∀ i : Fin n, Dw Z (Fin.castAdd 1 i) = ρ.val⁻¹ • A i) ∧
        Dw Z (Fin.natAdd n (0 : Fin 1)) = B) :
    annularAveragedColumns s β P Dw ((s * (1 + t)) • θ.val) =
      fun i => (s * (1 + t))⁻¹ • tangentialColumns θ A i +
        (s⁻¹ * θ.val i) • B := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let Z := fun ρ : Ioi (0 : ℝ) =>
    e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)
  have hsp (i : Fin n) :
      (fun ρ : Ioi (0 : ℝ) => β ρ.val • ρ.val •
        (Dw (Z ρ) (Fin.castAdd 1 i) - θ.val i •
          ∑ j : Fin n, θ.val j • Dw (Z ρ) (Fin.castAdd 1 j))) =ᵐ[P]
      (fun ρ => β ρ.val • tangentialColumns θ A i) := by
    filter_upwards [hD] with ρ hρ
    change (∀ i : Fin n, Dw (Z ρ) (Fin.castAdd 1 i) = ρ.val⁻¹ • A i) ∧
      Dw (Z ρ) (Fin.natAdd n (0 : Fin 1)) = B at hρ
    simp_rw [hρ.1]
    simp_rw [smul_comm (θ.val _) (ρ.val⁻¹) (A _)]
    rw [← Finset.smul_sum, smul_comm (θ.val i) (ρ.val⁻¹),
      ← smul_sub]
    simp only [smul_smul, mul_inv_cancel₀ (show ρ.val ≠ 0 from ne_of_gt ρ.property), mul_one]
    rfl
  have htm : (fun ρ : Ioi (0 : ℝ) => β ρ.val •
      Dw (Z ρ) (Fin.natAdd n (0 : Fin 1))) =ᵐ[P] (fun ρ => β ρ.val • B) := by
    filter_upwards [hD] with ρ hρ
    exact congrArg (fun x : Ambient q => β ρ.val • x) hρ.2
  funext i
  rw [annularAveragedColumns_param hs ht β P Dw θ i,
    integral_congr_ae (hsp i), integral_congr_ae htm,
    integral_smul_const, integral_smul_const, hmass, one_smul, one_smul]

theorem hsNormSq_annularAveragedColumns_param_le {n q : ℕ}
    {s t : ℝ} (hs : 0 < s) (ht : -1 < t)
    (β : ℝ → ℝ) (P : Measure (Ioi (0 : ℝ)))
    (Dw : Domain (n + 1) → Gradient (n + 1) q)
    (θ : sphere (0 : Domain n) 1) (A : Gradient n q) (B : Ambient q)
    (hmass : (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) = 1)
    (hD : ∀ᵐ ρ : Ioi (0 : ℝ) ∂P,
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
      let Z := e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)
      (∀ i : Fin n, Dw Z (Fin.castAdd 1 i) = ρ.val⁻¹ • A i) ∧
        Dw Z (Fin.natAdd n (0 : Fin 1)) = B) :
    hsNormSq (annularAveragedColumns s β P Dw ((s * (1 + t)) • θ.val)) ≤
      ((s * (1 + t))⁻¹) ^ 2 * hsNormSq A + (s⁻¹) ^ 2 * ‖B‖ ^ 2 := by
  rw [annularAveragedColumns_param_of_coherent_columns hs ht β P Dw θ A B hmass hD]
  simpa only [mul_smul] using
    hsNormSq_annular_columns_le θ A B (s * (1 + t))⁻¹ s⁻¹

end StratificationTheory
