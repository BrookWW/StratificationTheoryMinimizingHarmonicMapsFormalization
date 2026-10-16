module

public import StratificationTheory.Foundation.SpatialConeAnnularBounds
public import StratificationTheory.Foundation.CubicalConeRadialFormula
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# The actual positive spatial annular cone weak pair

Original face-times-time data produce the same maximum-coordinate radial
map and its actual chain columns on the spatial annular cone. The native
energy constant depends only on dimension; interpolation time is unchanged.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StratificationTheory

theorem exists_positive_spatial_annular_cone_constant (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (q : ℕ) (ε : ℝ), ε ≤ 1 →
    ∀ (G : Domain (n + 1) × ℝ → Ambient q)
      (Dw : Domain (n + 1) → Gradient (n + 1) q),
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let S := ⋂ i : Fin n, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
    let B : OpenDomain n := ⟨S,isOpen_iInter_of_finite (fun i : Fin n =>
      isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)⟩
    let Ω : OpenDomain (n + 1) :=
      ⟨{z | (e z).1 ∈ S ∧ (e z).2 0 ∈ Ioo (0 : ℝ) ε},
        (B.property.preimage (continuous_fst.comp e.continuous)).inter
          (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
            (continuous_snd.comp e.continuous)))⟩
    let T : Domain (n + 1 + 1) → ℝ := fun y => (e (E y).1).2 0
    let F : Domain (n + 1 + 1) → Domain (n + 1) := fun y =>
      e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2)
    let w : Domain (n + 1) → Ambient q := fun z =>
      G (e.symm ((e z).1,EuclideanSpace.single (0 : Fin 1) 1),(e z).2 0)
    let D : Domain (n + 1 + 1) → Gradient (n + 1 + 1) q := fun y i =>
      ∑ j : Fin (n + 1), (fderiv ℝ F y (EuclideanSpace.single i 1)) j • Dw (F y) j
    let V : OpenDomain (n + 1 + 1) :=
      ⟨({y | T y ∈ Ioo (0 : ℝ) 1 ∧ ∀ i : Fin n, |(e (E y).1).1 i| < T y} ∩
          {y | ‖(E y).1‖ ∈ Ioo (1 / 4 : ℝ) 1}) ∩ {y | (E y).2 0 ∈ Ioo (0 : ℝ) ε},
        isOpen_positive_spatial_annular_cone n ε⟩
    let W : Domain (n + 1 + 1) → Ambient q := fun y =>
      G (‖WithLp.ofLp (E y).1‖⁻¹ • (E y).1,(E y).2 0)
    MemW12 Ω w Dw →
      MemW12 V W D ∧
      (∫ y in V.val,hsNormSq (D y)) ≤ Cn * ∫ z in Ω.val,hsNormSq (Dw z) ∧
      ∀ P : Ambient q → Prop, (∀ᵐ z ∂volume.restrict Ω.val,P (w z)) →
        ∀ᵐ y ∂volume.restrict V.val,P (W y) := by
  let ρ : ℝ := (4 * ((n + 1 : ℕ) : ℝ))⁻¹
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  obtain ⟨hc,L,hL,hTransport⟩ := exists_spatial_cone_time_sobolev_transport n hρ 2
  let c : ℝ≥0∞ := ∫⁻ r in Ioo ρ 2,ENNReal.ofReal (r ^ n)
  let A : ℝ := ((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * L ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A * c.toReal + 1,by positivity,?_⟩
  intro q ε hε G Dw e E S B Ω T F w D V W hw
  obtain ⟨U,hU,hData⟩ := hTransport B 0 ε
  have hWU : MemW12 U (w ∘ F) D := (hData q w Dw hw).1
  have hEnergyU : dirichletEnergy D U.val ≤
      ENNReal.ofReal A * c * dirichletEnergy Dw Ω.val := (hData q w Dw hw).2.1
  have hSub : V.val ⊆ U.val := by
    intro y hy
    have h := spatial_cone_annular_transport_carrier hε y hy.1.1.1.1 hy.1.1.2 hy.1.2 hy.2
    rw [hU]
    exact ⟨⟨h.1,⟨h.2.1,h.2.2.1⟩⟩,mem_ball_zero_iff.mpr h.2.2.2⟩
  have hRaw (y : Domain (n + 1 + 1)) (hy : y ∈ V.val) : (w ∘ F) y = W y := by
    have hRad := (positive_cube_cone_radial_retraction (E y).1 hy.1.1.1.1 hy.1.1.2).2
    change G (e.symm ((e (F y)).1,EuclideanSpace.single (0 : Fin 1) 1),(e (F y)).2 0) = _
    change G (e.symm ((e (e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2))).1,
      EuclideanSpace.single (0 : Fin 1) 1),
        (e (e.symm ((T y)⁻¹ • (e (E y).1).1,(E y).2))).2 0) = _
    rw [e.apply_symm_apply,← hRad]
  have hWeak : MemW12 V (w ∘ F) D :=
    ⟨hWU.1.mono hSub,hWU.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i => (hWU.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  have hW : MemW12 V W D := hWeak.congr_ae
    (by filter_upwards [ae_restrict_mem V.property.measurableSet] with y hy; exact hRaw y hy)
    (EventuallyEq.refl _ _)
  have hEnergy : dirichletEnergy D V.val ≤ ENNReal.ofReal A * c * dirichletEnergy Dw Ω.val :=
    (show dirichletEnergy D V.val ≤ dirichletEnergy D U.val from lintegral_mono_set hSub).trans hEnergyU
  have hFinite : ENNReal.ofReal A * c * dirichletEnergy Dw Ω.val ≠ ⊤ := by
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc)
    rw [dirichletEnergy_eq_ofReal_integral hw.integrable_hsNormSq]
    exact ENNReal.ofReal_ne_top
  have hReal := ENNReal.toReal_mono hFinite hEnergy
  rw [dirichletEnergy_toReal hW.integrable_hsNormSq,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA,dirichletEnergy_toReal hw.integrable_hsNormSq] at hReal
  have hNonneg : 0 ≤ ∫ z in Ω.val,hsNormSq (Dw z) := integral_nonneg fun _ => hsNormSq_nonneg _
  refine ⟨hW,by nlinarith only [hReal,hNonneg],?_⟩
  intro P hP
  have hPU := (hData q w Dw hw).2.2 P hP
  have hPV := ae_restrict_of_ae_restrict_of_subset hSub hPU
  filter_upwards [hPV,ae_restrict_mem V.property.measurableSet] with y hy hyV
  rwa [hRaw y hyV] at hy

end StratificationTheory
