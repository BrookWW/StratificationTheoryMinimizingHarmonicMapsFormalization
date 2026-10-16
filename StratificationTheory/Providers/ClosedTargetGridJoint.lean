module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import StratificationTheory.Foundation.FullGridEnergy
import StratificationTheory.Foundation.CoordinateClosedTargetACL
import StratificationTheory.Foundation.CoordinateClosedTargetLineL2

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
open StratificationTheory
namespace StratificationTheory.Providers.ClosedTargetGridJoint

theorem result {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u v : Domain (n + 1) → Ambient q}
    {Du Dv : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (hv : MemW12 (ballDomain z R) v Dv)
    {N : Set (Ambient q)} (hN : IsClosed N)
    (huN : ∀ᵐ y ∂volume.restrict (ball z R), u y ∈ N)
    (hvN : ∀ᵐ y ∂volume.restrict (ball z R), v y ∈ N)
    (S : Fin (n + 1) → Set (Domain n)) (hS : ∀ i, MeasurableSet (S i))
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i < b i)
    (hrect : ∀ i x, x ∈ S i → ∀ t ∈ Ioo (a i) (b i),
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (Fin.natAdd n (0 : Fin 1)) i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R)
    {ε : ℝ} (hε : 0 < ε) :
    let p := fun i : Fin (n + 1) => Equiv.swap (Fin.natAdd n (0 : Fin 1)) i
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := fun i => {y : Domain (n + 1) |
      (e ((Q i).symm y)).1 ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let c := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let β := fun i y => (e ((Q i).symm y)).1
    let E := (ball z R).indicator (fun y => ENNReal.ofReal (hsNormSq (Du y) + hsNormSq (Dv y)))
    let Δ := (ball z R).indicator (fun y => ENNReal.ofReal (‖u y - v y‖ ^ 2))
    let basis := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _i : Fin (n + 1) => ε) (fun _i => hε.ne'.isUnit)
    ∃ Wu Wv : Fin (n + 1) → Domain (n + 1) → Ambient q,
      (∀ i, AEStronglyMeasurable (Wu i) (volume.restrict (Ω i)) ∧
        AEStronglyMeasurable (Wv i) (volume.restrict (Ω i)) ∧
        Wu i =ᵐ[volume.restrict (Ω i)] u ∧ Wv i =ᵐ[volume.restrict (Ω i)] v) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (S i),
        MemLp (fun t => u (c i x t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        MemLp (fun t => v (c i x t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        MemLp (fun t => Du (c i x t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        MemLp (fun t => Dv (c i x t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
        AbsolutelyContinuousOnInterval (fun t => Wu i (c i x t)) (a i) (b i) ∧
        AbsolutelyContinuousOnInterval (fun t => Wv i (c i x t)) (a i) (b i) ∧
        (fun t => Wu i (c i x t)) =ᵐ[volume.restrict (Ioo (a i) (b i))] (fun t => u (c i x t)) ∧
        (fun t => Wv i (c i x t)) =ᵐ[volume.restrict (Ioo (a i) (b i))] (fun t => v (c i x t)) ∧
        (∀ t ∈ Icc (a i) (b i), Wu i (c i x t) ∈ N ∧ Wv i (c i x t) ∈ N) ∧
        ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
          (Wu i (c i x t) - Wu i (c i x s) = ∫ r in s..t, Du (c i x r) i) ∧
          (Wv i (c i x t) - Wv i (c i x s) = ∫ r in s..t, Dv (c i x r) i)) ∧
    ∃ offset : Fin (n + 1) → ℝ,
      (∀ i, offset i ∈ Ico (0 : ℝ) ε) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let y := WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)
        ∀ i, y ∈ Ω i →
          Wu i y = u y ∧ Wv i y = v y ∧
          MemLp (fun t => u (c i (β i y) t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          MemLp (fun t => v (c i (β i y) t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          MemLp (fun t => Du (c i (β i y) t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          MemLp (fun t => Dv (c i (β i y) t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
          AbsolutelyContinuousOnInterval (fun t => Wu i (c i (β i y) t)) (a i) (b i) ∧
          AbsolutelyContinuousOnInterval (fun t => Wv i (c i (β i y) t)) (a i) (b i) ∧
          (fun t => Wu i (c i (β i y) t)) =ᵐ[volume.restrict (Ioo (a i) (b i))]
            (fun t => u (c i (β i y) t)) ∧
          (fun t => Wv i (c i (β i y) t)) =ᵐ[volume.restrict (Ioo (a i) (b i))]
            (fun t => v (c i (β i y) t)) ∧
          (∀ t ∈ Icc (a i) (b i), Wu i (c i (β i y) t) ∈ N ∧ Wv i (c i (β i y) t) ∈ N) ∧
          ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
            (Wu i (c i (β i y) t) - Wu i (c i (β i y) s) = ∫ r in s..t, Du (c i (β i y) r) i) ∧
            (Wv i (c i (β i y) t) - Wv i (c i (β i y) s) = ∫ r in s..t, Dv (c i (β i y) r) i)) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let y := WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)
        ∀ i j, y ∈ Ω i → y ∈ Ω j → Wu i y = Wu j y ∧ Wv i y = Wv j y) ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), (∫⁻ t in Ico (0 : ℝ) ε, E (WithLp.toLp 2 (((l : Fin (n + 1) → ℝ) + offset) + t • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ))))) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ *
          (dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R)) ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), (∫⁻ t in Ico (0 : ℝ) ε, Δ (WithLp.toLp 2 (((l : Fin (n + 1) → ℝ) + offset) + t • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ))))) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ *
          ∫⁻ y in ball z R, ENNReal.ofReal (‖u y - v y‖ ^ 2) := by
  intro p Q e Ω c β E Δ basis
  let Wu := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) u Du
  let Wv := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) v Dv
  have hidx (i : Fin (n + 1)) : p i (Fin.natAdd n (0 : Fin 1)) = i :=
    Equiv.swap_apply_left _ _
  have hrepU (i : Fin (n + 1)) :=
    coordinatePermACLRepresentative_closed_target_of_memW12_ball
      hR hu hN huN (p i) (hS i) (hab i) (hrect i)
  have hrepV (i : Fin (n + 1)) :=
    coordinatePermACLRepresentative_closed_target_of_memW12_ball
      hR hv hN hvN (p i) (hS i) (hab i) (hrect i)
  have hLpU (i : Fin (n + 1)) :=
    ae_coordinatePerm_line_memLp_two_of_memW12_ball
      hR hu (p i) (hS i) (hab i) (hrect i)
  have hLpV (i : Fin (n + 1)) :=
    ae_coordinatePerm_line_memLp_two_of_memW12_ball
      hR hv (p i) (hS i) (hab i) (hrect i)
  generalize hLdef : (fun (i : Fin (n + 1)) (x : Domain n) =>
    MemLp (fun t => u (c i x t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
    MemLp (fun t => v (c i x t)) 2 (volume.restrict (Ioo (a i) (b i))) ∧
    MemLp (fun t => Du (c i x t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
    MemLp (fun t => Dv (c i x t) i) 2 (volume.restrict (Ioo (a i) (b i))) ∧
    AbsolutelyContinuousOnInterval (fun t => Wu i (c i x t)) (a i) (b i) ∧
    AbsolutelyContinuousOnInterval (fun t => Wv i (c i x t)) (a i) (b i) ∧
    (fun t => Wu i (c i x t)) =ᵐ[volume.restrict (Ioo (a i) (b i))] (fun t => u (c i x t)) ∧
    (fun t => Wv i (c i x t)) =ᵐ[volume.restrict (Ioo (a i) (b i))] (fun t => v (c i x t)) ∧
    (∀ t ∈ Icc (a i) (b i), Wu i (c i x t) ∈ N ∧ Wv i (c i x t) ∈ N) ∧
    ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
      (Wu i (c i x t) - Wu i (c i x s) = ∫ r in s..t, Du (c i x r) i) ∧
      (Wv i (c i x t) - Wv i (c i x s) = ∫ r in s..t, Dv (c i x r) i)) = L
  have hlines : ∀ i, ∀ᵐ x ∂volume.restrict (S i), L i x := by
    intro i
    rw [← hLdef]
    filter_upwards [hLpU i, hLpV i, (hrepU i).2.2, (hrepV i).2.2] with x hxLU hxLV hxU hxV
    have hDu := hxLU.2
    have hDv := hxLV.2
    rw [hidx i] at hDu hDv
    refine ⟨hxLU.1, hxLV.1, hDu, hDv, hxU.1, hxV.1, hxU.2.1, hxV.2.1, ?_, ?_⟩
    · intro t ht
      exact ⟨hxU.2.2.1 t ht, hxV.2.2.1 t ht⟩
    · intro s hs t ht
      have hdu := hxU.2.2.2 s hs t ht
      have hdv := hxV.2.2.2 s hs t ht
      rw [hidx i] at hdu hdv
      exact ⟨hdu, hdv⟩
  have hΩ (i : Fin (n + 1)) : MeasurableSet (Ω i) :=
    ((hS i).preimage (continuous_fst.comp
      (e.continuous.comp (Q i).symm.continuous)).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp (e.continuous.comp (Q i).symm.continuous))).measurable)
  generalize hPdef : (fun y : Domain (n + 1) => ∀ i, y ∈ Ω i →
    Wu i y = u y ∧ Wv i y = v y ∧ L i (β i y)) = P
  have hP : ∀ᵐ y ∂volume, P y := by
    rw [← hPdef]
    apply ae_all_iff.mpr
    intro i
    apply (ae_restrict_iff' (hΩ i)).mp
    have hcoord := ((measurePreserving_cylinder_coordinates n).comp
      (Q i).symm.measurePreserving).restrict_preimage
        ((hS i).prod (measurableSet_Ioo (a := a i) (b := b i)))
    rw [← Measure.prod_restrict] at hcoord
    have hProduct := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (S i)) (ν := volume.restrict (Ioo (a i) (b i)))).ae (hlines i)
    have hAmbient := hcoord.quasiMeasurePreserving.ae hProduct
    filter_upwards [(hrepU i).2.1, (hrepV i).2.1, hAmbient] with y hyU hyV hyL
    simp only [Function.comp_def] at hyL
    refine And.intro hyU (And.intro hyV ?_)
    exact hyL
  have hEu : AEMeasurable (fun y => ENNReal.ofReal (hsNormSq (Du y)))
      (volume.restrict (ball z R)) := hu.integrable_hsNormSq.aemeasurable.ennreal_ofReal
  have hE : AEMeasurable E volume := by
    apply (aemeasurable_indicator_iff measurableSet_ball).mpr
    exact (hu.integrable_hsNormSq.add hv.integrable_hsNormSq).aemeasurable.ennreal_ofReal
  have hEI : (∫⁻ y, E y) =
      dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R) := by
    rw [lintegral_indicator measurableSet_ball]
    simp_rw [ENNReal.ofReal_add (hsNormSq_nonneg (Du _)) (hsNormSq_nonneg (Dv _))]
    exact lintegral_add_left' hEu _
  have hΔI := (hu.2.1.sub hv.2.1).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hΔ : AEMeasurable Δ volume :=
    (aemeasurable_indicator_iff measurableSet_ball).mpr hΔI.aemeasurable.ennreal_ofReal
  have hΔtotal : (∫⁻ y, Δ y) = ∫⁻ y in ball z R, ENNReal.ofReal (‖u y - v y‖ ^ 2) :=
    lintegral_indicator measurableSet_ball _
  have hΔfinite : (∫⁻ y, Δ y) ≠ ⊤ := by
    rw [hΔtotal]
    exact (lintegral_ofReal_ne_top_iff_integrable hΔI.aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _)).mpr hΔI
  have hEfinite : (∫⁻ y, E y) ≠ ⊤ := by
    rw [hEI]
    exact ENNReal.add_ne_top.mpr ⟨hu.dirichletEnergy_ne_top, hv.dirichletEnergy_ne_top⟩
  obtain ⟨offset, ho, hPo, hFo, hGo⟩ := exists_full_grid_translate_pair_energy
    hε hE hΔ hEfinite hΔfinite hP
  refine ⟨Wu, Wv, ?_, ?_, offset, ho, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hrepU i).1, (hrepV i).1, (hrepU i).2.1, (hrepV i).2.1⟩
  · rw [← hLdef] at hlines
    exact hlines
  · intro l y i hi
    have hy : P y := hPo l
    rw [← hPdef] at hy
    have hiy := hy i hi
    rw [← hLdef] at hiy
    exact hiy
  · intro l y i j hi hj
    have hy : P y := hPo l
    rw [← hPdef] at hy
    exact ⟨(hy i hi).1.trans (hy j hj).1.symm,
      (hy i hi).2.1.trans (hy j hj).2.1.symm⟩
  · rwa [hEI] at hFo
  · rwa [hΔtotal] at hGo

end StratificationTheory.Providers.ClosedTargetGridJoint
