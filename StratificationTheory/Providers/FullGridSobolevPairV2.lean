module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import StratificationTheory.Foundation.FullGridEnergy

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped ENNReal Topology
open StratificationTheory
namespace StratificationTheory.Providers.FullGridSobolevPairV2

private theorem ae_full_grid_pair_vertex_properties {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u v : Domain (n + 1) → Ambient q}
    {Du Dv : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (hv : MemW12 (ballDomain z R) v Dv)
    (S : Fin (n + 1) → Set (Domain n)) (hS : ∀ i, MeasurableSet (S i))
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i < b i)
    (hrect : ∀ i x, x ∈ S i → ∀ t ∈ Ioo (a i) (b i),
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (Fin.natAdd n (0 : Fin 1)) i))
        ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
          (x, EuclideanSpace.single (0 : Fin 1) t)) ∈ ball z R) :
    let p := fun i : Fin (n + 1) => Equiv.swap (Fin.natAdd n (0 : Fin 1)) i
    let Q := fun i => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (p i)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Ω := fun i => {y : Domain (n + 1) |
      (e ((Q i).symm y)).1 ∈ S i ∧ (e ((Q i).symm y)).2 0 ∈ Ioo (a i) (b i)}
    let Wu := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) u Du
    let Wv := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) v Dv
    let c := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let β := fun i y => (e ((Q i).symm y)).1
    ∀ᵐ y ∂volume, ∀ i, y ∈ Ω i →
    Wu i y = u y ∧ Wv i y = v y ∧
    AbsolutelyContinuousOnInterval (fun t => Wu i (c i (β i y) t)) (a i) (b i) ∧
    AbsolutelyContinuousOnInterval (fun t => Wv i (c i (β i y) t)) (a i) (b i) ∧
    ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
      (Wu i (c i (β i y) t) - Wu i (c i (β i y) s) = ∫ r in s..t, Du (c i (β i y) r) i) ∧
      (Wv i (c i (β i y) t) - Wv i (c i (β i y) s) = ∫ r in s..t, Dv (c i (β i y) r) i) := by
  intro p Q e Ω Wu Wv c β
  have hΩ (i : Fin (n + 1)) : MeasurableSet (Ω i) :=
    ((hS i).preimage (continuous_fst.comp
      (e.continuous.comp (Q i).symm.continuous)).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp (e.continuous.comp (Q i).symm.continuous))).measurable)
  have hidx (i : Fin (n + 1)) : p i (Fin.natAdd n (0 : Fin 1)) = i := Equiv.swap_apply_left _ _
  have hrepU (i : Fin (n + 1)) := coordinatePermACLRepresentative_of_memW12_ball
    hR hu (p i) (hS i) (hab i) (hrect i)
  have hrepV (i : Fin (n + 1)) := coordinatePermACLRepresentative_of_memW12_ball
    hR hv (p i) (hS i) (hab i) (hrect i)

  apply ae_all_iff.mpr
  intro i
  apply (ae_restrict_iff' (hΩ i)).mp
  have hcoord := ((measurePreserving_cylinder_coordinates n).comp
    (Q i).symm.measurePreserving).restrict_preimage
      ((hS i).prod (measurableSet_Ioo (a := a i) (b := b i)))
  rw [← Measure.prod_restrict] at hcoord
  have huProduct := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (S i)) (ν := volume.restrict (Ioo (a i) (b i)))).ae (hrepU i).2.2
  have hvProduct := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (S i)) (ν := volume.restrict (Ioo (a i) (b i)))).ae (hrepV i).2.2
  have huAmbient := hcoord.quasiMeasurePreserving.ae huProduct
  have hvAmbient := hcoord.quasiMeasurePreserving.ae hvProduct
  filter_upwards [(hrepU i).2.1, (hrepV i).2.1, huAmbient, hvAmbient]
    with y hyU hyV hyu hyv
  refine ⟨hyU, hyV, hyu.1, hyv.1, ?_⟩
  intro s hs t ht
  have hdu := hyu.2 s hs t ht
  have hdv := hyv.2 s hs t ht
  simp only [Function.comp_def] at hdu hdv
  rw [hidx i] at hdu hdv
  dsimp only [Wu, Wv, c, β, Q, e]
  exact ⟨hdu, hdv⟩

private theorem full_grid_canonical_energy_and_vertex_compatibility {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u v : Domain (n + 1) → Ambient q}
    {Du Dv : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (hv : MemW12 (ballDomain z R) v Dv)
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
    let Wu := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) u Du
    let Wv := fun i => coordinatePermACLRepresentative (p i) (a i) (b i) v Dv
    let c := fun i x t => Q i (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    let β := fun i y => (e ((Q i).symm y)).1
    let E := (ball z R).indicator (fun y => ENNReal.ofReal (hsNormSq (Du y) + hsNormSq (Dv y)))
    let Δ := (ball z R).indicator (fun y => ENNReal.ofReal (‖u y - v y‖ ^ 2))
    let basis := (Pi.basisFun ℝ (Fin (n + 1))).isUnitSMul
      (w := fun _i : Fin (n + 1) => ε) (fun _i => hε.ne'.isUnit)
    ∃ offset : Fin (n + 1) → ℝ,
      (∀ i, offset i ∈ Ico (0 : ℝ) ε) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let y := WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)
        ∀ i, y ∈ Ω i →
          Wu i y = u y ∧ Wv i y = v y ∧
          AbsolutelyContinuousOnInterval (fun t => Wu i (c i (β i y) t)) (a i) (b i) ∧
          AbsolutelyContinuousOnInterval (fun t => Wv i (c i (β i y) t)) (a i) (b i) ∧
          ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
            (Wu i (c i (β i y) t) - Wu i (c i (β i y) s) = ∫ r in s..t, Du (c i (β i y) r) i) ∧
            (Wv i (c i (β i y) t) - Wv i (c i (β i y) s) = ∫ r in s..t, Dv (c i (β i y) r) i)) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let y := WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)
        ∀ i j, y ∈ Ω i → y ∈ Ω j → Wu i y = Wu j y ∧ Wv i y = Wv j y) ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), gridEdgeDensity ε E i ((l : Fin (n + 1) → ℝ) + offset)) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ *
          (dirichletEnergy Du (ball z R) + dirichletEnergy Dv (ball z R)) ∧
      (∑' l : Submodule.span ℤ (Set.range basis),
        ∑ i : Fin (n + 1), gridEdgeDensity ε Δ i ((l : Fin (n + 1) → ℝ) + offset)) ≤
        (2 * (n + 1)) * (ENNReal.ofReal (ε ^ n))⁻¹ *
          ∫⁻ y in ball z R, ENNReal.ofReal (‖u y - v y‖ ^ 2) := by
  intro p Q e Ω Wu Wv c β E Δ basis
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
  generalize hPdef : (fun y : Domain (n + 1) => ∀ i, y ∈ Ω i →
    Wu i y = u y ∧ Wv i y = v y ∧
    AbsolutelyContinuousOnInterval (fun t => Wu i (c i (β i y) t)) (a i) (b i) ∧
    AbsolutelyContinuousOnInterval (fun t => Wv i (c i (β i y) t)) (a i) (b i) ∧
    ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
      (Wu i (c i (β i y) t) - Wu i (c i (β i y) s) = ∫ r in s..t, Du (c i (β i y) r) i) ∧
      (Wv i (c i (β i y) t) - Wv i (c i (β i y) s) = ∫ r in s..t, Dv (c i (β i y) r) i)) = P
  have hPraw := ae_full_grid_pair_vertex_properties hR hu hv S hS a b hab hrect
  dsimp only at hPraw
  have hP : ∀ᵐ y ∂volume, P y := by
    rw [← hPdef]
    dsimp only [p, Q, e, Ω, Wu, Wv, c, β]
    exact hPraw
  obtain ⟨offset, ho, hPo, hFo, hGo⟩ := exists_full_grid_translate_pair_energy
    hε hE hΔ hEfinite hΔfinite hP
  refine ⟨offset, ho, ?_, ?_, ?_, ?_⟩
  · intro l y i hi
    have hy : P y := hPo l
    rw [← hPdef] at hy
    exact hy i hi
  · intro l y i j hi hj
    have hy : P y := hPo l
    rw [← hPdef] at hy
    exact ⟨(hy i hi).1.trans (hy j hj).1.symm,
      (hy i hi).2.1.trans (hy j hj).2.1.symm⟩
  · rwa [hEI] at hFo
  · rwa [hΔtotal] at hGo

theorem result {n q : ℕ}
    {z : Domain (n + 1)} {R : ℝ} (hR : 0 < R)
    {u v : Domain (n + 1) → Ambient q}
    {Du Dv : Domain (n + 1) → Gradient (n + 1) q}
    (hu : MemW12 (ballDomain z R) u Du) (hv : MemW12 (ballDomain z R) v Dv)
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
        AbsolutelyContinuousOnInterval (fun t => Wu i (c i x t)) (a i) (b i) ∧
        AbsolutelyContinuousOnInterval (fun t => Wv i (c i x t)) (a i) (b i) ∧
        ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
          (Wu i (c i x t) - Wu i (c i x s) = ∫ r in s..t, Du (c i x r) i) ∧
          (Wv i (c i x t) - Wv i (c i x s) = ∫ r in s..t, Dv (c i x r) i)) ∧
    ∃ offset : Fin (n + 1) → ℝ,
      (∀ i, offset i ∈ Ico (0 : ℝ) ε) ∧
      (∀ l : Submodule.span ℤ (Set.range basis),
        let y := WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)
        ∀ i, y ∈ Ω i →
          Wu i y = u y ∧ Wv i y = v y ∧
          AbsolutelyContinuousOnInterval (fun t => Wu i (c i (β i y) t)) (a i) (b i) ∧
          AbsolutelyContinuousOnInterval (fun t => Wv i (c i (β i y) t)) (a i) (b i) ∧
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
  have hcore := full_grid_canonical_energy_and_vertex_compatibility hR hu hv S hS a b hab hrect hε
  obtain ⟨offset, ho, hvertices, hcompat, hE, hΔ⟩ := hcore
  have hrepU (i : Fin (n + 1)) := coordinatePermACLRepresentative_of_memW12_ball
    hR hu (p i) (hS i) (hab i) (hrect i)
  have hrepV (i : Fin (n + 1)) := coordinatePermACLRepresentative_of_memW12_ball
    hR hv (p i) (hS i) (hab i) (hrect i)
  have hidx (i : Fin (n + 1)) : p i (Fin.natAdd n (0 : Fin 1)) = i := Equiv.swap_apply_left _ _
  dsimp only at hvertices
  generalize hPreddef : (fun y : Domain (n + 1) => ∀ i, y ∈ Ω i →
    Wu i y = u y ∧ Wv i y = v y ∧
    AbsolutelyContinuousOnInterval (fun t => Wu i (c i (β i y) t)) (a i) (b i) ∧
    AbsolutelyContinuousOnInterval (fun t => Wv i (c i (β i y) t)) (a i) (b i) ∧
    ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
      (Wu i (c i (β i y) t) - Wu i (c i (β i y) s) = ∫ r in s..t, Du (c i (β i y) r) i) ∧
      (Wv i (c i (β i y) t) - Wv i (c i (β i y) s) = ∫ r in s..t, Dv (c i (β i y) r) i)) = Pred
  have hPo : ∀ l : Submodule.span ℤ (Set.range basis),
      Pred (WithLp.toLp 2 ((l : Fin (n + 1) → ℝ) + offset)) := by
    rw [← hPreddef]
    dsimp only [Wu, Wv, p, Q, e, Ω, c, β, basis]
    exact hvertices
  refine ⟨Wu, Wv, ?_, ?_, offset, ho, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hrepU i).1, (hrepV i).1, (hrepU i).2.1, (hrepV i).2.1⟩
  · intro i
    filter_upwards [(hrepU i).2.2, (hrepV i).2.2] with x hxU hxV
    refine ⟨hxU.1, hxV.1, ?_⟩
    intro s hs t ht
    have hdu := hxU.2 s hs t ht
    have hdv := hxV.2 s hs t ht
    rw [hidx i] at hdu hdv
    exact ⟨hdu, hdv⟩
  · intro l y i hi
    have hy : Pred y := hPo l
    rw [← hPreddef] at hy
    exact hy i hi
  · exact hcompat
  · exact hE
  · exact hΔ

end StratificationTheory.Providers.FullGridSobolevPairV2
