module

public import HarmonicMaps.Analysis.SmoothInverseSobolev
public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ContDiff
namespace StratificationTheory

/-- An actual Euclidean rotation about the ball center pulls back Sobolev
maps with the displayed linear combinations of their original weak columns. -/
theorem memW12_ball_centered_isometry {n q : ℕ}
    {c : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain c R) u Du) (Q : Domain n ≃ₗᵢ[ℝ] Domain n) :
    MemW12 (ballDomain c R) (fun x => u (c + Q (x - c)))
      (fun x i => ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • Du (c + Q (x - c)) j) := by
  let f : Domain n → Domain n := fun x => c + Q.symm (x - c)
  let g : Domain n → Domain n := fun x => c + Q (x - c)
  have hf : ContDiff ℝ ∞ f :=
    contDiff_const.add (Q.symm.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const))
  have hg : ContDiff ℝ ∞ g :=
    contDiff_const.add (Q.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const))
  have hfg : Function.RightInverse g f := by
    intro x
    simp only [f, g, add_sub_cancel_left, Q.symm_apply_apply, add_sub_cancel]
  have hgf : Function.LeftInverse g f := by
    intro x
    simp only [f, g, add_sub_cancel_left, Q.apply_symm_apply, add_sub_cancel]
  have hfball : MapsTo f (ball c R) (ball c R) := by
    intro x hx
    rw [mem_ball_iff_norm] at hx ⊢
    simpa only [f, add_sub_cancel_left, Q.symm.norm_map] using hx
  have hgball : MapsTo g (ball c R) (ball c R) := by
    intro x hx
    rw [mem_ball_iff_norm] at hx ⊢
    simpa only [g, add_sub_cancel_left, Q.norm_map] using hx
  have hcomp := hu.comp_smooth_inverse_ball hR hf hg hfg hgf hfball hgball
  have hD (x : Domain n) : fderiv ℝ g x = Q.toContinuousLinearEquiv.toContinuousLinearMap := by
    have hh := ((Q.toContinuousLinearEquiv.hasFDerivAt.comp x
      ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)).const_add c)
    simpa only [g, Function.comp_apply, id_eq, ContinuousLinearMap.comp_id,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hh.fderiv
  have hcols : (fun x i => ∑ j : Fin n,
      (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j) =
        (fun x i => ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • Du (c + Q (x - c)) j) := by
    funext x i
    rw [hD]
    rfl
  rw [hcols] at hcomp
  exact hcomp

/-- Orthogonal changes of the source basis preserve the actual sum of
squared column norms, including zero-dimensional source or target spaces. -/
theorem hsNormSq_source_isometry {n q : ℕ} (Q : Domain n ≃ₗᵢ[ℝ] Domain n)
    (A : Gradient n q) :
    hsNormSq (fun i => ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • A j) = hsNormSq A := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).map Q
  have hentry (i : Fin n) (k : Fin q) :
      (∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • A j) k =
        ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j * (A j) k := by
    change (EuclideanSpace.proj k) (∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • A j) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  rw [hsNormSq_eq_sum_entries, hsNormSq_eq_sum_entries, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  let v : Domain n := WithLp.toLp 2 (fun j => (A j) k)
  have hi (i : Fin n) : inner ℝ (b i) v =
      ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j * (A j) k := by
    simp [b, PiLp.inner_apply, EuclideanSpace.basisFun_apply, v, mul_comm]
  have h := b.sum_sq_norm_inner_right v
  simpa only [hi, Real.norm_eq_abs, sq_abs, EuclideanSpace.real_norm_sq_eq, v,
    hentry] using h

/-- The same centered Euclidean isometry gives full weak data and exact
real and extended Dirichlet energy, using the original weak columns. -/
theorem memW12_ball_centered_isometry_energy {n q : ℕ}
    {c : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain c R) u Du) (Q : Domain n ≃ₗᵢ[ℝ] Domain n) :
    let g : Domain n → Domain n := fun x => c + Q (x - c)
    let D : Domain n → Gradient n q := fun x i =>
      ∑ j : Fin n, (Q (EuclideanSpace.single i 1)) j • Du (g x) j
    MemW12 (ballDomain c R) (u ∘ g) D ∧
      (∀ x, hsNormSq (D x) = hsNormSq (Du (g x))) ∧
      (∫ x in ball c R, hsNormSq (D x)) = (∫ x in ball c R, hsNormSq (Du x)) ∧
      dirichletEnergy D (ball c R) = dirichletEnergy Du (ball c R) := by
  intro g D
  have hW : MemW12 (ballDomain c R) (u ∘ g) D := memW12_ball_centered_isometry hR hu Q
  have hHS (x : Domain n) : hsNormSq (D x) = hsNormSq (Du (g x)) :=
    hsNormSq_source_isometry Q (Du (g x))
  let G : Domain n ≃ₜ Domain n := (Homeomorph.addRight (-c)).trans
    (Q.toHomeomorph.trans (Homeomorph.addLeft c))
  have hG : (G : Domain n → Domain n) = g := by
    funext x
    change c + Q (x + -c) = c + Q (x - c)
    rw [sub_eq_add_neg]
  have hMP : MeasurePreserving g volume volume := by
    have h := (measurePreserving_add_left volume c).comp
      (Q.measurePreserving.comp (measurePreserving_add_right volume (-c)))
    simpa only [Function.comp_def, g, sub_eq_add_neg] using h
  have hEmb : MeasurableEmbedding g := by
    rw [← hG]
    exact G.measurableEmbedding
  have hpre : g ⁻¹' ball c R = ball c R := by
    ext x
    simp only [mem_preimage, mem_ball_iff_norm, g, add_sub_cancel_left, Q.norm_map]
  have hMPB := hMP.restrict_preimage (measurableSet_ball (x := c) (ε := R))
  rw [hpre] at hMPB
  have hE : (∫ x in ball c R, hsNormSq (D x)) = ∫ x in ball c R, hsNormSq (Du x) := by
    calc
      _ = ∫ x in ball c R, hsNormSq (Du (g x)) := integral_congr_ae (Eventually.of_forall hHS)
      _ = _ := hMPB.integral_comp hEmb (fun x => hsNormSq (Du x))
  refine ⟨hW, hHS, hE, ?_⟩
  have hDI : IntegrableOn (fun x => hsNormSq (D x)) (ball c R) := hW.integrable_hsNormSq
  have hUI : IntegrableOn (fun x => hsNormSq (Du x)) (ball c R) := hu.integrable_hsNormSq
  rw [dirichletEnergy_eq_ofReal_integral hDI, dirichletEnergy_eq_ofReal_integral hUI, hE]

end StratificationTheory
