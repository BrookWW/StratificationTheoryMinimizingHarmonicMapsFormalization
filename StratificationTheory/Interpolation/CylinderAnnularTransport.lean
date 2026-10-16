module

public import StratificationTheory.Foundation.AnnularTestFields
public import StratificationTheory.Frozen.CylinderSobolev
import StratificationTheory.Interpolation.CylinderLinearInterpolation
import HarmonicMaps.SobolevLemmas
import HarmonicMaps.SobolevRestriction
import Mathlib.Analysis.Calculus.FDeriv.Add
import StratificationTheory.Foundation.CylinderRadialAverage
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import StratificationTheory.Foundation.AnnularTestCutoff
import StratificationTheory.Foundation.AnnularCylinderL2

/-!
# Actual annular Sobolev transport by radial averaging

Physical spatial-time coordinates preserve the finite divergence trace.
Compact annular fields give exact Jacobian identities for an original ambient
weak gradient. Native polar Fubini and radial probability averages retain the
same weighted map and full weak columns. The resulting literal annular map
is Sobolev with its actual averaged columns. Smooth weights of unit radial
average and translation adapters are also provided.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace StratificationTheory

private theorem cylinder_coordinate_fst {n : ℕ} (y : Domain (n + 1)) (i : Fin n) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 i =
      y (Fin.castAdd 1 i) := by
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    PiLp.sumPiLpEquivProdLpPiLp]

private theorem cylinder_coordinate_time {n : ℕ} (y : Domain (n + 1)) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 =
      y (Fin.natAdd n (0 : Fin 1)) := by
  simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
    PiLp.sumPiLpEquivProdLpPiLp]

private theorem cylinder_spatial_scalar_derivative {n : ℕ}
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : Domain n) (t : ℝ) (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    fderiv ℝ (fun z : Domain n => φ (e.symm (z, EuclideanSpace.single (0 : Fin 1) t))) x
      (EuclideanSpace.single i 1) =
      fderiv ℝ φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
        (EuclideanSpace.single (Fin.castAdd 1 i) 1) := by
  intro e
  have h := (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    (e.symm.hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (EuclideanSpace.single (0 : Fin 1) t) x)))
  change HasFDerivAt (fun z : Domain n => φ (e.symm (z, EuclideanSpace.single (0 : Fin 1) t))) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply]
  have hb : e.symm (EuclideanSpace.single i 1, 0) =
      EuclideanSpace.single (Fin.castAdd 1 i) 1 := by
    apply e.injective
    rw [e.apply_symm_apply, finAddEquivProd_spatial_basis]
  change fderiv ℝ φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    (e.symm (EuclideanSpace.single i 1, 0)) = _
  rw [hb]

private theorem cylinder_time_scalar_derivative {n : ℕ}
    {φ : Domain (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Domain n) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    deriv (fun τ : ℝ => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ))) t =
      fderiv ℝ φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
        (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) := by
  intro e
  have hsingle : HasDerivAt (fun τ : ℝ => EuclideanSpace.single (0 : Fin 1) τ)
      (EuclideanSpace.single (0 : Fin 1) 1) t := by
    convert (hasDerivAt_id t).smul_const (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) using 1 <;>
      first
      | rfl
      | simp only [one_smul]
      | (funext τ
         ext j
         simp only [EuclideanSpace.single, PiLp.single_apply, PiLp.smul_apply, smul_eq_mul, id_eq]
         split_ifs <;> ring)

  have harg := e.symm.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk hsingle)
  have h := (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t harg
  change HasDerivAt (fun τ : ℝ => φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ))) _ t at h
  rw [h.deriv]
  have hb : e.symm (0, EuclideanSpace.single (0 : Fin 1) 1) =
      EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1 := by
    apply e.injective
    rw [e.apply_symm_apply, finAddEquivProd_time_basis]
  change fderiv ℝ φ (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))
    (e.symm (0, EuclideanSpace.single (0 : Fin 1) 1)) = _
  rw [hb]

/-- The actual ambient divergence equals the spatial plus temporal divergence
of the same physical field under the canonical coordinate split. -/
theorem cylinder_ambient_divergence_eq_coordinates {n : ℕ}
    {V : Domain (n + 1) → Domain (n + 1)} (hV : ContDiff ℝ ∞ V)
    (x : Domain n) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let y := e.symm (x, EuclideanSpace.single (0 : Fin 1) t)
    (∑ k : Fin (n + 1), (fderiv ℝ V y (EuclideanSpace.single k 1)) k) =
      (∑ i : Fin n, (fderiv ℝ (fun z : Domain n =>
        (e (V (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).1) x
          (EuclideanSpace.single i 1)) i) +
        deriv (fun τ : ℝ => (e (V (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ)))).2 0) t := by
  intro e y
  have hcoord (k : Fin (n + 1)) : ContDiff ℝ ∞ (fun z => V z k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hV
  have hcoordD (k : Fin (n + 1)) : fderiv ℝ (fun z => V z k) y =
      (EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ V y) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp y
      (hV.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  have hsp (i : Fin n) : (fderiv ℝ (fun z : Domain n =>
      (e (V (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).1) x
        (EuclideanSpace.single i 1)) i =
      (fderiv ℝ V y (EuclideanSpace.single (Fin.castAdd 1 i) 1)) (Fin.castAdd 1 i) := by
    have harg := e.symm.hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (EuclideanSpace.single (0 : Fin 1) t) x))
    have hVc := (hV.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x harg
    have heVc := e.hasFDerivAt.comp x hVc
    have hF := (ContinuousLinearMap.fst ℝ (Domain n) (Domain 1)).hasFDerivAt.comp x heVc
    change HasFDerivAt (fun z : Domain n =>
      (e (V (e.symm (z, EuclideanSpace.single (0 : Fin 1) t)))).1) _ x at hF
    rw [hF.fderiv]
    have hb : e.symm (EuclideanSpace.single i 1, 0) =
        EuclideanSpace.single (Fin.castAdd 1 i) 1 := by
      apply e.injective
      rw [e.apply_symm_apply, finAddEquivProd_spatial_basis]
    change (e (fderiv ℝ V y (e.symm (EuclideanSpace.single i 1, 0)))).1 i = _
    rw [hb, cylinder_coordinate_fst]

  have htime : deriv (fun τ : ℝ => (e (V (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ)))).2 0) t =
      (fderiv ℝ V y (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1))
        (Fin.natAdd n (0 : Fin 1)) := by
    have hscalar := cylinder_time_scalar_derivative (hcoord (Fin.natAdd n (0 : Fin 1))) x t
    change deriv (fun τ : ℝ => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ))
      (Fin.natAdd n (0 : Fin 1))) t =
      fderiv ℝ (fun z => V z (Fin.natAdd n (0 : Fin 1))) y
        (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) 1) at hscalar
    rw [hcoordD] at hscalar
    have hfun : (fun τ : ℝ => (e (V (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ)))).2 0) =
        (fun τ : ℝ => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) τ)) (Fin.natAdd n (0 : Fin 1))) := by
      funext τ
      exact cylinder_coordinate_time _
    rw [hfun]
    exact hscalar
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_one]
  rw [htime]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (hsp i).symm


/-- The full ambient Euclidean divergence of the actual test field has the
annular Jacobian formula, before removing the time-cutoff derivative. -/
theorem divergence_annularTestField {n : ℕ} (hn : 2 ≤ n) (s : ℝ)
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (hβ0 : (0 : ℝ) ∉ tsupport β) (i : Fin n)
    (x : Domain n) (hx : x ≠ 0) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let y := e.symm (x, EuclideanSpace.single (0 : Fin 1) t)
    let θ := ‖x‖⁻¹ • x
    let L := s * (1 + t)
    (∑ k : Fin (n + 1),
      (fderiv ℝ (annularTestField s β ζ ψ i) y (EuclideanSpace.single k 1)) k) =
      s * L ^ (n - 1) * β ‖x‖ * ζ t * coordinateDerivative ψ hψ i (L • θ) +
        L ^ (n - 1) * β ‖x‖ * deriv ζ t * ψ (L • θ) * θ i := by
  exact (cylinder_ambient_divergence_eq_coordinates
    (contDiff_annularTestField s hβ hζ hψ hβ0 i) x t).trans
      (annularTestField_coordinate_divergence hn s hβ hζ hψ i x hx t)

/-- A genuine weak gradient satisfies the vector-test identity for every
smooth compactly supported actual Euclidean field in its original domain. -/
theorem hasWeakGradient_integral_divergence_test {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) {V : Domain n → Domain n}
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V) (hsV : tsupport V ⊆ Ω.val) :
    (∫ x in Ω.val, (∑ k : Fin n, (fderiv ℝ V x (EuclideanSpace.single k 1)) k) • u x) =
      -(∫ x in Ω.val, ∑ k : Fin n, V x k • Du x k) := by
  let φ : Fin n → Domain n → ℝ := fun k x => V x k
  have hφ (k : Fin n) : ContDiff ℝ ∞ (φ k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hV
  have hcφ (k : Fin n) : HasCompactSupport (φ k) :=
    hcV.comp_left (map_zero (EuclideanSpace.proj (𝕜 := ℝ) k))
  have hsφ (k : Fin n) : tsupport (φ k) ⊆ Ω.val := by
    have hs : Function.support (φ k) ⊆ Function.support V := by
      intro x hx hz
      exact hx (congrArg (fun z : Domain n => z k) hz)
    exact (closure_mono hs).trans hsV
  have hDφ (k : Fin n) (x : Domain n) : coordinateDerivative (φ k) (hφ k) k x =
      (fderiv ℝ V x (EuclideanSpace.single k 1)) k := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x
      (hV.differentiable (by simp)).differentiableAt.hasFDerivAt
    change HasFDerivAt (φ k) _ x at h
    rw [coordinateDerivative, h.fderiv]
    rfl
  have hLI (k : Fin n) : IntegrableOn
      (fun x => coordinateDerivative (φ k) (hφ k) k x • u x) Ω.val :=
    hu.integrable_test_derivative k (hφ k) (hcφ k) (hsφ k)
  have hRI (k : Fin n) : IntegrableOn (fun x => φ k x • Du x k) Ω.val :=
    hu.integrable_test_gradient k (hφ k) (hcφ k) (hsφ k)
  calc
    _ = ∫ x in Ω.val, ∑ k : Fin n, coordinateDerivative (φ k) (hφ k) k x • u x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [Finset.sum_smul]
        simp only [hDφ]
    _ = ∑ k : Fin n, ∫ x in Ω.val, coordinateDerivative (φ k) (hφ k) k x • u x :=
      integral_finsetSum Finset.univ (fun k _ => hLI k)
    _ = ∑ k : Fin n, -(∫ x in Ω.val, φ k x • Du x k) :=
      Finset.sum_congr rfl fun k _ => hu.2.2 k (φ k) (hφ k) (hcφ k) (hsφ k)
    _ = _ := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun k _ => hRI k)]


/-- The original ambient weak gradient gives the annular Jacobian test
identity, with its original columns and without assuming annular membership. -/
theorem annular_test_field_distribution_identity {n q : ℕ} (hn : 2 ≤ n) (s : ℝ)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : HasWeakGradient Ω w Dw)
    (hΩ0 : ∀ y ∈ Ω.val,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1 ≠ 0)
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (hcβ : HasCompactSupport β) (hcζ : HasCompactSupport ζ)
    {l r a b : ℝ} (hl : 0 ≤ l) (hsβ : tsupport β ⊆ Ioo l r)
    (hsζ : tsupport ζ ⊆ Ioo a b)
    (hband : {y : Domain (n + 1) |
      ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∈ Ioo l r ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b} ⊆ Ω.val)
    (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    (∫ y in Ω.val,
      (let x := (e y).1
       let t := (e y).2 0
       let θ := ‖x‖⁻¹ • x
       let L := s * (1 + t)
       s * L ^ (n - 1) * β ‖x‖ * ζ t * coordinateDerivative ψ hψ i (L • θ) +
         L ^ (n - 1) * β ‖x‖ * deriv ζ t * ψ (L • θ) * θ i) • w y) =
      -(∫ y in Ω.val, ∑ k : Fin (n + 1), annularTestField s β ζ ψ i y k • Dw y k) := by
  intro e
  have hβ0 : (0 : ℝ) ∉ tsupport β := fun h => (not_lt_of_ge hl) (hsβ h).1
  have hV := contDiff_annularTestField s hβ hζ hψ hβ0 i
  have hcV := hasCompactSupport_annularTestField s hcβ hcζ ψ i
  have hsV := (tsupport_annularTestField_subset_collar s hsβ hsζ ψ i).trans hband
  have hid := hasWeakGradient_integral_divergence_test hw hV hcV hsV
  have hdiag (y : Domain (n + 1)) (hy : y ∈ Ω.val) :
      (∑ k : Fin (n + 1),
        (fderiv ℝ (annularTestField s β ζ ψ i) y (EuclideanSpace.single k 1)) k) =
      s * (s * (1 + (e y).2 0)) ^ (n - 1) * β ‖(e y).1‖ * ζ ((e y).2 0) *
        coordinateDerivative ψ hψ i ((s * (1 + (e y).2 0)) • (‖(e y).1‖⁻¹ • (e y).1)) +
      (s * (1 + (e y).2 0)) ^ (n - 1) * β ‖(e y).1‖ * deriv ζ ((e y).2 0) *
        ψ ((s * (1 + (e y).2 0)) • (‖(e y).1‖⁻¹ • (e y).1)) * (‖(e y).1‖⁻¹ • (e y).1) i := by
    have h := divergence_annularTestField hn s hβ hζ hψ hβ0 i (e y).1 (hΩ0 y hy) ((e y).2 0)
    dsimp only at h
    simpa only [e, cylinder_coordinates_inverse_left] using h
  calc
    _ = ∫ y in Ω.val, (∑ k : Fin (n + 1),
        (fderiv ℝ (annularTestField s β ζ ψ i) y (EuclideanSpace.single k 1)) k) • w y := by
      apply setIntegral_congr_fun Ω.property.measurableSet
      intro y hy
      dsimp only
      rw [hdiag y hy]
    _ = _ := hid


/-- The actual full gradient contracts with the physical test field in the
same spatial tangential columns and the same original time column. -/
theorem annularTestField_gradient_contraction {n q : ℕ} (s : ℝ)
    (β ζ : ℝ → ℝ) (ψ : Domain n → ℝ) (i : Fin n)
    (Dw : Domain (n + 1) → Gradient (n + 1) q) (x : Domain n) (t : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let y := e.symm (x, EuclideanSpace.single (0 : Fin 1) t)
    let θ := ‖x‖⁻¹ • x
    let L := s * (1 + t)
    (∑ k : Fin (n + 1), annularTestField s β ζ ψ i y k • Dw y k) =
      (s * L ^ (n - 2) * ζ t * β ‖x‖ * ψ (L • θ)) •
        (‖x‖ • Dw y (Fin.castAdd 1 i) -
          θ i • ∑ j : Fin n, x j • Dw y (Fin.castAdd 1 j)) +
      (L ^ (n - 1) * β ‖x‖ * ζ t * ψ (L • θ) * θ i) •
        Dw y (Fin.natAdd n (0 : Fin 1)) := by
  intro e y θ L
  have hcoords := annularTestField_coordinates s β ζ ψ i x t
  have hsp (j : Fin n) : annularTestField s β ζ ψ i y (Fin.castAdd 1 j) =
      s * L ^ (n - 2) * ζ t *
        (β ‖x‖ * ψ (L • θ) * (‖x‖ * (EuclideanSpace.single i (1 : ℝ)) j - θ i * x j)) := by
    have h := congrArg (fun p : Domain n × Domain 1 => p.1 j) hcoords
    rw [cylinder_coordinate_fst] at h
    simpa only [annularSpatialTestField, y, e, θ, L, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] using h
  have htime : annularTestField s β ζ ψ i y (Fin.natAdd n (0 : Fin 1)) =
      L ^ (n - 1) * β ‖x‖ * ζ t * ψ (L • θ) * θ i := by
    have h := congrArg (fun p : Domain n × Domain 1 => p.2 0) hcoords
    rw [cylinder_coordinate_time] at h
    simpa only [EuclideanSpace.single, PiLp.single_apply, ite_true] using h
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_one]
  rw [htime]
  congr 1
  simp_rw [hsp]
  have hcoeff (j : Fin n) : s * L ^ (n - 2) * ζ t *
      (β ‖x‖ * ψ (L • θ) * (‖x‖ * (EuclideanSpace.single i (1 : ℝ)) j - θ i * x j)) =
      (s * L ^ (n - 2) * ζ t * β ‖x‖ * ψ (L • θ)) *
        (‖x‖ * (EuclideanSpace.single i (1 : ℝ)) j - θ i * x j) := by ring
  simp_rw [hcoeff]
  let C := s * L ^ (n - 2) * ζ t * β ‖x‖ * ψ (L • θ)
  change (∑ j : Fin n, (C * (‖x‖ * (EuclideanSpace.single i (1 : ℝ)) j - θ i * x j)) •
    Dw y (Fin.castAdd 1 j)) = C • _
  simp_rw [mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  simp_rw [sub_smul, mul_smul]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  congr 1
  have hdelta : (∑ j : Fin n, (EuclideanSpace.single i (1 : ℝ)) j •
      Dw y (Fin.castAdd 1 j)) = Dw y (Fin.castAdd 1 i) := by
    simp only [EuclideanSpace.single, PiLp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true, one_smul]
    · intro j _ hji
      rw [if_neg hji, zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hdelta]

private theorem weakGradient_vector_test_integrable {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) {V : Domain n → Domain n}
    (hV : ContDiff ℝ ∞ V) (hcV : HasCompactSupport V) (hsV : tsupport V ⊆ Ω.val) :
    IntegrableOn (fun x => (∑ k : Fin n,
      (fderiv ℝ V x (EuclideanSpace.single k 1)) k) • u x) Ω.val ∧
    IntegrableOn (fun x => ∑ k : Fin n, V x k • Du x k) Ω.val := by
  let φ : Fin n → Domain n → ℝ := fun k x => V x k
  have hφ (k : Fin n) : ContDiff ℝ ∞ (φ k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hV
  have hcφ (k : Fin n) : HasCompactSupport (φ k) :=
    hcV.comp_left (map_zero (EuclideanSpace.proj (𝕜 := ℝ) k))
  have hsφ (k : Fin n) : tsupport (φ k) ⊆ Ω.val := by
    have hs : Function.support (φ k) ⊆ Function.support V := by
      intro x hx hz
      exact hx (congrArg (fun z : Domain n => z k) hz)
    exact (closure_mono hs).trans hsV
  have hDφ (k : Fin n) (x : Domain n) : coordinateDerivative (φ k) (hφ k) k x =
      (fderiv ℝ V x (EuclideanSpace.single k 1)) k := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x
      (hV.differentiable (by simp)).differentiableAt.hasFDerivAt
    change HasFDerivAt (φ k) _ x at h
    rw [coordinateDerivative, h.fderiv]
    rfl
  have hLI (k : Fin n) : IntegrableOn
      (fun x => coordinateDerivative (φ k) (hφ k) k x • u x) Ω.val :=
    hu.integrable_test_derivative k (hφ k) (hcφ k) (hsφ k)
  have hRI (k : Fin n) : IntegrableOn (fun x => φ k x • Du x k) Ω.val :=
    hu.integrable_test_gradient k (hφ k) (hcφ k) (hsφ k)
  constructor
  · apply (integrable_finsetSum Finset.univ (fun k _ => hLI k)).congr
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [Finset.sum_smul]
      simp only [hDφ]
  · exact integrable_finsetSum Finset.univ (fun k _ => hRI k)


/-- Native polar Fubini turns the original full ambient weak-gradient test
identity into the actual annular tangential and temporal column integrals. -/
theorem annular_test_field_native_polar_identity {n q : ℕ} (hn : 2 ≤ n) (s : ℝ)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : HasWeakGradient Ω w Dw)
    {l r a b : ℝ} (hl : 0 < l)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (l < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < r) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (hcβ : HasCompactSupport β) (hcζ : HasCompactSupport ζ)
    (hsβ : tsupport β ⊆ Ioo l r) (hsζ : tsupport ζ ⊆ Ioo a b) (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let ν := volume.restrict (Ioo a b)
    let η := (Measure.volumeIoiPow (n - 1)).restrict {ρ : Ioi (0 : ℝ) | l < ρ.val ∧ ρ.val < r}
    let Z : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Domain (n + 1) := fun p =>
      e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)
    let F : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Ambient q := fun p =>
      let θ := p.1.1.val
      let t := p.1.2
      let L := s * (1 + t)
      (s * L ^ (n - 1) * β p.2.val * ζ t * coordinateDerivative ψ hψ i (L • θ) +
        L ^ (n - 1) * β p.2.val * deriv ζ t * ψ (L • θ) * θ i) • w (Z p)
    let G : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Ambient q := fun p =>
      let θ := p.1.1.val
      let t := p.1.2
      let L := s * (1 + t)
      (s * L ^ (n - 2) * ζ t * β p.2.val * ψ (L • θ)) •
        (p.2.val • (Dw (Z p) (Fin.castAdd 1 i) -
          θ i • ∑ j : Fin n, θ j • Dw (Z p) (Fin.castAdd 1 j))) +
      (L ^ (n - 1) * β p.2.val * ζ t * ψ (L • θ) * θ i) •
        Dw (Z p) (Fin.natAdd n (0 : Fin 1))
    Integrable F ((σ.prod ν).prod η) ∧ Integrable G ((σ.prod ν).prod η) ∧
      (∫ p : sphere (0 : Domain n) 1 × ℝ, (∫ ρ, F (p, ρ) ∂η) ∂σ.prod ν) =
        -(∫ p : sphere (0 : Domain n) 1 × ℝ, (∫ ρ, G (p, ρ) ∂η) ∂σ.prod ν) := by
  intro e σ ν η Z F G
  have hnpos : 0 < n := by omega
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos]
    infer_instance
  have hβ0 : (0 : ℝ) ∉ tsupport β := fun h => (not_lt_of_ge hl.le) (hsβ h).1
  let V := annularTestField s β ζ ψ i
  have hV : ContDiff ℝ ∞ V := contDiff_annularTestField s hβ hζ hψ hβ0 i
  have hcV : HasCompactSupport V := hasCompactSupport_annularTestField s hcβ hcζ ψ i
  have hsV : tsupport V ⊆ Ω.val := by
    rw [hΩ]
    exact tsupport_annularTestField_subset_collar s hsβ hsζ ψ i
  let LF : Domain (n + 1) → Ambient q := fun y =>
    (∑ k : Fin (n + 1), (fderiv ℝ V y (EuclideanSpace.single k 1)) k) • w y
  let RG : Domain (n + 1) → Ambient q := fun y =>
    ∑ k : Fin (n + 1), V y k • Dw y k
  obtain ⟨hLF, hRG⟩ := weakGradient_vector_test_integrable hw hV hcV hsV
  have hMP := measurePreserving_native_polar_collar_cylinder_inverse hnpos hl r a b
  change MeasurePreserving Z ((σ.prod ν).prod η)
    (volume.restrict {y : Domain (n + 1) |
      (l < ‖(e y).1‖ ∧ ‖(e y).1‖ < r) ∧ (e y).2 0 ∈ Ioo a b}) at hMP
  rw [← hΩ] at hMP
  have hLFp : Integrable (LF ∘ Z) ((σ.prod ν).prod η) :=
    (hMP.integrable_comp hLF.aestronglyMeasurable).mpr hLF
  have hRGp : Integrable (RG ∘ Z) ((σ.prod ν).prod η) :=
    (hMP.integrable_comp hRG.aestronglyMeasurable).mpr hRG
  have hnorm (θ : sphere (0 : Domain n) 1) (ρ : Ioi (0 : ℝ)) :
      ‖ρ.val • θ.val‖ = ρ.val := by
    rw [norm_smul, Real.norm_of_nonneg ρ.property.le, mem_sphere_zero_iff_norm.mp θ.property, mul_one]
  have hunit (θ : sphere (0 : Domain n) 1) (ρ : Ioi (0 : ℝ)) :
      ‖ρ.val • θ.val‖⁻¹ • (ρ.val • θ.val) = θ.val := by
    rw [hnorm, smul_smul, inv_mul_cancel₀ ρ.property.ne', one_smul]
  have hFL : LF ∘ Z = F := by
    funext p
    have hx : p.2.val • p.1.1.val ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact p.2.property.ne')
    have hd := divergence_annularTestField hn s hβ hζ hψ hβ0 i
      (p.2.val • p.1.1.val) hx p.1.2
    dsimp only at hd
    rw [hunit, hnorm] at hd
    exact congrArg (fun z : ℝ => z • w (Z p)) hd
  have hGR : RG ∘ Z = G := by
    funext p
    have hd := annularTestField_gradient_contraction s β ζ ψ i Dw (p.2.val • p.1.1.val) p.1.2
    dsimp only at hd
    rw [hunit, hnorm] at hd
    have hsum : (∑ j : Fin n, (p.2.val • p.1.1.val) j • Dw (Z p) (Fin.castAdd 1 j)) =
        p.2.val • ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j) := by
      simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
    have hvec : p.2.val • Dw (Z p) (Fin.castAdd 1 i) -
        p.1.1.val i • (p.2.val • ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j)) =
        p.2.val • (Dw (Z p) (Fin.castAdd 1 i) -
          p.1.1.val i • ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j)) := by
      rw [smul_sub, smul_comm (p.1.1.val i) p.2.val]
    dsimp only [Z, e] at hsum hvec
    rw [hsum, hvec] at hd
    exact hd
  have hFI : Integrable F ((σ.prod ν).prod η) := hFL ▸ hLFp
  have hGI : Integrable G ((σ.prod ν).prod η) := hGR ▸ hRGp
  refine ⟨hFI, hGI, ?_⟩
  have hLFmap : (∫ p, LF (Z p) ∂((σ.prod ν).prod η)) = ∫ y in Ω.val, LF y := by
    have h := integral_map hMP.aemeasurable (hMP.map_eq.symm ▸ hLF.aestronglyMeasurable)
    rw [hMP.map_eq] at h
    exact h.symm
  have hRGmap : (∫ p, RG (Z p) ∂((σ.prod ν).prod η)) = ∫ y in Ω.val, RG y := by
    have h := integral_map hMP.aemeasurable (hMP.map_eq.symm ▸ hRG.aestronglyMeasurable)
    rw [hMP.map_eq] at h
    exact h.symm
  calc
    _ = ∫ p, F p ∂((σ.prod ν).prod η) := (integral_prod _ hFI).symm
    _ = ∫ y in Ω.val, LF y := by rw [← hFL]; exact hLFmap
    _ = -(∫ y in Ω.val, RG y) := hasWeakGradient_integral_divergence_test hw hV hcV hsV
    _ = -(∫ p, G p ∂((σ.prod ν).prod η)) := by rw [← hGR]; exact congrArg Neg.neg hRGmap.symm
    _ = _ := congrArg Neg.neg (integral_prod _ hGI)


/-- Actual finite cylinder-extension columns give native L2 radial averages
of the same weighted map, tangential spatial columns and temporal column. -/
theorem memLp_annular_averaged_columns_of_memW12 {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : MemW12 Ω w Dw)
    {δ a b : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (1 - δ < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < 1 + δ) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    {β : ℝ → ℝ} (hβ : Continuous β) (hcβ : HasCompactSupport β) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let μ := σ.prod (volume.restrict (Ioo a b))
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    let Z : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Domain (n + 1) := fun p =>
      e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)
    let W : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Ambient q :=
      fun p => β p.2.val • w (Z p)
    let A : Fin n → (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Ambient q :=
      fun i p => β p.2.val • p.2.val •
        (Dw (Z p) (Fin.castAdd 1 i) - p.1.1.val i •
          ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j))
    let B : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Ambient q :=
      fun p => β p.2.val • Dw (Z p) (Fin.natAdd n (0 : Fin 1))
    IsProbabilityMeasure P ∧ MemLp W 2 (μ.prod P) ∧
      (∀ i, MemLp (A i) 2 (μ.prod P)) ∧ MemLp B 2 (μ.prod P) ∧
      MemLp (fun p => ∫ ρ, W (p, ρ) ∂P) 2 μ ∧
      (∀ i, MemLp (fun p => ∫ ρ, A i (p, ρ) ∂P) 2 μ) ∧
      MemLp (fun p => ∫ ρ, B (p, ρ) ∂P) 2 μ := by
  intro e σ μ η P Z W A B
  have hmap := hw.2.1
  rw [hΩ] at hmap
  obtain ⟨hP, hrawW, _⟩ := memLp_two_native_radial_collar_average hn hδ hδsmall a b hmap
  letI : IsProbabilityMeasure P := hP
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  have hrawD (k : Fin (n + 1)) : MemLp (fun p => Dw (Z p) k) 2 (μ.prod P) := by
    have hcolumn := hw.2.2 k
    rw [hΩ] at hcolumn
    exact (memLp_two_native_radial_collar_average hn hδ hδsmall a b hcolumn).2.1
  have hβP : MemLp (fun ρ : Ioi (0 : ℝ) => β ρ.val) ∞ P :=
    (hβ.memLp_top_of_hasCompactSupport hcβ
      (Measure.map (Subtype.val : Ioi (0 : ℝ) → ℝ) P)).comp_of_map
        measurable_subtype_coe.aemeasurable
  have hβprod : MemLp (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) => β p.2.val)
      ∞ (μ.prod P) := hβP.comp_snd μ
  have hJ : MeasurableSet {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ} :=
    (isOpen_Ioo.preimage continuous_subtype_val).measurableSet
  have hAE : ∀ᵐ ρ ∂P, 1 - δ < ρ.val ∧ ρ.val < 1 + δ :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem hJ)
  have hρP : MemLp (fun ρ : Ioi (0 : ℝ) => ρ.val) ∞ P := by
    apply memLp_top_of_bound measurable_subtype_coe.aestronglyMeasurable 2
    filter_upwards [hAE] with ρ hρ
    rw [Real.norm_of_nonneg ρ.property.le]
    linarith only [hρ.2, hδsmall]
  have hρprod := hρP.comp_snd μ
  have hθ (j : Fin n) : MemLp
      (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) => p.1.1.val j) ∞ (μ.prod P) := by
    have hbase : MemLp (fun θ : sphere (0 : Domain n) 1 => θ.val j) ∞ σ := by
      apply memLp_top_of_bound
        ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp continuous_subtype_val).aestronglyMeasurable 1
      exact Eventually.of_forall fun θ =>
        (PiLp.norm_apply_le θ.val j).trans_eq (mem_sphere_zero_iff_norm.mp θ.property)
    exact (hbase.comp_fst (volume.restrict (Ioo a b))).comp_fst P
  have hsum : MemLp (fun p => ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j))
      2 (μ.prod P) :=
    memLp_finsetSum Finset.univ (fun j _ => (hrawD (Fin.castAdd 1 j)).smul (hθ j))
  have hW : MemLp W 2 (μ.prod P) := hrawW.smul hβprod
  have hT (i : Fin n) : MemLp (fun p => Dw (Z p) (Fin.castAdd 1 i) -
      p.1.1.val i • ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j)) 2 (μ.prod P) :=
    (hrawD (Fin.castAdd 1 i)).sub (hsum.smul (hθ i))
  have hρT (i : Fin n) : MemLp (fun p => p.2.val • (Dw (Z p) (Fin.castAdd 1 i) -
      p.1.1.val i • ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j))) 2 (μ.prod P) :=
    (hT i).smul hρprod
  have hA (i : Fin n) : MemLp (A i) 2 (μ.prod P) := (hρT i).smul hβprod
  have hB : MemLp B 2 (μ.prod P) := (hrawD (Fin.natAdd n (0 : Fin 1))).smul hβprod
  exact ⟨hP, hW, hA, hB, (memLp_two_probability_average hW).1,
    fun i => (memLp_two_probability_average (hA i)).1, (memLp_two_probability_average hB).1⟩


private theorem native_sphere_time_continuous_memLp_top {n : ℕ} {a b : ℝ}
    {f : sphere (0 : Domain n) 1 × ℝ → ℝ} (hf : Continuous f) :
    MemLp f ∞ ((Measure.euclideanHausdorffMeasure (n - 1) :
      Measure (sphere (0 : Domain n) 1)).prod (volume.restrict (Ioo a b))) := by
  have hK : IsCompact ((univ : Set (sphere (0 : Domain n) 1)) ×ˢ Icc a b) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply memLp_top_of_bound hf.aestronglyMeasurable C
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem (measurableSet_Ioo (a := a) (b := b)))] with p hp
  exact hC p ⟨mem_univ _, Ioo_subset_Icc_self hp⟩

/-- Averaging the original full extension over a smooth radial cutoff gives
native sphere-time weak identities for its actual L2 tangential and time columns. -/
theorem annular_averaged_columns_weak_identity {n q : ℕ} (hn : 2 ≤ n) (s : ℝ)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : MemW12 Ω w Dw)
    {δ a b : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (1 - δ < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < 1 + δ) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    {β ζ : ℝ → ℝ} {ψ : Domain n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ)
    (hcβ : HasCompactSupport β) (hcζ : HasCompactSupport ζ)
    (hsβ : tsupport β ⊆ Ioo (1 - δ) (1 + δ)) (hsζ : tsupport ζ ⊆ Ioo a b) (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let μ := σ.prod (volume.restrict (Ioo a b))
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    let Z : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Domain (n + 1) := fun p =>
      e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)
    let W := fun p : sphere (0 : Domain n) 1 × ℝ => ∫ ρ : Ioi (0 : ℝ), β ρ.val • w (Z (p, ρ)) ∂P
    let A := fun p : sphere (0 : Domain n) 1 × ℝ => ∫ ρ : Ioi (0 : ℝ), β ρ.val • ρ.val •
      (Dw (Z (p, ρ)) (Fin.castAdd 1 i) - p.1.val i •
        ∑ j : Fin n, p.1.val j • Dw (Z (p, ρ)) (Fin.castAdd 1 j)) ∂P
    let B := fun p : sphere (0 : Domain n) 1 × ℝ =>
      ∫ ρ : Ioi (0 : ℝ), β ρ.val • Dw (Z (p, ρ)) (Fin.natAdd n (0 : Fin 1)) ∂P
    let D := fun p : sphere (0 : Domain n) 1 × ℝ =>
      let L := s * (1 + p.2)
      s * L ^ (n - 1) * ζ p.2 * coordinateDerivative ψ hψ i (L • p.1.val) +
        L ^ (n - 1) * deriv ζ p.2 * ψ (L • p.1.val) * p.1.val i
    let S := fun p : sphere (0 : Domain n) 1 × ℝ =>
      s * (s * (1 + p.2)) ^ (n - 2) * ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val)
    let T := fun p : sphere (0 : Domain n) 1 × ℝ =>
      (s * (1 + p.2)) ^ (n - 1) * ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i
    Integrable (fun p => D p • W p) μ ∧ Integrable (fun p => S p • A p + T p • B p) μ ∧
      (∫ p, D p • W p ∂μ) = -(∫ p, S p • A p + T p • B p ∂μ) := by
  intro e σ μ η P Z W A B D S T
  have hnpos : 0 < n := by omega
  have hdata := memLp_annular_averaged_columns_of_memW12 hnpos hw hδ hδsmall hΩ hβ.continuous hcβ
  obtain ⟨hP, _hWL, hAL, hBL, hWA, hAA, hBA⟩ := hdata
  letI : IsProbabilityMeasure P := hP
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos]
    infer_instance
  have harg : Continuous (fun p : sphere (0 : Domain n) 1 × ℝ => (s * (1 + p.2)) • p.1.val) := by
    fun_prop
  have hψD : Continuous (coordinateDerivative ψ hψ i) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hζD : Continuous (deriv ζ) := hζ.continuous_deriv (by simp)
  have hDC : Continuous D := by
    dsimp only [D]
    fun_prop
  have hSC : Continuous S := by
    dsimp only [S]
    fun_prop
  have hTC : Continuous T := by
    dsimp only [T]
    fun_prop
  have hDL : MemLp D ∞ μ := native_sphere_time_continuous_memLp_top hDC
  have hSL : MemLp S ∞ μ := native_sphere_time_continuous_memLp_top hSC
  have hTL : MemLp T ∞ μ := native_sphere_time_continuous_memLp_top hTC
  have hDW : MemLp (fun p => D p • W p) 2 μ := hWA.smul hDL
  have hSA : MemLp (fun p => S p • A p) 2 μ := (hAA i).smul hSL
  have hTB : MemLp (fun p => T p • B p) 2 μ := hBA.smul hTL
  have hLInt : Integrable (fun p => D p • W p) μ := hDW.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hRInt : Integrable (fun p => S p • A p + T p • B p) μ :=
    (hSA.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).add (hTB.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  obtain ⟨_hFη, _hGη, hrawη⟩ := annular_test_field_native_polar_identity hn s hw.1
    (by linarith : 0 < 1 - δ) hΩ hβ hζ hψ hcβ hcζ hsβ hsζ i
  have hFC (p : sphere (0 : Domain n) 1 × ℝ) (ρ : Ioi (0 : ℝ)) :
      s * (s * (1 + p.2)) ^ (n - 1) * β ρ.val * ζ p.2 *
          coordinateDerivative ψ hψ i ((s * (1 + p.2)) • p.1.val) +
        (s * (1 + p.2)) ^ (n - 1) * β ρ.val * deriv ζ p.2 *
          ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i = D p * β ρ.val := by dsimp only [D]; ring
  have hSC' (p : sphere (0 : Domain n) 1 × ℝ) (ρ : Ioi (0 : ℝ)) :
      s * (s * (1 + p.2)) ^ (n - 2) * ζ p.2 * β ρ.val *
        ψ ((s * (1 + p.2)) • p.1.val) = S p * β ρ.val := by dsimp only [S]; ring
  have hTC' (p : sphere (0 : Domain n) 1 × ℝ) (ρ : Ioi (0 : ℝ)) :
      (s * (1 + p.2)) ^ (n - 1) * β ρ.val * ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val) *
        p.1.val i = T p * β ρ.val := by dsimp only [T]; ring
  simp_rw [hFC, hSC', hTC', mul_smul] at hrawη
  let F0 := fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
    D p.1 • (β p.2.val • w (Z p))
  let G0 := fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
    S p.1 • (β p.2.val • p.2.val • (Dw (Z p) (Fin.castAdd 1 i) - p.1.1.val i •
      ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j))) +
    T p.1 • (β p.2.val • Dw (Z p) (Fin.natAdd n (0 : Fin 1)))
  change (∫ p, (∫ ρ, F0 (p, ρ) ∂η) ∂μ) = -(∫ p, (∫ ρ, G0 (p, ρ) ∂η) ∂μ) at hrawη
  have hrawP : (∫ p, (∫ ρ, F0 (p, ρ) ∂P) ∂μ) = -(∫ p, (∫ ρ, G0 (p, ρ) ∂P) ∂μ) := by
    simp only [P, integral_smul_measure, integral_smul, hrawη, smul_neg]
  have hSInt : Integrable (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
      S p.1 • (β p.2.val • p.2.val • (Dw (Z p) (Fin.castAdd 1 i) - p.1.1.val i •
        ∑ j : Fin n, p.1.1.val j • Dw (Z p) (Fin.castAdd 1 j)))) (μ.prod P) :=
    ((hAL i).smul (hSL.comp_fst P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hTInt : Integrable (fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
      T p.1 • (β p.2.val • Dw (Z p) (Fin.natAdd n (0 : Fin 1)))) (μ.prod P) :=
    (hBL.smul (hTL.comp_fst P)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hleft : (∫ p, (∫ ρ, F0 (p, ρ) ∂P) ∂μ) = ∫ p, D p • W p ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => integral_smul (D p) _
  have hright : (∫ p, (∫ ρ, G0 (p, ρ) ∂P) ∂μ) = ∫ p, S p • A p + T p • B p ∂μ := by
    apply integral_congr_ae
    filter_upwards [hSInt.prod_right_ae, hTInt.prod_right_ae] with p hp hq
    rw [integral_add hp hq, integral_smul, integral_smul]
  exact ⟨hLInt, hRInt, by rw [← hleft, ← hright]; exact hrawP⟩


/-- Every genuine radial collar admits a smooth nonnegative compact cutoff
whose average against its native radial probability measure is exactly one. -/
theorem exists_normalized_smooth_radial_weight {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) :
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    IsProbabilityMeasure P ∧ ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Ioo (1 - δ) (1 + δ) ∧ (∀ t, 0 ≤ β t) ∧
      (∫ ρ : Ioi (0 : ℝ), β ρ.val ∂P) = 1 := by
  intro η P
  let J : Set (Ioi (0 : ℝ)) := {ρ | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
  obtain ⟨hpos, hfinite⟩ := radial_collar_jacobian_mass_finite_pos (n := n) hδ
  have hmass : η univ = Measure.volumeIoiPow (n - 1) J := Measure.restrict_apply_univ J
  letI : IsFiniteMeasure η := ⟨by rw [hmass]; exact hfinite.lt_top⟩
  letI : NeZero η := ⟨by
    intro hz
    have hzero := congrArg (fun ν : Measure (Ioi (0 : ℝ)) => ν univ) hz
    rw [hmass] at hzero
    have hηzero : η univ = 0 := by rw [hz]; rfl
    exact hpos.ne' (hmass.symm.trans hηzero)⟩
  letI : IsProbabilityMeasure P := inferInstance
  obtain ⟨β₀, hsβ₀, hcβ₀, hβ₀, hvalues, hβ₀one⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (isOpen_Ioo.mem_nhds (show (1 : ℝ) ∈ Ioo (1 - δ) (1 + δ) from
        ⟨by linarith only [hδ], by linarith only [hδ]⟩))
  have hnonneg (t : ℝ) : 0 ≤ β₀ t := (hvalues (mem_range_self t)).1
  have hβ₀P : MemLp (fun ρ : Ioi (0 : ℝ) => β₀ ρ.val) ∞ P := by
    apply memLp_top_of_bound (hβ₀.continuous.comp continuous_subtype_val).aestronglyMeasurable 1
    exact Eventually.of_forall fun ρ => by
      change ‖β₀ ρ.val‖ ≤ 1
      rw [Real.norm_of_nonneg (hnonneg ρ.val)]
      exact (hvalues (mem_range_self ρ.val)).2
  have hβ₀I : Integrable (fun ρ : Ioi (0 : ℝ) => β₀ ρ.val) P :=
    hβ₀P.integrable (by simp)
  let S : Set (Ioi (0 : ℝ)) := Function.support (fun ρ : Ioi (0 : ℝ) => β₀ ρ.val)
  have hS : IsOpen S := isOpen_ne_fun (hβ₀.continuous.comp continuous_subtype_val) continuous_const
  have hSnonempty : S.Nonempty := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    change β₀ 1 ≠ 0
    rw [hβ₀one]
    norm_num
  have hSJ : S ⊆ J := fun ρ hρ => hsβ₀ (subset_tsupport β₀ hρ)
  have hνpos : 0 < Measure.volumeIoiPow (n - 1) S := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hae := (ae_volumeIoiPow_iff (n - 1)).mp (measure_eq_zero_iff_ae_notMem.mp hzero)
    have hbasezero := measure_eq_zero_iff_ae_notMem.mpr hae
    letI : Measure.IsOpenPosMeasure (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
      Measure.IsOpenPosMeasure.comap volume isOpen_Ioi.isOpenEmbedding_subtypeVal
    exact (hS.measure_pos _ hSnonempty).ne' hbasezero
  have hPpos : 0 < P S := by
    change 0 < ((η univ)⁻¹ • η) S
    rw [Measure.smul_apply, Measure.restrict_apply hS.measurableSet,
      inter_eq_left.mpr hSJ, smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.inv_pos.mpr (by rw [hmass]; exact hfinite)).ne' hνpos.ne'
  let m : ℝ := ∫ ρ : Ioi (0 : ℝ), β₀ ρ.val ∂P
  have hm : 0 < m := (integral_pos_iff_support_of_nonneg
    (fun ρ : Ioi (0 : ℝ) => hnonneg ρ.val) hβ₀I).mpr hPpos
  let β : ℝ → ℝ := fun t => m⁻¹ * β₀ t
  have hsupport : tsupport β ⊆ tsupport β₀ := by
    apply closure_mono
    intro t ht hz
    exact ht (by change m⁻¹ * β₀ t = 0; rw [hz, mul_zero])
  refine ⟨inferInstance, β, contDiff_const.mul hβ₀,
    hcβ₀.of_isClosed_subset (isClosed_tsupport _) hsupport,
    hsupport.trans hsβ₀, fun t => mul_nonneg (inv_nonneg.mpr hm.le) (hnonneg t), ?_⟩
  change (∫ ρ : Ioi (0 : ℝ), m⁻¹ * β₀ ρ.val ∂P) = 1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ hm.ne'


/-- Actual compact annular tests remove the temporal cutoff and retain the
same radial averages of the original map and full weak columns. -/
theorem annular_averaged_columns_test_identity {n q : ℕ} (hn : 2 ≤ n)
    {s a b : ℝ} (hab : a < b) (ha : -1 < a) (hs : 0 < s)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : MemW12 Ω w Dw)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (1 - δ < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < 1 + δ) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hsβ : tsupport β ⊆ Ioo (1 - δ) (1 + δ))
    {ψ : Domain n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ {x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)}) (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    let μ := σ.prod (volume.restrict (Ioo a b))
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    let Z : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) → Domain (n + 1) := fun p =>
      e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)
    let W := fun p : sphere (0 : Domain n) 1 × ℝ => ∫ ρ : Ioi (0 : ℝ), β ρ.val • w (Z (p, ρ)) ∂P
    let A := fun p : sphere (0 : Domain n) 1 × ℝ => ∫ ρ : Ioi (0 : ℝ), β ρ.val • ρ.val •
      (Dw (Z (p, ρ)) (Fin.castAdd 1 i) - p.1.val i •
        ∑ j : Fin n, p.1.val j • Dw (Z (p, ρ)) (Fin.castAdd 1 j)) ∂P
    let B := fun p : sphere (0 : Domain n) 1 × ℝ =>
      ∫ ρ : Ioi (0 : ℝ), β ρ.val • Dw (Z (p, ρ)) (Fin.natAdd n (0 : Fin 1)) ∂P
    let D := fun p : sphere (0 : Domain n) 1 × ℝ =>
      s * (s * (1 + p.2)) ^ (n - 1) * coordinateDerivative ψ hψ i ((s * (1 + p.2)) • p.1.val)
    let S := fun p : sphere (0 : Domain n) 1 × ℝ =>
      s * (s * (1 + p.2)) ^ (n - 2) * ψ ((s * (1 + p.2)) • p.1.val)
    let T := fun p : sphere (0 : Domain n) 1 × ℝ =>
      (s * (1 + p.2)) ^ (n - 1) * ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i
    Integrable (fun p => D p • W p) μ ∧ Integrable (fun p => S p • A p + T p • B p) μ ∧
      (∫ p, D p • W p ∂μ) = -(∫ p, S p • A p + T p • B p ∂μ) := by
  intro e σ μ η P Z W A B D S T
  obtain ⟨ζ, hζ, hcζ, hsζ, hcut⟩ := exists_annular_time_test_cutoff hab ha hs hψ hcψ hsψ
  obtain ⟨hLI, hRI, hEq⟩ := annular_averaged_columns_weak_identity hn s hw hδ hδsmall hΩ
    hβ hζ hψ hcβ hcζ hsβ hsζ i
  let Dζ := fun p : sphere (0 : Domain n) 1 × ℝ =>
    s * (s * (1 + p.2)) ^ (n - 1) * ζ p.2 * coordinateDerivative ψ hψ i ((s * (1 + p.2)) • p.1.val) +
      (s * (1 + p.2)) ^ (n - 1) * deriv ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i
  let Sζ := fun p : sphere (0 : Domain n) 1 × ℝ =>
    s * (s * (1 + p.2)) ^ (n - 2) * ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val)
  let Tζ := fun p : sphere (0 : Domain n) 1 × ℝ =>
    (s * (1 + p.2)) ^ (n - 1) * ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i
  change Integrable (fun p => Dζ p • W p) μ at hLI
  change Integrable (fun p => Sζ p • A p + Tζ p • B p) μ at hRI
  change (∫ p, Dζ p • W p ∂μ) = -(∫ p, Sζ p • A p + Tζ p • B p ∂μ) at hEq
  have hD (p : sphere (0 : Domain n) 1 × ℝ) (hp : p.2 ∈ Ioo a b) : Dζ p = D p := by
    have h := hcut p.1 p.2 hp
    calc
      _ = s * (s * (1 + p.2)) ^ (n - 1) *
          (ζ p.2 * coordinateDerivative ψ hψ i ((s * (1 + p.2)) • p.1.val)) +
        (s * (1 + p.2)) ^ (n - 1) * (deriv ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val)) * p.1.val i := by
          dsimp only [Dζ]
          ring
      _ = _ := by rw [h.2.2 i, h.2.1, mul_zero, zero_mul, add_zero]
  have hS (p : sphere (0 : Domain n) 1 × ℝ) (hp : p.2 ∈ Ioo a b) : Sζ p = S p := by
    have h := (hcut p.1 p.2 hp).1
    calc
      _ = s * (s * (1 + p.2)) ^ (n - 2) * (ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val)) := by
        dsimp only [Sζ]
        ring
      _ = _ := by rw [h]
  have hT (p : sphere (0 : Domain n) 1 × ℝ) (hp : p.2 ∈ Ioo a b) : Tζ p = T p := by
    have h := (hcut p.1 p.2 hp).1
    calc
      _ = (s * (1 + p.2)) ^ (n - 1) * (ζ p.2 * ψ ((s * (1 + p.2)) • p.1.val)) * p.1.val i := by
        dsimp only [Tζ]
        ring
      _ = _ := by rw [h]
  have hLAE : (fun p => Dζ p • W p) =ᵐ[μ] (fun p => D p • W p) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (measurableSet_Ioo (a := a) (b := b)))] with p hp
    rw [hD p hp]
  have hRAE : (fun p => Sζ p • A p + Tζ p • B p) =ᵐ[μ]
      (fun p => S p • A p + T p • B p) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (measurableSet_Ioo (a := a) (b := b)))] with p hp
    rw [hS p hp, hT p hp]
  exact ⟨hLI.congr hLAE, hRI.congr hRAE, by
    rw [← integral_congr_ae hLAE, ← integral_congr_ae hRAE]
    exact hEq⟩


/-- Translation preserves the actual finite Sobolev map and all its original
weak columns on any finite-volume open domain. -/
theorem memW12_translate_finite_openDomain {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hfinite : volume Ω.val ≠ ⊤) (c : Domain n) :
    MemW12 ⟨{x : Domain n | x - c ∈ Ω.val},
      Ω.property.preimage (continuous_id.sub continuous_const)⟩
      (fun x => u (x - c)) (fun x i => Du (x - c) i) := by
  let V : OpenDomain n := ⟨{x : Domain n | x - c ∈ Ω.val},
    Ω.property.preimage (continuous_id.sub continuous_const)⟩
  have hMP := (measurePreserving_sub_right (volume : Measure (Domain n)) c).restrict_preimage
    Ω.property.measurableSet
  change MeasurePreserving (fun x : Domain n => x - c)
    (volume.restrict V.val) (volume.restrict Ω.val) at hMP
  have hM : MemLp (fun x => u (x - c)) 2 (volume.restrict V.val) :=
    hu.2.1.comp_measurePreserving hMP
  have hD (i : Fin n) : MemLp (fun x => Du (x - c) i) 2 (volume.restrict V.val) :=
    (hu.2.2 i).comp_measurePreserving hMP
  have hfiniteV : volume V.val ≠ ⊤ := by
    change volume ((fun x : Domain n => x - c) ⁻¹' Ω.val) ≠ ⊤
    rw [(measurePreserving_sub_right (volume : Measure (Domain n)) c).measure_preimage
      Ω.property.measurableSet.nullMeasurableSet]
    exact hfinite
  letI : IsFiniteMeasure (volume.restrict V.val) := isFiniteMeasure_restrict.mpr hfiniteV
  have hMI : IntegrableOn (fun x => u (x - c)) V.val := hM.integrable (by norm_num)
  have hDI (i : Fin n) : IntegrableOn (fun x => Du (x - c) i) V.val :=
    (hD i).integrable (by norm_num)
  refine ⟨⟨hMI.locallyIntegrableOn, fun i => (hDI i).locallyIntegrableOn, ?_⟩, hM, hD⟩
  intro i φ hφ hcφ hsφ
  let ψ : Domain n → ℝ := fun z => φ (c + z)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_const.add contDiff_id)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph (Homeomorph.addLeft c)
  have hsψ : tsupport ψ ⊆ Ω.val := by
    have hpre := tsupport_comp_subset_preimage φ ((continuous_const (y := c)).add continuous_id)
    intro z hz
    have hmem := hsφ (hpre hz)
    change c + z - c ∈ Ω.val at hmem
    simpa only [add_sub_cancel_left] using hmem
  have hder (x : Domain n) : coordinateDerivative ψ hψ i (x - c) =
      coordinateDerivative φ hφ i x := by
    change fderiv ℝ (fun z => φ (c + z)) (x - c) (EuclideanSpace.single i 1) = _
    rw [fderiv_comp_add_left]
    have hx : c + (x - c) = x := by abel
    rw [hx]
    rfl
  have htest := hu.1.2.2 i ψ hψ hcψ hsψ
  have hLI := hu.1.integrable_test_derivative i hψ hcψ hsψ
  have hRI := hu.1.integrable_test_gradient i hψ hcψ hsψ
  have hLM : (∫ x in V.val, coordinateDerivative ψ hψ i (x - c) • u (x - c)) =
      ∫ z in Ω.val, coordinateDerivative ψ hψ i z • u z := by
    have h := integral_map hMP.aemeasurable (hMP.map_eq.symm ▸ hLI.aestronglyMeasurable)
    rw [hMP.map_eq] at h
    exact h.symm
  have hRM : (∫ x in V.val, ψ (x - c) • Du (x - c) i) =
      ∫ z in Ω.val, ψ z • Du z i := by
    have h := integral_map hMP.aemeasurable (hMP.map_eq.symm ▸ hRI.aestronglyMeasurable)
    rw [hMP.map_eq] at h
    exact h.symm
  rw [← hLM, ← hRM] at htest
  simp_rw [hder] at htest
  have heq (x : Domain n) : ψ (x - c) = φ x := by
    dsimp only [ψ]
    congr 1
    abel
  simp_rw [heq] at htest
  exact htest


/-- The literal radial average of an ambient cylinder extension in annular
coordinates; every value is given by the same integral formula. -/
@[expose] noncomputable def annularAveragedMap {n q : ℕ} (s : ℝ)
    (β : ℝ → ℝ) (P : Measure (Ioi (0 : ℝ)))
    (w : Domain (n + 1) → Ambient q) (x : Domain n) : Ambient q :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  ∫ ρ, β ρ.val • w (e.symm (ρ.val • (‖x‖⁻¹ • x),
    EuclideanSpace.single (0 : Fin 1) (‖x‖ / s - 1))) ∂P

/-- Actual averaged spatial tangential and temporal columns in annular
coordinates. The original ambient columns are averaged over radial volume. -/
@[expose] noncomputable def annularAveragedColumns {n q : ℕ} (s : ℝ)
    (β : ℝ → ℝ) (P : Measure (Ioi (0 : ℝ)))
    (Dw : Domain (n + 1) → Gradient (n + 1) q) (x : Domain n) : Gradient n q :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let θ := ‖x‖⁻¹ • x
  let Z := fun ρ : Ioi (0 : ℝ) => e.symm (ρ.val • θ,
    EuclideanSpace.single (0 : Fin 1) (‖x‖ / s - 1))
  fun i => ‖x‖⁻¹ • (∫ ρ, β ρ.val • ρ.val •
    (Dw (Z ρ) (Fin.castAdd 1 i) - θ i • ∑ j : Fin n, θ j • Dw (Z ρ) (Fin.castAdd 1 j)) ∂P) +
    (s⁻¹ * θ i) • ∫ ρ, β ρ.val • Dw (Z ρ) (Fin.natAdd n (0 : Fin 1)) ∂P

/-- Positive annular parameters recover precisely the same radial average
of the original cylinder extension. -/
theorem annularAveragedMap_param {n q : ℕ} {s t : ℝ} (hs : 0 < s) (ht : -1 < t)
    (β : ℝ → ℝ) (P : Measure (Ioi (0 : ℝ))) (w : Domain (n + 1) → Ambient q)
    (θ : sphere (0 : Domain n) 1) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    annularAveragedMap s β P w ((s * (1 + t)) • θ.val) =
      ∫ ρ, β ρ.val • w (e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)) ∂P := by
  intro e
  have hrad : 0 < s * (1 + t) := mul_pos hs (by linarith only [ht])
  have hnorm : ‖(s * (1 + t)) • θ.val‖ = s * (1 + t) := by
    rw [norm_smul, Real.norm_of_nonneg hrad.le, mem_sphere_zero_iff_norm.mp θ.property, mul_one]
  have hunit : ‖(s * (1 + t)) • θ.val‖⁻¹ • ((s * (1 + t)) • θ.val) = θ.val := by
    rw [hnorm, smul_smul, inv_mul_cancel₀ hrad.ne', one_smul]
  have htime : ‖(s * (1 + t)) • θ.val‖ / s - 1 = t := by
    rw [hnorm]
    field_simp
    ring
  unfold annularAveragedMap
  rw [hunit, htime]

/-- The actual averaged annular columns pull back to the same native
spatial tangential average divided by radius and time average divided by scale. -/
theorem annularAveragedColumns_param {n q : ℕ} {s t : ℝ} (hs : 0 < s) (ht : -1 < t)
    (β : ℝ → ℝ) (P : Measure (Ioi (0 : ℝ))) (Dw : Domain (n + 1) → Gradient (n + 1) q)
    (θ : sphere (0 : Domain n) 1) (i : Fin n) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let Z := fun ρ : Ioi (0 : ℝ) => e.symm (ρ.val • θ.val, EuclideanSpace.single (0 : Fin 1) t)
    annularAveragedColumns s β P Dw ((s * (1 + t)) • θ.val) i =
      (s * (1 + t))⁻¹ • (∫ ρ, β ρ.val • ρ.val •
        (Dw (Z ρ) (Fin.castAdd 1 i) - θ.val i •
          ∑ j : Fin n, θ.val j • Dw (Z ρ) (Fin.castAdd 1 j)) ∂P) +
      (s⁻¹ * θ.val i) • ∫ ρ, β ρ.val • Dw (Z ρ) (Fin.natAdd n (0 : Fin 1)) ∂P := by
  intro e Z
  have hrad : 0 < s * (1 + t) := mul_pos hs (by linarith only [ht])
  have hnorm : ‖(s * (1 + t)) • θ.val‖ = s * (1 + t) := by
    rw [norm_smul, Real.norm_of_nonneg hrad.le, mem_sphere_zero_iff_norm.mp θ.property, mul_one]
  have hunit : ‖(s * (1 + t)) • θ.val‖⁻¹ • ((s * (1 + t)) • θ.val) = θ.val := by
    rw [hnorm, smul_smul, inv_mul_cancel₀ hrad.ne', one_smul]
  have htime : ‖(s * (1 + t)) • θ.val‖ / s - 1 = t := by
    rw [hnorm]
    field_simp
    ring
  unfold annularAveragedColumns
  rw [hunit, htime, hnorm]


/-- A genuine full finite cylinder extension gives an actual Sobolev map on
the annulus by radial averaging, with the displayed averaged weak columns. -/
theorem memW12_annularAveragedMap {n q : ℕ} (hn : 2 ≤ n)
    {s a b : ℝ} (hab : a < b) (ha : -1 < a) (hs : 0 < s)
    {Ω : OpenDomain (n + 1)} {w : Domain (n + 1) → Ambient q}
    {Dw : Domain (n + 1) → Gradient (n + 1) q} (hw : MemW12 Ω w Dw)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 2)
    (hΩ : Ω.val = {y : Domain (n + 1) |
      (1 - δ < ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ ∧
        ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).1‖ < 1 + δ) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) y).2 0 ∈ Ioo a b})
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hsβ : tsupport β ⊆ Ioo (1 - δ) (1 + δ)) :
    let η := (Measure.volumeIoiPow (n - 1)).restrict
      {ρ : Ioi (0 : ℝ) | 1 - δ < ρ.val ∧ ρ.val < 1 + δ}
    let P := (η univ)⁻¹ • η
    MemW12 ⟨{x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)},
      isOpen_Ioo.preimage continuous_norm⟩
      (annularAveragedMap s β P w) (annularAveragedColumns s β P Dw) := by
  intro η P
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let μ := σ.prod (volume.restrict (Ioo a b))
  let Z := fun p : (sphere (0 : Domain n) 1 × ℝ) × Ioi (0 : ℝ) =>
    e.symm (p.2.val • p.1.1.val, EuclideanSpace.single (0 : Fin 1) p.1.2)
  let F := fun p : sphere (0 : Domain n) 1 × ℝ => ∫ ρ : Ioi (0 : ℝ), β ρ.val • w (Z (p, ρ)) ∂P
  let A := fun i : Fin n => fun p : sphere (0 : Domain n) 1 × ℝ =>
    ∫ ρ : Ioi (0 : ℝ), β ρ.val • ρ.val • (Dw (Z (p, ρ)) (Fin.castAdd 1 i) - p.1.val i •
      ∑ j : Fin n, p.1.val j • Dw (Z (p, ρ)) (Fin.castAdd 1 j)) ∂P
  let B := fun p : sphere (0 : Domain n) 1 × ℝ =>
    ∫ ρ : Ioi (0 : ℝ), β ρ.val • Dw (Z (p, ρ)) (Fin.natAdd n (0 : Fin 1)) ∂P
  let U := annularAveragedMap s β P w
  let DU := annularAveragedColumns s β P Dw
  let V : OpenDomain n := ⟨{x : Domain n | s * (1 + a) < ‖x‖ ∧ ‖x‖ < s * (1 + b)},
    isOpen_Ioo.preimage continuous_norm⟩
  have hnpos : 0 < n := by omega
  obtain ⟨hP, _hW, _hA, _hB, hFL, hAL, hBL⟩ :=
    memLp_annular_averaged_columns_of_memW12 hnpos hw hδ hδsmall hΩ hβ.continuous hcβ
  letI : IsProbabilityMeasure P := hP
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hnpos]
    infer_instance
  have htime : ∀ᵐ p : sphere (0 : Domain n) 1 × ℝ ∂μ, p.2 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  have hMap (p : sphere (0 : Domain n) 1 × ℝ) (hp : p.2 ∈ Ioo a b) :
      U ((s * (1 + p.2)) • p.1.val) = F p :=
    annularAveragedMap_param hs (ha.trans hp.1) β P w p.1
  have hCol (p : sphere (0 : Domain n) 1 × ℝ) (hp : p.2 ∈ Ioo a b) (i : Fin n) :
      DU ((s * (1 + p.2)) • p.1.val) i =
        (s * (1 + p.2))⁻¹ • A i p + (s⁻¹ * p.1.val i) • B p :=
    annularAveragedColumns_param hs (ha.trans hp.1) β P Dw p.1 i
  have hFparam : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
      U ((s * (1 + p.2)) • p.1.val)) 2 μ := by
    apply hFL.ae_eq
    filter_upwards [htime] with p hp
    exact (hMap p hp).symm
  have hUL : MemLp U 2 (volume.restrict V.val) :=
    (memLp_two_annulus_of_cylinder_pullback hnpos hs ha hab U hFparam).1
  have hlo : 0 < s * (1 + a) := mul_pos hs (by linarith only [ha])
  have hinv : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => (s * (1 + p.2))⁻¹) ∞ μ := by
    have hC : Continuous (fun p : sphere (0 : Domain n) 1 × ℝ => s * (1 + p.2)) := by fun_prop
    apply memLp_top_of_bound hC.aestronglyMeasurable.inv₀ ((s * (1 + a))⁻¹)
    filter_upwards [htime] with p hp
    have hL : 0 < s * (1 + p.2) := mul_pos hs (by linarith only [ha, hp.1])
    change ‖(s * (1 + p.2))⁻¹‖ ≤ (s * (1 + a))⁻¹
    rw [norm_inv, Real.norm_of_nonneg hL.le]
    apply (inv_le_inv₀ hL hlo).mpr
    apply mul_le_mul_of_nonneg_left _ hs.le
    linarith only [hp.1]
  have hθS (i : Fin n) : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ => s⁻¹ * p.1.val i) ∞ μ :=
    native_sphere_time_continuous_memLp_top (by fun_prop)
  have hDparam (i : Fin n) : MemLp (fun p : sphere (0 : Domain n) 1 × ℝ =>
      DU ((s * (1 + p.2)) • p.1.val) i) 2 μ := by
    have hL : MemLp (fun p => (s * (1 + p.2))⁻¹ • A i p + (s⁻¹ * p.1.val i) • B p) 2 μ :=
      ((hAL i).smul hinv).add (hBL.smul (hθS i))
    apply hL.ae_eq
    filter_upwards [htime] with p hp
    exact (hCol p hp i).symm
  have hDUL (i : Fin n) : MemLp (fun x => DU x i) 2 (volume.restrict V.val) :=
    (memLp_two_annulus_of_cylinder_pullback hnpos hs ha hab (fun x => DU x i) (hDparam i)).1
  have hfinite : volume V.val ≠ ⊤ := by
    have hballfinite : volume (ball (0 : Domain n) (s * (1 + b))) ≠ ⊤ := measure_ball_ne_top
    apply ne_top_of_le_ne_top hballfinite
    apply measure_mono
    intro x hx
    exact (show x ∈ ball (0 : Domain n) (s * (1 + b)) from by
      rw [mem_ball, dist_zero_right]
      exact hx.2)
  letI : IsFiniteMeasure (volume.restrict V.val) := isFiniteMeasure_restrict.mpr hfinite
  have hUI : IntegrableOn U V.val := hUL.integrable (by norm_num)
  have hDUI (i : Fin n) : IntegrableOn (fun x => DU x i) V.val := (hDUL i).integrable (by norm_num)
  change MemW12 V U DU
  refine ⟨⟨hUI.locallyIntegrableOn, fun i => (hDUI i).locallyIntegrableOn, ?_⟩, hUL, hDUL⟩
  intro i ψ hψ hcψ hsψ
  have hNative :
      (∫ p : sphere (0 : Domain n) 1 × ℝ,
        (s * (s * (1 + p.2)) ^ (n - 1) * coordinateDerivative ψ hψ i ((s * (1 + p.2)) • p.1.val)) • F p ∂μ) =
      -(∫ p : sphere (0 : Domain n) 1 × ℝ,
        (s * (s * (1 + p.2)) ^ (n - 2) * ψ ((s * (1 + p.2)) • p.1.val)) • A i p +
        ((s * (1 + p.2)) ^ (n - 1) * ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i) • B p ∂μ) :=
    (annular_averaged_columns_test_identity hn hab ha hs hw hδ hδsmall hΩ hβ hcβ hsβ hψ hcψ hsψ i).2.2
  have hLeft := integral_annular_cylinder (b := b) hnpos hs ha
    (fun x => coordinateDerivative ψ hψ i x • U x)
  have hRight := integral_annular_cylinder (b := b) hnpos hs ha (fun x => ψ x • DU x i)
  change (∫ x in V.val, coordinateDerivative ψ hψ i x • U x) =
    -(∫ x in V.val, ψ x • DU x i)
  rw [hLeft, hRight]
  have hLAE : (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (s * (s * (1 + p.2)) ^ (n - 1)) •
        (coordinateDerivative ψ hψ i ((s * (1 + p.2)) • p.1.val) • U ((s * (1 + p.2)) • p.1.val))) =ᵐ[μ]
      (fun p => (s * (s * (1 + p.2)) ^ (n - 1) * coordinateDerivative ψ hψ i
        ((s * (1 + p.2)) • p.1.val)) • F p) := by
    filter_upwards [htime] with p hp
    rw [hMap p hp, ← mul_smul]
  have hRAE : (fun p : sphere (0 : Domain n) 1 × ℝ =>
      (s * (s * (1 + p.2)) ^ (n - 1)) •
        (ψ ((s * (1 + p.2)) • p.1.val) • DU ((s * (1 + p.2)) • p.1.val) i)) =ᵐ[μ]
      (fun p => (s * (s * (1 + p.2)) ^ (n - 2) * ψ ((s * (1 + p.2)) • p.1.val)) • A i p +
        ((s * (1 + p.2)) ^ (n - 1) * ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i) • B p) := by
    filter_upwards [htime] with p hp
    rw [hCol p hp i]
    simp only [smul_add, smul_smul]
    have hLp : s * (1 + p.2) ≠ 0 := (mul_pos hs (by linarith only [ha, hp.1])).ne'
    have hindex : n - 1 = n - 2 + 1 := by omega
    have hS : s * (s * (1 + p.2)) ^ (n - 1) *
        (ψ ((s * (1 + p.2)) • p.1.val) * (s * (1 + p.2))⁻¹) =
        s * (s * (1 + p.2)) ^ (n - 2) * ψ ((s * (1 + p.2)) • p.1.val) := by
      rw [hindex, pow_succ]
      field_simp [hs.ne', show (1 + p.2) ≠ 0 by linarith only [ha, hp.1]]
    have hT : s * (s * (1 + p.2)) ^ (n - 1) *
        (ψ ((s * (1 + p.2)) • p.1.val) * (s⁻¹ * p.1.val i)) =
        (s * (1 + p.2)) ^ (n - 1) * ψ ((s * (1 + p.2)) • p.1.val) * p.1.val i := by
      field_simp [hs.ne']
    rw [hS, hT]
  rw [integral_congr_ae hLAE, integral_congr_ae hRAE]
  exact hNative

end StratificationTheory
