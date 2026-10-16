module

public import StratificationTheory.Foundation.RadialSobolevPullback
public import StratificationTheory.Foundation.RadialL2Transfer
public import HarmonicMaps.Analysis.SobolevL2Closure

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

/-- A smooth angular graph approximation produces the actual degree-zero
weak Sobolev extension of the limiting slice on a fixed punctured collar. -/
theorem exists_radial_weak_gradient_of_smooth_angular_graph_limit {n q : ℕ} (hn : 0 < n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    {f : ℕ → Domain n → Ambient q} (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (a : Domain n) (r : ℝ)
    (hu : MemLp (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val))
      2 (volume : Measure (Domain n)).toSphere)
    (hDu : ∀ i : Fin n, MemLp (fun θ : sphere (0 : Domain n) 1 => Du (a + r • θ.val) i)
      2 (volume : Measure (Domain n)).toSphere)
    (hfm : ∀ k, MemLp (fun θ : sphere (0 : Domain n) 1 => f k (a + r • θ.val))
      2 (volume : Measure (Domain n)).toSphere)
    (hfD : ∀ k (i : Fin n), MemLp (fun θ : sphere (0 : Domain n) 1 =>
      coordinateDerivative (f k) (hf k) i (a + r • θ.val))
        2 (volume : Measure (Domain n)).toSphere)
    (hconv : Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
      ‖f k (a + r • θ.val) - u (a + r • θ.val)‖ ^ 2
        ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0))
    (hDconv : ∀ i : Fin n, Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
      ‖coordinateDerivative (f k) (hf k) i (a + r • θ.val) - Du (a + r • θ.val) i‖ ^ 2
        ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0)) :
    let U : OpenDomain n := ⟨{x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2},
      isOpen_Ioo.preimage continuous_norm⟩
    ∃ D : Domain n → Gradient n q,
      MemW12 U (fun x : Domain n => u (a + r • (‖x‖⁻¹ • x))) D ∧
      ∀ (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n),
        D (ρ.val • θ.val) i = (r / ρ.val) • tangentialColumns θ (Du (a + r • θ.val)) i := by
  dsimp only
  classical
  have hnpos : 0 < n := by omega
  let w : Domain n → Ambient q := fun x => u (a + r • (‖x‖⁻¹ • x))
  let D : Domain n → Gradient n q := fun x =>
    if hx : x ≠ 0 then
      let θ := (homeomorphUnitSphereProd (Domain n)
        ⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using hx⟩).1
      (r / ‖x‖) • tangentialColumns θ (Du (a + r • θ.val))
    else 0
  let m : ℕ → Domain n → Ambient q := fun k x => f k (a + r • (‖x‖⁻¹ • x))
  let Dm : ℕ → Domain n → Gradient n q := fun k x i =>
    fderiv ℝ (m k) x (EuclideanSpace.single i 1)
  have hwRay (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) :
      w (ρ.val • θ.val) = u (a + r • θ.val) :=
    radial_smooth_pullback_ray u a r ρ.property θ
  have hDRay (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n) :
      D (ρ.val • θ.val) i = (r / ρ.val) •
        tangentialColumns θ (Du (a + r • θ.val)) i := by
    have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    have hnorm : ‖ρ.val • θ.val‖ = ρ.val := by
      rw [norm_smul, Real.norm_of_nonneg ρ.property.le, hθ, mul_one]
    have hx0 : ρ.val • θ.val ≠ 0 := by
      intro hz
      have hz' := congrArg norm hz
      rw [hnorm, norm_zero] at hz'
      exact ρ.property.ne' hz'
    let p : sphere (0 : Domain n) 1 × Ioi (0 : ℝ) := (θ, ⟨ρ.val, ρ.property⟩)
    have hs : (⟨ρ.val • θ.val,
        by simpa only [mem_compl_iff, mem_singleton_iff] using hx0⟩ :
        ({(0 : Domain n)}ᶜ : Set (Domain n))) =
        (homeomorphUnitSphereProd (Domain n)).symm p := by
      apply Subtype.ext
      simp only [homeomorphUnitSphereProd_symm_apply_coe, p]
    simp only [D, dif_pos hx0, hs, Homeomorph.apply_symm_apply, p, hnorm, Pi.smul_apply]
  have hmRay (k : ℕ) (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) :
      m k (ρ.val • θ.val) = f k (a + r • θ.val) :=
    radial_smooth_pullback_ray (f k) a r ρ.property θ
  have hDmRay (k : ℕ) (ρ : PositiveRadius) (θ : sphere (0 : Domain n) 1) (i : Fin n) :
      Dm k (ρ.val • θ.val) i = (r / ρ.val) • tangentialColumns θ
        (fun j => coordinateDerivative (f k) (hf k) j (a + r • θ.val)) i :=
    fderiv_radial_smooth_pullback_column (hf k) a r ρ.property θ i
  have hU : IsOpen {x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2} :=
    isOpen_Ioo.preimage continuous_norm
  let U : OpenDomain n := ⟨{x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2}, hU⟩
  let K : Set (Domain n) := closedBall 0 2 \ ball 0 (1 / 2)
  have hK : IsCompact K := (isCompact_closedBall 0 2).diff isOpen_ball
  have hUK : U.val ⊆ K := by
    intro x hx
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hx.2.le,
      by simpa only [mem_ball, dist_zero_right, not_lt] using hx.1.le⟩
  have hK0 : (0 : Domain n) ∉ K := by
    intro hx
    exact hx.2 (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  have hmW (k : ℕ) : MemW12 U (m k) (Dm k) :=
    memW12_radial_smooth_pullback U hK hUK hK0 (hf k) a r
  have hwLp : MemLp w 2 (volume.restrict U.val) :=
    (memLp_two_radial_collar_and_norm hnpos hu hwRay (1 / 2) (by norm_num : (0 : ℝ) < 2)).1
  have hDLp (i : Fin n) : MemLp (fun x => D x i) 2 (volume.restrict U.val) :=
    memLp_two_tangential_radial_columns hnpos hDu r hDRay
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2) i
  have hmapAngular := tendsto_eLpNorm_two_zero_of_integral_norm_sq
    (fun k => (hfm k).sub hu) hconv
  have hmconv : Tendsto (fun k => eLpNorm (m k - w) 2 (volume.restrict U.val))
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_radial_collar_zero (n := n)
      (v := fun k θ => f k (a + r • θ.val) - u (a + r • θ.val))
      (w := fun k x => m k x - w x) hnpos (fun k => (hfm k).sub hu) hmapAngular
        ?_ (1 / 2) (by norm_num : (0 : ℝ) < 2)
    intro k ρ θ
    rw [hmRay k ρ θ, hwRay ρ θ]
  have hgradconv (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => Dm k x i - D x i)
      2 (volume.restrict U.val)) atTop (𝓝 0) :=
    tendsto_eLpNorm_tangential_radial_column_error_zero (n := n)
      (A := fun k θ j => coordinateDerivative (f k) (hf k) j (a + r • θ.val))
      (B := fun θ => Du (a + r • θ.val)) (D := Dm) (DB := D)
      hnpos hfD hDu hDconv r hDmRay hDRay
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2) i
  letI : IsFiniteMeasure (volume.restrict U.val) :=
    isFiniteMeasure_restrict.mpr
      (ne_top_of_le_ne_top hK.measure_ne_top (measure_mono hUK))
  have hwW : MemW12 U w D := MemW12.of_L2_limit hmW hwLp hDLp hmconv hgradconv
  exact ⟨D, hwW, hDRay⟩

end StratificationTheory
