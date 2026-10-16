module

public import StratificationTheory.Foundation.PolarJointConvergence
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.SobolevRestriction

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped Topology ENNReal ContDiff

namespace StratificationTheory

/-- Actual local Sobolev data admit one smooth graph approximation and one
subsequence whose map and all classical column errors vanish angularly on a
common radial full-measure set. Every original map and column retains its
actual angular L2 membership there. -/
theorem exists_smooth_subseq_ae_angular_graph_approximation {n q : ℕ}
    (hn : 0 < n) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall a R ⊆ Ω.val) :
    ∃ m : ℕ → Domain n → Ambient q, ∃ hm : ∀ k, ContDiff ℝ ∞ (m k),
      (∀ k, MemW12 (ballDomain a R) (m k)
        (fun x i => coordinateDerivative (m k) (hm k) i x)) ∧
      ∃ κ : ℕ → ℕ, StrictMono κ ∧
        ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
          MemLp (fun θ : sphere (0 : Domain n) 1 => u (a + r • θ.val))
            2 (volume : Measure (Domain n)).toSphere ∧
          (∀ i : Fin n, MemLp (fun θ : sphere (0 : Domain n) 1 => Du (a + r • θ.val) i)
            2 (volume : Measure (Domain n)).toSphere) ∧
          (∀ k, MemLp (fun θ : sphere (0 : Domain n) 1 => m k (a + r • θ.val))
            2 (volume : Measure (Domain n)).toSphere ∧
            ∀ i : Fin n, MemLp (fun θ : sphere (0 : Domain n) 1 =>
              coordinateDerivative (m k) (hm k) i (a + r • θ.val))
              2 (volume : Measure (Domain n)).toSphere) ∧
          (∀ k, Integrable (fun θ : sphere (0 : Domain n) 1 =>
            ‖m k (a + r • θ.val) - u (a + r • θ.val)‖ ^ 2)
            (volume : Measure (Domain n)).toSphere ∧
            ∀ i : Fin n, Integrable (fun θ : sphere (0 : Domain n) 1 =>
              ‖coordinateDerivative (m k) (hm k) i (a + r • θ.val) - Du (a + r • θ.val) i‖ ^ 2)
                (volume : Measure (Domain n)).toSphere) ∧
          Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
            ‖m (κ k) (a + r • θ.val) - u (a + r • θ.val)‖ ^ 2
              ∂(volume : Measure (Domain n)).toSphere) atTop (𝓝 0) ∧
          ∀ i : Fin n, Tendsto (fun k => ∫ θ : sphere (0 : Domain n) 1,
            ‖coordinateDerivative (m (κ k)) (hm (κ k)) i (a + r • θ.val) -
              Du (a + r • θ.val) i‖ ^ 2 ∂(volume : Measure (Domain n)).toSphere)
                atTop (𝓝 0) := by
  classical
  have hfinite := hu.memW12_ball hball
  obtain ⟨m, hm, hmW, hconv, hDconv⟩ := hfinite.smoothDensity_memW12_ball hR
  let f : Option (Fin n) → ℕ → Domain n → Ambient q := fun j k =>
    match j with
    | none => m k
    | some i => coordinateDerivative (m k) (hm k) i
  let v : Option (Fin n) → Domain n → Ambient q := fun j =>
    match j with
    | none => u
    | some i => fun x => Du x i
  have hf (j : Option (Fin n)) (k : ℕ) : MemLp (f j k) 2 (volume.restrict (ball a R)) := by
    cases j with
    | none => exact (hmW k).2.1
    | some i => exact (hmW k).2.2 i
  have hv (j : Option (Fin n)) : MemLp (v j) 2 (volume.restrict (ball a R)) := by
    cases j with
    | none => exact hfinite.2.1
    | some i => exact hfinite.2.2 i
  have hl (j : Option (Fin n)) : Tendsto (fun k => eLpNorm (f j k - v j) 2
      (volume.restrict (ball a R))) atTop (𝓝 0) := by
    cases j with
    | none => exact hconv
    | some i => exact hDconv i
  obtain ⟨κ, hκ, hae⟩ := exists_subseq_ae_tendsto_polar_l2_family_ball
    (ι := Option (Fin n)) (n := n) (f := f) (u := v) (a := a) (R := R) hn hf hv hl
  refine ⟨m, hm, hmW, κ, hκ, ?_⟩
  filter_upwards [hae] with r hr
  refine ⟨(hr none).2.1, (fun i => (hr (some i)).2.1), ?_, ?_,
    (hr none).2.2.2, fun i => (hr (some i)).2.2.2⟩
  · intro k
    exact ⟨(hr none).1 k, fun i => (hr (some i)).1 k⟩
  · intro k
    exact ⟨(hr none).2.2.1 k, fun i => (hr (some i)).2.2.1 k⟩

end StratificationTheory
