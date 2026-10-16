module

public import StratificationTheory.Foundation.SpatialConeIndependentL2
public import StratificationTheory.Foundation.ConicalSideGeometry
public import StratificationTheory.Foundation.CubicalFaceRectangleL2

/-!
# Genuine parallel spatial-cone traces with unchanged time

Original flat native L2 traces produce the parallel-side traces of the same
literal spatial cone map. An independent parameter, in particular actual
interpolation time, retains its original value in every displayed formula.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

theorem native_spatial_face_cone_parallel_side_L2 {A E : Type*}
    [MeasurableSpace A] [NormedAddCommGroup E]
    {n : ℕ} (τ : Measure A) [IsFiniteMeasure τ]
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSbound : ∀ x ∈ S, ∀ i : Fin n, |x i| < 1)
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀) (hb₁ : b₁ < 1)
    (w : Domain (n + 1) × A → E) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let μ := ((volume : Measure (Domain n)).restrict S).prod τ
    let f : (Domain n × A) × ℝ → E := fun p =>
      w (b.symm (p.1.1, EuclideanSpace.single (0 : Fin 1) p.2),p.1.2)
    ∀ H : C(Icc a 1, Lp E 2 μ),
    AEStronglyMeasurable f (μ.prod (volume.restrict (Ioo a 1))) →
    (∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 μ,
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x => f (x,z))) →
    ∀ (g : Domain n × A → E) (hg : MemLp g 2 μ),
    H ⟨1, ha.le, le_rfl⟩ = hg.toLp g →
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let W : Domain ((n + 1) + 1) × A → E := fun p =>
      w ((((e p.1).2 0)⁻¹ • (e p.1).1),p.2)
    let γ : ℝ → Domain (n + 1) × A → Domain ((n + 1) + 1) × A := fun δ p =>
      (e.symm (b.symm ((b p.1).1, EuclideanSpace.single (0 : Fin 1) (T p.1 - δ)),
        EuclideanSpace.single (0 : Fin 1) (T p.1)),p.2)
    let R : ℝ → Domain (n + 1) × A → E := fun δ p => W (γ δ p) - g (ξ p.1,p.2)
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (R δ) 2 ((volume.restrict C).prod τ) ∧
      ∀ p : Domain (n + 1) × A, p.1 ∈ C →
        (γ δ p).2 = p.2 ∧
        ((e (γ δ p).1).2 0 ∈ Ioo (0 : ℝ) 1 ∧
          ∀ i : Fin (n + 1), |(e (γ δ p).1).1 i| < (e (γ δ p).1).2 0) ∧
        (e (γ δ p).1).2 0 - (b (e (γ δ p).1).1).2 0 = δ) ∧
      Tendsto (fun δ => eLpNorm (R δ) 2 ((volume.restrict C).prod τ))
        (𝓝[>] 0) (𝓝 0) := by
  intro b μ f H hf hSlices g hg hEnd e T ξ C W γ R
  have hSfinite : (volume : Measure (Domain n)) S ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_unit_coordinate_face_ne_top n) (measure_mono (fun x hx =>
      (mem_unit_coordinate_face_iff x).mpr (hSbound x hx)))
  have hraw := native_spatial_cone_raw_parameter_L2 τ hS hSfinite ha hb₀ H f hf hSlices g hg hEnd
    (b₁ := b₁)
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 2 * b₀ := Ioo_mem_nhdsGT (by positivity)
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ p : Domain (n + 1) × A, p.1 ∈ C →
        R δ p = f ((ξ p.1,p.2),1 - δ / T p.1) - g (ξ p.1,p.2) := by
    filter_upwards [hsmall] with δ hδ
    intro p hp
    have ht : 0 < T p.1 := hb₀.trans_le hp.1.1
    have hx : ∀ i : Fin n, |(b p.1).1 i| < T p.1 := by
      intro i
      have hi := hSbound (ξ p.1) hp.2 i
      change |(T p.1)⁻¹ * (b p.1).1 i| < 1 at hi
      rw [abs_mul, abs_of_pos (inv_pos.mpr ht)] at hi
      have hi' : |(b p.1).1 i| / T p.1 < 1 := by
        simpa only [div_eq_mul_inv, mul_comm] using hi
      exact (div_lt_one ht).mp hi'
    have hs := native_face_cone_parallel_side_slice (fun x => w (x,p.2)) ht hδ.1
      (hδ.2.trans_le (by linarith only [hp.1.1])) (b p.1).1 hx
    exact congrArg (fun z => z - g (ξ p.1,p.2)) hs.1
  have hC : MeasurableSet C :=
    (measurableSet_Icc.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp b.continuous)).measurable).inter
      (hS.preimage (((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp b.continuous)).measurable.inv.smul
        (measurable_fst.comp b.continuous.measurable)))
  have hAE : ∀ᶠ δ in 𝓝[>] (0 : ℝ), R δ =ᵐ[(volume.restrict C).prod τ]
      (fun p => f ((ξ p.1,p.2),1 - δ / T p.1) - g (ξ p.1,p.2)) := by
    have hmem : ∀ᵐ p : Domain (n + 1) × A ∂(volume.restrict C).prod τ, p.1 ∈ C :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hC)
    filter_upwards [heq] with δ hδ
    filter_upwards [hmem] with p hp
    exact hδ p hp
  refine ⟨?_, hraw.2.congr' (hAE.mono (fun _ h => (eLpNorm_congr_ae h).symm))⟩
  filter_upwards [hraw.1, hAE, hsmall] with δ hL hA hδ
  refine ⟨hL.ae_eq hA.symm, ?_⟩
  intro p hp
  have ht : 0 < T p.1 := hb₀.trans_le hp.1.1
  have hx : ∀ i : Fin n, |(b p.1).1 i| < T p.1 := by
    intro i
    have hi := hSbound (ξ p.1) hp.2 i
    change |(T p.1)⁻¹ * (b p.1).1 i| < 1 at hi
    rw [abs_mul, abs_of_pos (inv_pos.mpr ht)] at hi
    have hi' : |(b p.1).1 i| / T p.1 < 1 := by simpa only [div_eq_mul_inv, mul_comm] using hi
    exact (div_lt_one ht).mp hi'
  have hs := native_face_cone_parallel_side_slice (fun x => w (x,p.2)) ht hδ.1
    (hδ.2.trans_le (by linarith only [hp.1.1])) (b p.1).1 hx
  refine ⟨rfl, ⟨?_, hs.2.2⟩, hs.2.1⟩
  simpa only [γ, e.apply_symm_apply, PiLp.single_apply, ite_true] using
    (show T p.1 ∈ Ioo (0 : ℝ) 1 from ⟨ht,hp.1.2.trans_lt hb₁⟩)

end StratificationTheory
