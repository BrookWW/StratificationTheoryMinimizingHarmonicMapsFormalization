module

public import StratificationTheory.Foundation.SpatialConeIndependentL2

/-!
# Actual parallel spatial-cone limits on bounded positive height bands

The same literal cone map has the original flat trace as its parallel-side
L2 limit on any finite positive-height band. No unit-height cap is required.
The independent parameter retains its original value.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

theorem native_spatial_face_cone_parallel_limit_L2 {A E : Type*}
    [MeasurableSpace A] [NormedAddCommGroup E]
    {n : ℕ} (τ : Measure A) [IsFiniteMeasure τ]
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSfinite : (volume : Measure (Domain n)) S ≠ ⊤)
    {a b₀ b₁ : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
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
    let W : Domain (n + 1 + 1) × A → E := fun p => w ((((e p.1).2 0)⁻¹ • (e p.1).1),p.2)
    let γ : ℝ → Domain (n + 1) × A → Domain (n + 1 + 1) × A := fun δ p =>
      (e.symm (b.symm ((b p.1).1, EuclideanSpace.single (0 : Fin 1) (T p.1 - δ)),
        EuclideanSpace.single (0 : Fin 1) (T p.1)),p.2)
    let R : ℝ → Domain (n + 1) × A → E := fun δ p => W (γ δ p) - g (ξ p.1,p.2)
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (R δ) 2 ((volume.restrict C).prod τ)) ∧
      Tendsto (fun δ => eLpNorm (R δ) 2 ((volume.restrict C).prod τ))
        (𝓝[>] 0) (𝓝 0) := by
  intro b μ f H hf hSlices g hg hEnd e T ξ C W γ R
  have hraw := native_spatial_cone_raw_parameter_L2 τ hS hSfinite ha hb₀ H f hf hSlices g hg hEnd
    (b₁ := b₁)
  have hC : MeasurableSet C :=
    (measurableSet_Icc.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp b.continuous)).measurable).inter
      (hS.preimage (((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp b.continuous)).measurable.inv.smul
        (measurable_fst.comp b.continuous.measurable)))
  have hAE (δ : ℝ) : R δ =ᵐ[(volume.restrict C).prod τ]
      (fun p => f ((ξ p.1,p.2),1 - δ / T p.1) - g (ξ p.1,p.2)) := by
    have hmem : ∀ᵐ p : Domain (n + 1) × A ∂(volume.restrict C).prod τ, p.1 ∈ C :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hC)
    filter_upwards [hmem] with p hp
    have ht : T p.1 ≠ 0 := (hb₀.trans_le hp.1.1).ne'
    have hs : (T p.1)⁻¹ • EuclideanSpace.single (0 : Fin 1) (T p.1 - δ) =
        EuclideanSpace.single (0 : Fin 1) (1 - δ / T p.1) := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul]
      field_simp
    dsimp only [R,W,γ]
    rw [e.apply_symm_apply]
    simp only [PiLp.single_apply,ite_true]
    rw [← b.symm.map_smul]
    change w (b.symm ((T p.1)⁻¹ • (b p.1).1,
      (T p.1)⁻¹ • EuclideanSpace.single (0 : Fin 1) (T p.1 - δ)),p.2) - _ = _
    rw [hs]
  refine ⟨hraw.1.mono (fun δ h => h.ae_eq (hAE δ).symm),?_⟩
  exact hraw.2.congr' (Eventually.of_forall (fun δ => (eLpNorm_congr_ae (hAE δ)).symm))

end StratificationTheory
