module

public import StratificationTheory.Foundation.SpatialConeParallelLimit
public import StratificationTheory.Foundation.SpatialConeBaseParameterL2
public import StratificationTheory.Foundation.SpatialConeNormalCoordinates
public import StratificationTheory.Foundation.NormalTraceFromParallel

/-!
# Actual spatial unit-normal traces with independent time

Original native flat trace curves determine the same spatial cone map along
its actual inward unit normal on every compact interior lateral-time patch.
The tangential parameter shift is spatial; interpolation time is unchanged.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StratificationTheory

/-- The actual spatial unit-normal slices of the same cone map converge to
the original native edge-times-time trace class. -/
theorem native_spatial_face_cone_normal_side_L2 {E : Type*}
    [NormedAddCommGroup E] {n : ℕ}
    {S : Set (Domain n)} (hS : MeasurableSet S)
    (hSfinite : (volume : Measure (Domain n)) S ≠ ⊤)
    {a b₀ b₁ c d : ℝ} (ha : a < 1) (hb₀ : 0 < b₀)
    (w : Domain (n + 1) × ℝ → E) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1) (m := 1)
    let eF := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 1 + 1) (m := 1)
    let τ := (volume : Measure ℝ).restrict (Ioo c d)
    let μ := ((volume : Measure (Domain n)).restrict S).prod τ
    let f : (Domain n × ℝ) × ℝ → E := fun p =>
      w (b.symm (p.1.1, EuclideanSpace.single (0 : Fin 1) p.2),p.1.2)
    ∀ H : C(Icc a 1, Lp E 2 μ),
    AEStronglyMeasurable f (μ.prod (volume.restrict (Ioo a 1))) →
    (∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a 1,
      ∃ hs : MemLp (fun x => f (x,z)) 2 μ,
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp (fun x => f (x,z))) →
    ∀ (g : Domain n × ℝ → E) (hg : MemLp g 2 μ),
    H ⟨1, ha.le, le_rfl⟩ = hg.toLp g →
    let T : Domain (n + 1) → ℝ := fun y => (b y).2 0
    let ξ : Domain (n + 1) → Domain n := fun y => (T y)⁻¹ • (b y).1
    let C := {y : Domain (n + 1) | T y ∈ Icc b₀ b₁ ∧ ξ y ∈ S}
    let V := {y : Domain (n + 1 + 1) | (e y).1 ∈ C ∧ (e y).2 0 ∈ Ioo c d}
    let ν := spatialConeNormalVector n
    let Γ := spatialConeParallelSlice n
    let W : Domain (n + 1 + 1 + 1) → E := fun y =>
      w ((((e (eF y).1).2 0)⁻¹ • (e (eF y).1).1),(eF y).2 0)
    let G : Domain (n + 1 + 1) → E := fun y => g (ξ (e y).1,(e y).2 0)
    ‖ν‖ = 1 ∧ ∀ K : Set (Domain (n + 1 + 1)), IsCompact K → K ⊆ interior V →
      (∀ᶠ η in 𝓝[>] (0 : ℝ),
        MemLp (fun y => W (Γ 0 y + η • ν) - G y) 2 (volume.restrict K)) ∧
      Tendsto (fun η : ℝ => eLpNorm (fun y => W (Γ 0 y + η • ν) - G y)
        2 (volume.restrict K)) (𝓝[>] 0) (𝓝 0) := by
  intro b e eF τ μ f H hf hSlices g hg hEnd T ξ C V ν Γ W G
  let P : Domain (n + 1 + 1) → Domain (n + 1) × ℝ := fun y => ((e y).1,(e y).2 0)
  have hC : MeasurableSet C :=
    (measurableSet_Icc.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_snd.comp b.continuous)).measurable).inter
      (hS.preimage (((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp b.continuous)).measurable.inv.smul
        (measurable_fst.comp b.continuous.measurable)))
  have hMP := (measurePreserving_cylinder_coordinates (n + 1)).restrict_preimage
    (hC.prod (measurableSet_Ioo : MeasurableSet (Ioo c d)))
  change MeasurePreserving P (volume.restrict V)
    (((volume : Measure (Domain (n + 1))).prod volume).restrict (C ×ˢ Ioo c d)) at hMP
  rw [← Measure.prod_restrict] at hMP
  change MeasurePreserving P (volume.restrict V) ((volume.restrict C).prod τ) at hMP
  let γ : ℝ → Domain (n + 1) → Domain (n + 1 + 1) := fun δ y =>
    e.symm (b.symm ((b y).1,EuclideanSpace.single (0 : Fin 1) (T y - δ)),
      EuclideanSpace.single (0 : Fin 1) (T y))
  let Wp : Domain (n + 1 + 1) × ℝ → E := fun p => w ((((e p.1).2 0)⁻¹ • (e p.1).1),p.2)
  let γp : ℝ → Domain (n + 1) × ℝ → Domain (n + 1 + 1) × ℝ := fun δ p => (γ δ p.1,p.2)
  let Rp : ℝ → Domain (n + 1) × ℝ → E := fun δ p => Wp (γp δ p) - g (ξ p.1,p.2)
  obtain ⟨hRp,hRpLim⟩ :
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), MemLp (Rp δ) 2 ((volume.restrict C).prod τ)) ∧
      Tendsto (fun δ => eLpNorm (Rp δ) 2 ((volume.restrict C).prod τ))
        (𝓝[>] 0) (𝓝 0) :=
    native_spatial_face_cone_parallel_limit_L2 (b₁ := b₁) τ hS hSfinite ha hb₀ w
      H hf hSlices g hg hEnd
  have hraw (δ : ℝ) (y : Domain (n + 1 + 1)) :
      Rp δ (P y) = W (Γ δ y) - G y := by
    dsimp only [Rp, P, Wp, γp, W, Γ, G,spatialConeParallelSlice]
    rw [eF.apply_symm_apply]
  have hcompose (δ : ℝ) : (Rp δ ∘ P) = (fun y => W (Γ δ y) - G y) := funext (hraw δ)
  have hL : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      MemLp (fun y => W (Γ δ y) - G y) 2 (volume.restrict V) := by
    filter_upwards [hRp] with δ hδ
    rw [← hcompose δ]
    exact hδ.comp_measurePreserving hMP
  have hLim : Tendsto (fun δ => eLpNorm (fun y => W (Γ δ y) - G y)
      2 (volume.restrict V)) (𝓝[>] 0) (𝓝 0) := by
    apply hRpLim.congr'
    filter_upwards [hRp] with δ hδ
    have hnorm := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) hδ.aestronglyMeasurable hMP
    rw [hcompose δ] at hnorm
    exact hnorm.symm
  have hGp : MemLp (fun p : Domain (n + 1) × ℝ => g (ξ p.1,p.2))
      2 ((volume.restrict C).prod τ) :=
    memLp_spatial_cone_base_independent_parameter τ hS measurableSet_Icc
      (fun _ ht => hb₀.trans_le ht.1) (M := b₁) (fun _ ht => ht.2) g hg
  have hGpull : ((fun p : Domain (n + 1) × ℝ => g (ξ p.1,p.2)) ∘ P) = G := rfl
  have hG : MemLp G 2 (volume.restrict V) := by
    rw [← hGpull]
    exact hGp.comp_measurePreserving hMP
  let shift := spatialConeNormalTangentialShift n
  have hgeometry : ‖ν‖ = 1 ∧
      (∀ y η, Γ 0 y + η • ν = Γ (Real.sqrt 2 * η) (y + shift η)) ∧
      Continuous shift ∧ shift 0 = 0 := spatial_cone_normal_translation n
  have hshift : Tendsto shift (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [← hgeometry.2.2.2]
    exact hgeometry.2.2.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨hgeometry.1, tendsto_local_normal_L2_of_parallel_L2 V W Γ ν G shift
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) hgeometry.2.1 hshift hG hL hLim⟩

end StratificationTheory
