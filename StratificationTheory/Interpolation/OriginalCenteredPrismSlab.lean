module

public import StratificationTheory.Interpolation.OriginalNativePrismSlabWithTimeTrace
public import StratificationTheory.Foundation.SpatialPrismTranslation

public section
open HarmonicMaps MeasureTheory Metric Set Filter Module
open scoped Topology BigOperators ENNReal
namespace StratificationTheory

/-- One original Sobolev pair produces an actual full-dimensional weak
map on the centered interior spatial cube times the original time interval.
The physical mesh has the coupled energy bound, the frozen ambient
powers for its target distance, and its original two temporal trace classes. -/
theorem exists_original_ball_centered_prism_slab_with_time_trace {n q : ℕ}
    (w : Fin 2 → Domain (n + 2) → Ambient q)
    (Dw : Fin 2 → Domain (n + 2) → Gradient (n + 2) q)
    (hSob : ∀ l, MemW12 (ballDomain (0 : Domain (n + 2)) ((n : ℝ) + 3)) (w l) (Dw l))
    (N : Set (Ambient q)) (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ x ∂volume.restrict (ball (0 : Domain (n + 2)) ((n : ℝ) + 3)), w l x ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < (1 / 8 : ℝ)) :
    let J := (r : Fin (n + 3)) × (Fin r.val ↪ Fin (n + 2))
    let A₀ := (∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 0 x)) +
      ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), hsNormSq (Dw 1 x)
    let D₀ := ∫ x in ball (0 : Domain (n + 2)) ((n : ℝ) + 3), ‖w 0 x - w 1 x‖ ^ 2
    let K : ℝ≥0∞ := 4 * (Fintype.card J : ℝ≥0∞) * (Fintype.card J : ℝ≥0∞) *
      (6 * ((n + 3 : ℕ) : ℝ≥0∞)) ^ (n + 1)
    let BTube := ((2 : ℝ) ^ (n + 1) * ((n + 2).factorial : ℝ)) *
      ((4 * (Fintype.card J : ℝ)) * ε ^ ((1 : ℤ) - ((n + 2 : ℕ) : ℤ)) * Real.sqrt A₀ * Real.sqrt D₀ +
        (4 * (Fintype.card J : ℝ)) * ε ^ (-((n + 2 : ℕ) : ℤ)) * D₀)
    let U : OpenDomain (n + 2) :=
        ⟨⋂ j : Fin (n + 2), (EuclideanSpace.proj j) ⁻¹' Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ),
          isOpen_iInter_of_finite (fun j : Fin (n + 2) =>
            isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n + 2) (m := 1)
      let Ω : OpenDomain (n + 3) :=
        ⟨{x | (e x).1 ∈ U.val ∧ (e x).2 0 ∈ Ioo (0 : ℝ) ε},
          (U.property.preimage (continuous_fst.comp e.continuous)).inter
            (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
              (continuous_snd.comp e.continuous)))⟩
      ∃ (W : Domain (n + 3) → Ambient q) (D : Domain (n + 3) → Gradient (n + 3) q) (M : ℝ)
        (Htime : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict U.val))),
        MemW12 Ω W D ∧ (0 ≤ M ∧ ∀ z ∈ N, ‖z‖ ≤ M) ∧
        (∀ᵐ x ∂volume.restrict Ω.val, ‖W x‖ ≤ M) ∧
        ENNReal.ofReal (∫ x in Ω.val, hsNormSq (D x)) ≤
          K * (ENNReal.ofReal ε * ENNReal.ofReal A₀ +
            (ENNReal.ofReal ε)⁻¹ * ENNReal.ofReal D₀) ∧
        (∀ᵐ x ∂volume.restrict Ω.val, (infDist (W x) N) ^ 2 ≤ BTube) ∧
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) ε,
          ∃ hs : MemLp (fun x : Domain (n + 2) =>
            W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) 2 (volume.restrict U.val),
            Htime ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun x =>
              W (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        (∃ hw₀ : MemLp (fun x : Domain (n + 2) => w 0 x) 2 (volume.restrict U.val),
          Htime ⟨0, le_rfl, hε.le⟩ = hw₀.toLp (fun x => w 0 x)) ∧
        (∃ hw₁ : MemLp (fun x : Domain (n + 2) => w 1 x) 2 (volume.restrict U.val),
          Htime ⟨ε, hε.le, le_rfl⟩ = hw₁.toLp (fun x => w 1 x)) := by
  classical
  intro J A₀ D₀ K BTube U e Ω
  obtain ⟨base, hNative⟩ := exists_original_ball_native_prism_slab_with_time_trace
    w Dw hSob N hN hTarget ε hε hεsmall
  dsimp (config := {zeta := false}) only at hNative
  obtain ⟨W, D, M, H, hW, hM, hNorm, hEnergy, hTube, hRaw, hEnd₀, hEnd₁⟩ := hNative
  obtain ⟨hW₀, hEnergy₀, hProp, H₀, hRaw₀, hEnd₀', hEnd₁'⟩ :=
    spatial_prism_translation_with_original_time_trace base (3 / 4 : ℝ) hε w W D hW H hRaw hEnd₀ hEnd₁
  let lift := e.symm (base, (0 : Domain 1))
  let F := fun x : Domain (n + 3) => x - lift
  refine ⟨W ∘ F, D ∘ F, M, H₀, hW₀, hM, hProp (fun z => ‖z‖ ≤ M) hNorm, ?_,
    hProp (fun z => (infDist z N) ^ 2 ≤ BTube) hTube, hRaw₀, hEnd₀', hEnd₁'⟩
  rw [hEnergy₀]
  exact hEnergy

end StratificationTheory
