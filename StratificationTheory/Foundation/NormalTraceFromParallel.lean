module

public import StratificationTheory.Foundation.LocalMovingL2

/-!
# Native normal L2 limits from genuine parallel limits

A verified normal/parallel coordinate identity and a vanishing tangential
shift convert the same original parallel L2 limit into the actual normal
limit on every compact interior patch.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

theorem tendsto_local_normal_L2_of_parallel_L2 {E : Type*}
    [NormedAddCommGroup E] {m d : ℕ}
    (V : Set (Domain m)) (W : Domain d → E) (Γ : ℝ → Domain m → Domain d)
    (ν : Domain d) (g : Domain m → E) (shift : ℝ → Domain m)
    {c : ℝ} (hc : 0 < c)
    (hnormal : ∀ y η, Γ 0 y + η • ν = Γ (c * η) (y + shift η))
    (hshift : Tendsto shift (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hg : MemLp g 2 (volume.restrict V))
    (hL : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      MemLp (fun y => W (Γ δ y) - g y) 2 (volume.restrict V))
    (hLim : Tendsto (fun δ => eLpNorm (fun y => W (Γ δ y) - g y)
      2 (volume.restrict V)) (𝓝[>] 0) (𝓝 0)) :
    ∀ K : Set (Domain m), IsCompact K → K ⊆ interior V →
      (∀ᶠ η in 𝓝[>] (0 : ℝ),
        MemLp (fun y => W (Γ 0 y + η • ν) - g y) 2 (volume.restrict K)) ∧
      Tendsto (fun η : ℝ => eLpNorm (fun y => W (Γ 0 y + η • ν) - g y)
        2 (volume.restrict K)) (𝓝[>] 0) (𝓝 0) := by
  intro K hK hKV
  have hδ : Tendsto (fun η : ℝ => c * η) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [mul_zero,id_eq] using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hc hη
  let Ω := interior V
  let F : ℝ → Domain m → E := fun η y => W (Γ (c * η) y)
  have hE : ∀ᶠ η in 𝓝[>] (0 : ℝ), MemLp (fun y => F η y - g y)
      2 (volume.restrict Ω) :=
    (hδ.eventually hL).mono (fun _ h => h.mono_measure
      (Measure.restrict_mono_set volume interior_subset))
  have hELim : Tendsto (fun η : ℝ => eLpNorm (fun y => F η y - g y)
      2 (volume.restrict Ω)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hLim.comp hδ)
      (fun _ => zero_le)
    intro η
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume interior_subset)
  have hlocal := tendsto_local_L2_after_small_translation isOpen_interior hK hKV
    (hg.mono_measure (Measure.restrict_mono_set volume interior_subset)) hE hELim hshift
  have hformula (η : ℝ) (y : Domain m) :
      F η (y + shift η) - g y = W (Γ 0 y + η • ν) - g y := by
    dsimp only [F]
    rw [hnormal]
  refine ⟨?_,?_⟩
  · filter_upwards [hlocal.1] with η hη
    simpa only [hformula] using hη.2
  · exact hlocal.2.congr' (Eventually.of_forall (fun η => by simp only [hformula]))

end StratificationTheory
