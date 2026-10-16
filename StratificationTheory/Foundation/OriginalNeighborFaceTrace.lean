module

public import StratificationTheory.Foundation.TranslatedL2TraceCompatibility
public import HarmonicMaps.Energy

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- Two original normalized traces based at neighboring coordinate origins
give one physical segment trace with both original raw endpoint classes. -/
theorem exists_one_raw_face_trace_between_neighbor_origins {N k q : ℕ}
    {μ : Measure (Domain k)} {a b c c' ε : ℝ} (hε : 0 < ε)
    (hc : c ∈ Ioo a b) (hc' : c' ∈ Ioo a b) (hshift : c' = c + ε)
    (u : Domain N → Ambient q) (B : Domain k → Domain N) (y y' v : Domain N)
    (hy' : y' = y + ε • v)
    (H : C(Icc (a - c) (b - c), Lp (Ambient q) 2 μ))
    (K : C(Icc (a - c') (b - c'), Lp (Ambient q) 2 μ))
    (hH : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (a - c) (b - c),
      ∃ hslice : MemLp (fun s => u (y + B s + r • v)) 2 μ,
        H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun s => u (y + B s + r • v)))
    (hK : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (a - c') (b - c'),
      ∃ hslice : MemLp (fun s => u (y' + B s + r • v)) 2 μ,
        K ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun s => u (y' + B s + r • v)))
    (hf₀ : MemLp (fun s => u (y + B s)) 2 μ)
    (hH₀ : H ⟨0, sub_nonpos.mpr hc.1.le, sub_nonneg.mpr hc.2.le⟩ = hf₀.toLp (fun s => u (y + B s)))
    (hg₀ : MemLp (fun s => u (y' + B s)) 2 μ)
    (hK₀ : K ⟨0, sub_nonpos.mpr hc'.1.le, sub_nonneg.mpr hc'.2.le⟩ = hg₀.toLp (fun s => u (y' + B s))) :
    ∃ J : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 μ),
      (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
        ∃ hslice : MemLp (fun s => u (y + B s + r • v)) 2 μ,
          J ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun s => u (y + B s + r • v))) ∧
      J ⟨0, le_rfl, hε.le⟩ = hf₀.toLp (fun s => u (y + B s)) ∧
      J ⟨ε, hε.le, le_rfl⟩ = hg₀.toLp (fun s => u (y' + B s)) ∧
      ∀ L : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 μ),
        (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
          ∃ hslice : MemLp (fun s => u (y + B s + r • v)) 2 μ,
            L ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun s => u (y + B s + r • v))) → L = J := by
  let F : Domain k × ℝ → Ambient q := fun sr => u (y + B sr.1 + sr.2 • v)
  let F' : Domain k × ℝ → Ambient q := fun sr => u (y' + B sr.1 + sr.2 • v)
  have hclosed : ∀ r ∈ Icc (a - c) (b - c), r - ε ∈ Icc (a - c') (b - c') := by
    intro r hr
    rw [hshift]
    exact ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hopen : ∀ r ∈ Ioo (a - c) (b - c), r - ε ∈ Ioo (a - c') (b - c') := by
    intro r hr
    rw [hshift]
    exact ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hraw (s : Domain k) (r : ℝ) : F' (s, r - ε) = F (s, r) := by
    dsimp only [F', F]
    rw [hy', sub_smul]
    congr 1
    abel
  have hha : a - c < 0 := sub_neg.mpr hc.1
  have hhb : ε < b - c := by linarith only [hc'.2, hshift]
  have hhc : a - c' < 0 := sub_neg.mpr hc'.1
  have hhd : 0 < b - c' := sub_pos.mpr hc'.2
  have hF₀ : MemLp (fun s => F (s, 0)) 2 μ := by simpa only [F, zero_smul, add_zero] using hf₀
  have hF'₀ : MemLp (fun s => F' (s, 0)) 2 μ := by simpa only [F', zero_smul, add_zero] using hg₀
  have hH₀' : H ⟨0, hha.le, (hε.trans hhb).le⟩ = hF₀.toLp (fun s => F (s, 0)) := by
    simpa only [F, zero_smul, add_zero] using hH₀
  have hK₀' : K ⟨0, hhc.le, hhd.le⟩ = hF'₀.toLp (fun s => F' (s, 0)) := by
    simpa only [F', zero_smul, add_zero] using hK₀
  obtain ⟨J, _hJrestrict, hJ, hJ₀, hJε, hJunique⟩ :=
    exists_one_L2_trace_between_translated_raw_cuts hε hha hhb hhc hhd H K hH hK
      hclosed hopen hraw hF₀ hH₀' hF'₀ hK₀'
  exact ⟨J, hJ, by simpa only [F, zero_smul, add_zero] using hJ₀,
    by simpa only [F', zero_smul, add_zero] using hJε, hJunique⟩

end StratificationTheory
