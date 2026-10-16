-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StratificationTheory.Frozen.CylinderTraceCharacterization
public import StratificationTheory.Foundation.CylinderPointCoordinates
public import HarmonicMaps.Sobolev
import StratificationTheory.Providers.CylinderAnnularTransfer

public section
open HarmonicMaps MeasureTheory Metric Set Filter
namespace StratificationTheory

/-- A full cylinder Sobolev map transfers to the actual annulus with its
original interior values and the same continuous native-L2 endpoint trace
curve under the radial affine parameter. -/
theorem cylinder_to_annulus_exists {n q : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (hab : a < b) (ha : -1 < a) {s : ℝ} (hs : 0 < s)
    (c : Domain n) (v : unitCylinder n a b → Ambient q)
    (hv : MemCylinderW12 hn hab v) :
    let lo := s * (1 + a)
    let hi := s * (1 + b)
    let Ω : OpenDomain n := ⟨{x | lo < ‖x - c‖ ∧ ‖x - c‖ < hi},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let τ : C(Icc lo hi, Icc a b) :=
      ⟨fun r => ⟨r.val / s - 1, by
        constructor
        · have h : a + 1 ≤ r.val / s := (le_div_iff₀ hs).mpr (by
            have hr := r.property.1
            dsimp only [lo] at hr
            nlinarith only [hr])
          linarith only [h]
        · have h : r.val / s ≤ b + 1 := (div_le_iff₀ hs).mpr (by
            have hr := r.property.2
            dsimp only [hi] at hr
            nlinarith only [hr])
          linarith only [h]⟩,
        by
          apply Continuous.subtype_mk
          exact (continuous_subtype_val.div_const s).sub (continuous_const (y := (1 : ℝ)))⟩
    let K := (cylinderTrace hn hab v hv).comp τ
    let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
    ∃ W : Domain n → Ambient q, ∃ DW : Domain n → Gradient n q,
      MemW12 Ω W DW ∧
      (∀ (θ : sphere (0 : Domain n) 1) (t : ℝ) (ht : t ∈ Ioo a b),
        W (c + (s * (1 + t)) • θ.val) =
          v ⟨e.symm (θ.val, EuclideanSpace.single (0 : Fin 1) t),
            unitCylinder_param_mem θ ⟨t, ht.1.le, ht.2.le⟩⟩) ∧
      ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo lo hi,
        ∃ hslice : MemLp (fun θ : sphere (0 : Domain n) 1 => W (c + r • θ.val)) 2 σ,
          K ⟨r, hr.1.le, hr.2.le⟩ =
            hslice.toLp (fun θ : sphere (0 : Domain n) 1 => W (c + r • θ.val)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StratificationTheory.Providers.CylinderAnnularTransfer.result hn hab ha hs c v hv
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StratificationTheory
-- FROZEN_ANCHOR_SUFFIX_END
