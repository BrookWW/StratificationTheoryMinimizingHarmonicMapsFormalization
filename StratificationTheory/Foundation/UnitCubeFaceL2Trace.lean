module

public import StratificationTheory.Foundation.UnitCubeAffineCoordinates
public import StratificationTheory.Foundation.UnitIntervalL2Trace
public import StratificationTheory.Foundation.SurfaceL2TraceTransport

/-!
# Original physical face traces in unit-cube coordinates

The same positive similarity normalizes the spatial base and the physical
time interval. Exact native measure transport gives a continuous unit-face
L2 trace with the original affine raw slices and both original endpoint
classes. This is the flat trace carrier used by the face-cone interfaces.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- One physical trace on a positive cubical base normalizes to one unit
face trace. The spatial and time formulas are literal, and both original
endpoint classes are transported by that same spatial map. -/
theorem exists_unit_cube_face_L2_trace_normalization {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {ε : ℝ} (hε : 0 < ε)
    {f : Domain n × ℝ → E} {g₀ g₁ : Domain n → E} :
    let S : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let B : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let G : Domain n → Domain n := fun x => a + (ε / 2) • x
    ∀ (H : C(Icc (0 : ℝ) ε, Lp E 2 (volume.restrict S)))
      (_hH : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
        ∃ hslice : MemLp (fun x => f (x, r)) 2 (volume.restrict S),
          H ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (x, r)))
      (hg₀ : MemLp g₀ 2 (volume.restrict S)) (hg₁ : MemLp g₁ 2 (volume.restrict S)),
      H ⟨0, le_rfl, hε.le⟩ = hg₀.toLp g₀ →
      H ⟨ε, hε.le, le_rfl⟩ = hg₁.toLp g₁ →
      ∃ K : C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => f (G x, (ε / 2) * (t + 1))) 2 (volume.restrict B),
            K ⟨t, ht.1.le, ht.2.le⟩ =
              hslice.toLp (fun x => f (G x, (ε / 2) * (t + 1)))) ∧
        (∃ hleft : MemLp (g₀ ∘ G) 2 (volume.restrict B),
          K ⟨-1, le_rfl, by norm_num⟩ = hleft.toLp (g₀ ∘ G)) ∧
        (∃ hright : MemLp (g₁ ∘ G) 2 (volume.restrict B),
          K ⟨1, by norm_num, le_rfl⟩ = hright.toLp (g₁ ∘ G)) ∧
        ∀ L : C(Icc (-1 : ℝ) 1, Lp E 2 (volume.restrict B)),
          (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
            ∃ hslice : MemLp (fun x => f (G x, (ε / 2) * (t + 1))) 2 (volume.restrict B),
              L ⟨t, ht.1.le, ht.2.le⟩ =
                hslice.toLp (fun x => f (G x, (ε / 2) * (t + 1)))) → L = K := by
  intro S B a G H hH hg₀ hg₁ hH₀ hH₁
  let F : Domain n ≃ₜ Domain n :=
    (Homeomorph.smul (Units.mk0 (ε / 2) (half_pos hε).ne')).trans (Homeomorph.addLeft a)
  have hF : (F : Domain n → Domain n) = G := rfl
  have hmap : Measure.map F (volume.restrict B) ≤
      ENNReal.ofReal (((ε / 2) ^ n)⁻¹) • volume.restrict S := by
    rw [hF]
    exact le_of_eq (map_affine_unit_cube_volume n hε)
  obtain ⟨J, _hJall, hJpull, _hJunique⟩ :=
    exists_continuous_L2_curve_homeomorph_pullback F ENNReal.ofReal_ne_top hmap H
  have hJ : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
      ∃ hslice : MemLp (fun x => f (G x, r)) 2 (volume.restrict B),
        J ⟨r, hr.1.le, hr.2.le⟩ = hslice.toLp (fun x => f (G x, r)) := by
    filter_upwards [hH] with r hr hrI
    obtain ⟨hrL, hrEq⟩ := hr hrI
    exact hJpull ⟨r, hrI.1.le, hrI.2.le⟩ (fun x => f (x, r)) hrL hrEq
  obtain ⟨hleft, hJ₀⟩ := hJpull ⟨0, le_rfl, hε.le⟩ g₀ hg₀ hH₀
  obtain ⟨hright, hJ₁⟩ := hJpull ⟨ε, hε.le, le_rfl⟩ g₁ hg₁ hH₁
  obtain ⟨K, _hcommute, hK, hK₀, hK₁, hKunique⟩ :=
    exists_unit_interval_L2_trace_of_positive_segment
      (f := fun p : Domain n × ℝ => f (G p.1, p.2)) hε J hJ
  exact ⟨K, hK, ⟨hleft, hK₀.trans hJ₀⟩, ⟨hright, hK₁.trans hJ₁⟩, hKunique⟩

/-- The actual normalized weak face map and its normalized normal trace use
the same full affine chart. Both physical raw endpoint classes are retained
on the unit base. -/
theorem unit_cube_face_sobolev_and_trace {n q : ℕ} {ε : ℝ} (hε : 0 < ε)
    {w : Domain (n + 1) → Ambient q} {Dw : Domain (n + 1) → Gradient (n + 1) q}
    (hw : MemW12
      ⟨⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
        isOpen_iInter_of_finite (fun j : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩ w Dw) :
    let S : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let B : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let U : OpenDomain (n + 1) :=
      ⟨⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin (n + 1) =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain (n + 1) := WithLp.toLp 2 (fun _ => ε / 2)
    let G := fun x : Domain n => a + (ε / 2) • x
    let F := fun y : Domain (n + 1) => A + (ε / 2) • y
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let V := w ∘ F
    let DV := fun y j => (ε / 2) • Dw (F y) j
    ∀ (H : C(Icc (0 : ℝ) ε, Lp (Ambient q) 2 (volume.restrict S)))
      (_hH : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) ε,
        ∃ hslice : MemLp (fun x => w (e.symm (x, EuclideanSpace.single (0 : Fin 1) r)))
          2 (volume.restrict S), H ⟨r, hr.1.le, hr.2.le⟩ =
          hslice.toLp (fun x => w (e.symm (x, EuclideanSpace.single (0 : Fin 1) r))))
      (g₀ g₁ : Domain n → Ambient q)
      (hg₀ : MemLp g₀ 2 (volume.restrict S)) (hg₁ : MemLp g₁ 2 (volume.restrict S)),
      H ⟨0, le_rfl, hε.le⟩ = hg₀.toLp g₀ →
      H ⟨ε, hε.le, le_rfl⟩ = hg₁.toLp g₁ →
      MemW12 U V DV ∧
      (∫ y in U.val, hsNormSq (DV y)) = (ε / 2) ^ (2 - ((n + 1 : ℕ) : ℤ)) *
        ∫ y in ⋂ j : Fin (n + 1), (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
          hsNormSq (Dw y) ∧
      ∃ K : C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict B)),
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
          ∃ hslice : MemLp (fun x => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))
            2 (volume.restrict B), K ⟨t, ht.1.le, ht.2.le⟩ =
            hslice.toLp (fun x => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)))) ∧
        (∃ hleft : MemLp (g₀ ∘ G) 2 (volume.restrict B),
          K ⟨-1, le_rfl, by norm_num⟩ = hleft.toLp (g₀ ∘ G)) ∧
        (∃ hright : MemLp (g₁ ∘ G) 2 (volume.restrict B),
          K ⟨1, by norm_num, le_rfl⟩ = hright.toLp (g₁ ∘ G)) := by
  intro S B U a A G F e V DV H hH g₀ g₁ hg₀ hg₁ hH₀ hH₁
  have hweak := memW12_unit_cube_normalization_energy (n := n + 1) (q := q) hε hw
  let f : Domain n × ℝ → Ambient q := fun p => w (e.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2))
  obtain ⟨K, hK, hleft, hright, _hunique⟩ :=
    exists_unit_cube_face_L2_trace_normalization (n := n) (E := Ambient q)
      (f := f) hε H hH hg₀ hg₁ hH₀ hH₁
  have hraw (x : Domain n) (t : ℝ) : f (G x, (ε / 2) * (t + 1)) =
      V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) := by
    have hcoord : F (e.symm (x, EuclideanSpace.single (0 : Fin 1) t)) =
        e.symm (G x, EuclideanSpace.single (0 : Fin 1) ((ε / 2) * (t + 1))) :=
      affine_unit_cube_split_coordinates n ε x t
    exact congrArg w hcoord.symm
  refine ⟨hweak.1, hweak.2.1, K, ?_, hleft, hright⟩
  filter_upwards [hK] with t ht htI
  have hfun : (fun x => f (G x, (ε / 2) * (t + 1))) =
      (fun x => V (e.symm (x, EuclideanSpace.single (0 : Fin 1) t))) :=
    funext fun x => hraw x t
  have hpackage : ∃ hslice : MemLp (fun x => f (G x, (ε / 2) * (t + 1)))
      2 (volume.restrict B), K ⟨t, htI.1.le, htI.2.le⟩ =
        hslice.toLp (fun x => f (G x, (ε / 2) * (t + 1))) := ht htI
  rw [hfun] at hpackage
  exact hpackage

end StratificationTheory
