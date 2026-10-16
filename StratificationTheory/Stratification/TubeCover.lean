/- Copyright (c) 2026 BrookWW. All rights reserved. -/
module

public import StratificationTheory.Stratification.DiskPacking
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Recentered finite covers of subspace tubes

Actual orthogonal projection places the bounded part of a tube in a
subspace disk. A separated disk net gives plane-centered balls; the balls
meeting the set are retained and recentered at actual points of the set.
The finite covering and the quantitative cardinal bound concern these same
recentered centers.
-/

public section

open HarmonicMaps Metric Set Module

namespace StratificationTheory

/-- A bounded set close to an actual affine subspace has a quantitative
finite cover with centers in the set and radius `4 δ R`. The disk net,
selection of intersecting balls, and recentering are proved internally. -/
theorem exists_finset_recentered_subspace_tube_cover {n : ℕ}
    (A : Set (Domain n)) (a : Domain n) (V : Submodule ℝ (Domain n))
    (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (htube : ∀ x ∈ A ∩ ball a R,
      dist x (a + (V.orthogonalProjectionOnto (x - a) : Domain n)) ≤ δ * R) :
    ∃ centers : Finset (Domain n),
      (∀ c ∈ centers, c ∈ A ∩ ball a R) ∧
      (∀ x ∈ A ∩ ball a R, ∃ c ∈ centers, dist x c < 4 * δ * R) ∧
      (centers.card : ℝ) ≤ (5 : ℝ) ^ finrank ℝ V / δ ^ finrank ℝ V := by
  classical
  let S : Set (Domain n) := A ∩ ball a R
  let center : V → Domain n := fun p => a + p.val
  obtain ⟨P, _hPbound, _hPsep, hPcover, hPcard⟩ :=
    exists_finset_subspace_disk_net_small_scale V R δ hR hδ hδone
  have hplanecover : ∀ x ∈ S, ∃ p ∈ P, dist x (center p) < 2 * δ * R := by
    intro x hx
    let p : V := V.orthogonalProjectionOnto (x - a)
    have hxnorm : ‖x - a‖ < R := by
      simpa only [mem_ball, dist_eq_norm] using hx.2
    have hpbound : ‖(p : Domain n)‖ ≤ R :=
      (V.norm_orthogonalProjectionOnto_apply_le (x - a)).trans hxnorm.le
    obtain ⟨y, hy, hpy⟩ := hPcover p hpbound
    refine ⟨y, hy, ?_⟩
    calc
      dist x (center y) ≤ dist x (center p) + dist (center p) (center y) :=
        dist_triangle _ _ _
      _ < δ * R + δ * R := add_lt_add_of_le_of_lt (htube x hx)
        (by simpa only [center, dist_add_left] using hpy)
      _ = 2 * δ * R := by ring
  let T : Finset V := P.filter (fun p => ∃ x ∈ S, dist x (center p) < 2 * δ * R)
  have hchoose (p : T) : ∃ x ∈ S, dist x (center p.val) < 2 * δ * R :=
    (Finset.mem_filter.mp p.property).2
  choose z hzS hzclose using hchoose
  let centers : Finset (Domain n) := Finset.univ.image z
  have hcenters : ∀ c ∈ centers, c ∈ S := by
    intro c hc
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hc
    exact hzS p
  have hcover : ∀ x ∈ S, ∃ c ∈ centers, dist x c < 4 * δ * R := by
    intro x hx
    obtain ⟨p, hpP, hxp⟩ := hplanecover x hx
    have hpT : p ∈ T := Finset.mem_filter.mpr ⟨hpP, x, hx, hxp⟩
    let p' : T := ⟨p, hpT⟩
    have hzp : dist (center p) (z p') < 2 * δ * R := by
      rw [dist_comm]
      exact hzclose p'
    refine ⟨z p', Finset.mem_image.mpr ⟨p', Finset.mem_univ _, rfl⟩, ?_⟩
    calc
      dist x (z p') ≤ dist x (center p) + dist (center p) (z p') := dist_triangle _ _ _
      _ < 2 * δ * R + 2 * δ * R := add_lt_add hxp hzp
      _ = 4 * δ * R := by ring
  have hcard : centers.card ≤ P.card := by
    calc
      centers.card ≤ (Finset.univ : Finset T).card := Finset.card_image_le
      _ = T.card := by rw [Finset.card_univ, Fintype.card_coe]
      _ ≤ P.card := Finset.card_filter_le _ _
  exact ⟨centers, hcenters, hcover, (Nat.cast_le.mpr hcard).trans hPcard⟩

end StratificationTheory
