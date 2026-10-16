module

public import StratificationTheory.Foundation.ThreeCoordinatePrismFacetBoundary
public import StratificationTheory.Foundation.ThreeCoordinatePrismTemporalCaps

public section

open HarmonicMaps Set

namespace StratificationTheory

/-- All original signed caps of each first-prism facet agree pointwise
with the same physical lower-boundary representative. -/
theorem three_coordinate_prism_all_original_cap_values {N q : ℕ}
    (w : Fin 2 → Domain N → Ambient q)
    (rep : Fin 2 → Fin N → Domain N → Ambient q)
    (coord : Fin 3 ↪ Fin N) {ε : ℝ} (hε : 0 < ε) (y : Domain N)
    (i : Fin 3) (sideI : Bool) :
    let pair : Fin 2 ↪ Fin N :=
      (Fin.castSuccEmb.trans (Equiv.swap (Fin.last 2) i).toEmbedding).trans coord
    let origin := y + (if sideI then ε else 0) • EuclideanSpace.single (coord i) (1 : ℝ)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let e₃ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 1)
    let P := fun z : Domain 3 => y + ∑ k : Fin 3,
      (ε / 2 + (ε / 2) * z k) • EuclideanSpace.single (coord k) (1 : ℝ)
    let free := fun z : Domain 3 => if |z 0| < 1 then (0 : Fin 3) else if |z 1| < 1 then 1 else 2
    let E := fun z : Domain 4 =>
      let sp : Domain 3 := WithLp.toLp 2 ![z 0, z 1, z 2]
      if z 3 = -1 then w 0 (P sp) else if z 3 = 1 then w 1 (P sp) else
        (1 - (z 3 + 1) / 2) • rep 0 (coord (free sp)) (P sp) +
          ((z 3 + 1) / 2) • rep 1 (coord (free sp)) (P sp)
    let embed := fun t : Domain 2 => origin + t 0 • EuclideanSpace.single (pair 0) (1 : ℝ) +
      t 1 • EuclideanSpace.single (pair 1) (1 : ℝ)
    let edgePoint := fun (a : Fin 2) (side : Bool) (s : ℝ) => cubicalSignedFaceIsometry 1 a true
      (b.symm (EuclideanSpace.single (0 : Fin 1) s,
        EuclideanSpace.single (0 : Fin 1) (if side then ε else 0)))
    let F := fun a side l s => rep l (pair ((Equiv.swap (0 : Fin 2) 1) a)) (embed (edgePoint a side s))
    let T := fun z : Domain 2 => WithLp.toLp 2 (fun _ => ε / 2) + (ε / 2) • z
    let V := fun (a : Fin 2) (side : Bool) (z : Domain 2) =>
      (1 - (b (T z)).2 0 / ε) • F a side 0 ((b (T z)).1 0) +
        ((b (T z)).2 0 / ε) • F a side 1 ((b (T z)).1 0)
    let U := fun side : Bool => w (if side then 1 else 0) ∘ embed ∘ T
    let face := fun j : Fin 3 × Bool => if j.1 = 0 then V 0 j.2 ∘ cubicalSignedFaceIsometry 1 0 true
      else if j.1 = 1 then V 1 j.2 else U j.2
    let A := cubicalSignedFaceIsometry 2 i true
    let facet := fun z : Domain 3 => cubicalSignedFaceIsometry 3 i.castSucc sideI
      (e₃.symm (A z, EuclideanSpace.single (0 : Fin 1) 1))
    ∀ (j : Fin 3 × Bool) (x : Domain 2),
      x ∈ ⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1 →
      E (facet (cubicalSignedFaceIsometry 2 j.1 j.2
        (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) = face j x := by
  intro pair origin b e e₃ P free E embed edgePoint F T V U face A facet
  have hS := three_coordinate_prism_spatial_facet_edge_values w rep coord hε y i sideI
  change ∀ (a : Fin 2) (positive : Bool) (x : Domain 2),
    x ∈ ⋂ k : Fin 2, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1 →
    E (facet (cubicalSignedFaceIsometry 2 a.castSucc positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) =
      V a positive (cubicalSignedFaceIsometry 1 a true x) at hS
  have hT := fun (positive : Bool) (x : Domain 2) =>
    three_coordinate_prism_facet_temporal_cap_values w rep coord ε y i sideI positive x
  change ∀ (positive : Bool) (x : Domain 2),
    E (facet (cubicalSignedFaceIsometry 2 (2 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) = U positive x at hT
  dsimp only [face]
  generalize hE : E = E₀ at hS hT ⊢
  generalize hFacet : facet = F₀ at hS hT ⊢
  generalize hU : U = U₀ at hT ⊢
  generalize hV : V = V₀ at hS ⊢
  intro ⟨j, positive⟩ x hx
  fin_cases j
  · change E₀ (F₀ (cubicalSignedFaceIsometry 2 (0 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) =
      V₀ 0 positive (cubicalSignedFaceIsometry 1 0 true x)
    exact hS 0 positive x hx
  · change E₀ (F₀ (cubicalSignedFaceIsometry 2 (1 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) = V₀ 1 positive x
    have hId : cubicalSignedFaceIsometry 1 (1 : Fin 2) true x = x := by
      ext k
      fin_cases k <;> simp [cubicalSignedFaceIsometry_coordinate]
    have h := hS (1 : Fin 2) positive x hx
    change E₀ (F₀ (cubicalSignedFaceIsometry 2 (1 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) =
      V₀ 1 positive (cubicalSignedFaceIsometry 1 (1 : Fin 2) true x) at h
    rwa [hId] at h
  · change E₀ (F₀ (cubicalSignedFaceIsometry 2 (2 : Fin 3) positive
      (e.symm (x, EuclideanSpace.single (0 : Fin 1) 1)))) = U₀ positive x
    exact hT positive x

end StratificationTheory
