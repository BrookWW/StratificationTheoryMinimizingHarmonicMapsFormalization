module

public import StratificationTheory.Foundation.AffineDomainSobolevPullback
public import StratificationTheory.Foundation.CoordinateFaceNativeMeasure

/-!
# Native affine coordinates of a positive cubical face

The literal positive similarity from the unit cube to (0,epsilon)^n has its
exact restricted native volume, original weak columns and energy scaling.
-/

public section
open HarmonicMaps MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace StratificationTheory

/-- The actual affine face map sends the whole open unit cube exactly onto
the whole open positive parameter cube. -/
theorem affine_unit_cube_preimage_positive_cube (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let G : Domain n → Domain n := fun x => a + (ε / 2) • x
    let B : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let S : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    G ⁻¹' S = B := by
  intro a G B S
  ext x
  simp only [S, B, mem_preimage, mem_iInter]
  change (∀ j : Fin n, (G x) j ∈ Ioo (0 : ℝ) ε) ↔
    ∀ j : Fin n, x j ∈ Ioo (-1 : ℝ) 1
  have hr : 0 < ε / 2 := half_pos hε
  have hcoord (j : Fin n) : (G x) j ∈ Ioo (0 : ℝ) ε ↔ x j ∈ Ioo (-1 : ℝ) 1 := by
    change (0 < ε / 2 + (ε / 2) * x j ∧ ε / 2 + (ε / 2) * x j < ε) ↔
      (-1 < x j ∧ x j < 1)
    constructor
    · intro h
      constructor <;> nlinarith only [hr, h.1, h.2]
    · intro h
      constructor <;> nlinarith only [hr, h.1, h.2]
  exact forall_congr' hcoord

/-- The same literal affine unit-face map has the exact restricted native
volume coefficient, including the zero-dimensional base. -/
theorem map_affine_unit_cube_volume (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let G : Domain n → Domain n := fun x => a + (ε / 2) • x
    let B : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1
    let S : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    Measure.map G (volume.restrict B) =
      ENNReal.ofReal (((ε / 2) ^ n)⁻¹) • volume.restrict S := by
  intro a G B S
  have hpre : G ⁻¹' S = B := affine_unit_cube_preimage_positive_cube n hε
  have hEmb : MeasurableEmbedding G := by
    simpa only [sub_zero] using affineBall_measurableEmbedding a 0 (half_pos hε).ne'
  have hmap : Measure.map G volume = ENNReal.ofReal (((ε / 2) ^ n)⁻¹) • volume := by
    simpa only [sub_zero] using affineBall_map_volume a 0 (half_pos hε)
  rw [← hpre, ← hEmb.restrict_map, hmap, Measure.restrict_smul]

/-- The physical positive parameter cube has its exact native Euclidean
volume; in particular all original finite face carriers are finite. -/
theorem volume_native_positive_cube (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let S : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    (volume : Measure (Domain n)) S = ENNReal.ofReal (ε ^ n) := by
  intro S
  have hS : MeasurableSet S := MeasurableSet.iInter fun j : Fin n =>
    measurableSet_Ioo.preimage (EuclideanSpace.proj j).continuous.measurable
  have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → Domain n) ⁻¹' S =
      Set.univ.pi (fun _ : Fin n => Ioo (0 : ℝ) ε) := by
    ext t
    simp only [S, mem_preimage, mem_iInter, Set.mem_pi, Set.mem_univ, forall_const]
    rfl
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage hS.nullMeasurableSet, hpre,
    Real.volume_pi_Ioo]
  simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow hε.le]

/-- The same full unit-face similarity splits into the same spatial base
similarity and the literal affine time normalization. -/
theorem affine_unit_cube_split_coordinates (n : ℕ) (ε : ℝ)
    (x : Domain n) (t : ℝ) :
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let A : Domain (n + 1) := WithLp.toLp 2 (fun _ => ε / 2)
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    A + (ε / 2) • e.symm (x, EuclideanSpace.single (0 : Fin 1) t) =
      e.symm (a + (ε / 2) • x,
        EuclideanSpace.single (0 : Fin 1) ((ε / 2) * (t + 1))) := by
  intro a A e
  have hA : e A = (a, EuclideanSpace.single (0 : Fin 1) (ε / 2)) := by
    apply Prod.ext
    · ext j
      simp [e, A, a, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
        PiLp.sumPiLpEquivProdLpPiLp]
    · ext j
      fin_cases j
      simp [e, A, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
        PiLp.sumPiLpEquivProdLpPiLp]
  apply e.injective
  rw [map_add, map_smul, e.apply_symm_apply, hA, e.apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext j
    fin_cases j
    change ε / 2 + (ε / 2) * t = (ε / 2) * (t + 1)
    ring

/-- The same unit-face normalization retains the original weak pair and
its precise dimensionally scaled native energy, together with every source
native a.e. value constraint. -/
theorem memW12_unit_cube_normalization_energy {n q : ℕ} {ε : ℝ} (hε : 0 < ε)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12
      ⟨⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε,
        isOpen_iInter_of_finite (fun j : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩ w Dw) :
    let a : Domain n := WithLp.toLp 2 (fun _ => ε / 2)
    let G : Domain n → Domain n := fun x => a + (ε / 2) • x
    let B : OpenDomain n :=
      ⟨⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1,
        isOpen_iInter_of_finite (fun j : Fin n =>
          isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩
    let S : Set (Domain n) := ⋂ j : Fin n, (EuclideanSpace.proj j) ⁻¹' Ioo (0 : ℝ) ε
    let D : Domain n → Gradient n q := fun x j => (ε / 2) • Dw (G x) j
    MemW12 B (w ∘ G) D ∧
      (∫ x in B.val, hsNormSq (D x)) =
        (ε / 2) ^ (2 - (n : ℤ)) * ∫ x in S, hsNormSq (Dw x) ∧
      dirichletEnergy D B.val =
        ENNReal.ofReal ((ε / 2) ^ (2 - (n : ℤ))) * dirichletEnergy Dw S ∧
      ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict S, P (w x)) →
        ∀ᵐ x ∂volume.restrict B.val, P ((w ∘ G) x) := by
  intro a G B S D
  have hfinite : (volume : Measure (Domain n)) S ≠ ⊤ := by
    rw [volume_native_positive_cube n hε]
    exact ENNReal.ofReal_ne_top
  have hSopen : IsOpen S := isOpen_iInter_of_finite fun j : Fin n =>
    isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous
  let Ω : OpenDomain n := ⟨S, hSopen⟩
  have hw' : MemW12 Ω w Dw := hw
  have hdata := memW12_affine_preimage_energy (n := n) (q := q) (Ω := Ω)
    (u := w) (Du := Dw) hfinite hw' a 0 (half_pos hε)
  have hpre : G ⁻¹' S = B.val := affine_unit_cube_preimage_positive_cube n hε
  have hGcont : Continuous G :=
    continuous_const.add ((continuous_id : Continuous (fun x : Domain n => x)).const_smul (ε / 2))
  have hdomain : (⟨G ⁻¹' S, hSopen.preimage hGcont⟩ : OpenDomain n) = B := by
    exact Subtype.ext hpre
  dsimp only at hdata
  simp only [sub_zero] at hdata
  have hW : MemW12 B (w ∘ G) D := by
    have h := hdata.1
    change MemW12 ⟨G ⁻¹' S, hSopen.preimage hGcont⟩ (w ∘ G) D at h
    rwa [hdomain] at h
  have hE : (∫ x in G ⁻¹' S, hsNormSq (D x)) =
      (ε / 2) ^ (2 - (n : ℤ)) * ∫ x in S, hsNormSq (Dw x) := hdata.2.2.1
  have hDir : dirichletEnergy D (G ⁻¹' S) =
      ENNReal.ofReal ((ε / 2) ^ (2 - (n : ℤ))) * dirichletEnergy Dw S := hdata.2.2.2.1
  have hValues : ∀ P : Ambient q → Prop, (∀ᵐ x ∂volume.restrict S, P (w x)) →
      ∀ᵐ x ∂volume.restrict (G ⁻¹' S), P ((w ∘ G) x) := hdata.2.2.2.2
  rw [hpre] at hE hDir hValues
  exact ⟨hW, hE, hDir, hValues⟩

end StratificationTheory
