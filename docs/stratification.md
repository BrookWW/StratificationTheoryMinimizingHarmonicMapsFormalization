# Minimizing harmonic maps: statements and proof

This guide describes the mathematical statements and the proof chain exposed
by `StratificationTheory`. The source manuscript is
[minimizer_stratification.tex](../sources/minimizer_stratification.tex).
The complete final joint is
[`StratificationTheory.stratification`](../StratificationTheory/Frozen/Stratification.lean).
It retains one original map, its explicit weak gradient and the same actual
singular strata throughout.

## Objects and normalization

`HarmonicMaps.Domain n` and `Ambient q` are Euclidean spaces.
`Gradient n q` is a finite family of coordinate columns; its Pi norm is not
the Hilbert–Schmidt norm used in energy. For the displayed weak gradient,

```math
|Du|_{\mathrm{HS}}^2=\sum_{i=1}^n|D_i u|^2,
\qquad
E(u;B)=\int_B |Du|_{\mathrm{HS}}^2,
\qquad
\Theta_u(a,r)=r^{2-n}E(u;B_r(a)).
```

There is no factor $1/2$. `dirichletEnergy` is extended nonnegative real
valued; real energy conversions use proved local finiteness.
`MemW12Loc` supplies actual local $L^2$ data and distributional derivatives.
`IsLocallyEnergyMinimizing` compares with every target-valued Sobolev map
whose difference belongs to the actual function-and-gradient
$W^{1,2}_0$ closure on each ball with contained closed ball.

The target is nonempty, compact and smoothly embedded, without boundary.
Smoothness, projection estimates and regularity conclusions are not fields
of the minimizing-map predicate. A regular point has a smooth a.e.
representative on a neighborhood; singularity concerns this map class.

Monotonicity gives a finite nonnegative named density

```math
\Theta_u(a)=\lim_{r\downarrow0}\Theta_u(a,r)
           =\inf_{0 \lt r \lt R_a}\Theta_u(a,r),
\qquad \overline{B_{R_a}(a)}\subset\Omega.
```

The complete density characterization proves independence of the admissible
outer radius. Upstream smooth small-energy regularity gives one positive
threshold depending only on $n,N$: regular points have zero density, and
every singular point has density at least that same threshold.
The preliminary estimate is $\mathcal H^{n-2}(\Sigma(u))=0$.

## One connector for both Luckhaus estimates

`luckhaus_joint` chooses $C_n \gt 0$ before $q$, the compact target set, both
sphere maps and $0 \lt \varepsilon \lt 1/8$. Its witnesses include the actual cylinder
map, its full Sobolev membership, a finite radial annular weak extension,
and native spatial/time columns. Native surface measure is the Euclidean
Hausdorff measure of the appropriate dimension.

The raw extension agrees with the original cylinder map at every stated
radius and interior time. The weak-column coherence has its original
almost-everywhere radial quantifier. The native columns are $L^2$,
spatially tangent and have integrable Hilbert–Schmidt energy. The energy and
target-distance inequalities, and both named endpoint trace classes, all
refer to this same construction. Restricting an arbitrary ambient weak
gradient representative to a null surface is not used.

The uniform proof selects one translated grid with joint qualifications
for the original pair. Coordinate-line interpolation supplies the first
connectors. A dimension-generic successor constructs the next cell from its
actual shared lower faces and original horizontal data. It preserves raw
trace classes, all-rank physical energies and distance bounds. Finite mesh
assembly produces a genuine weak map and global time traces. Actual spatial
cylinder slicing, with constant-time extension for endpoint qualification,
then supplies the native connector and both named traces.

## Annular comparison and compactness

The projected annular operator consumes the genuine Luckhaus packet.
Its distance estimate first gives the tube condition for the smooth target
projection. Native radial coherence transports the actual column energy to
the annulus; the complete trace curve retains both endpoint classes.

For a comparison radius r and $0 \lt \eta \lt 1/8$, put

```math
\ell=\frac r{1+\eta},\qquad \tau=1+\eta.
```

Compress the competitor into $B_\ell$ using the actual affine pullback and
insert the projected connector on $\ell \lt |x| \lt r$. Its matching radial classes
produce the original zero-boundary difference required by minimality.
The compressed energy factor is $\tau^{2-n}\le1$ for every $n\ge2$.
The resulting comparison cost is controlled by

```math
8C_n r^{n-2}\bigl(\eta A+\eta^{-1}D\bigr).
```

The printed full-annulus Corollary 10.24 repair is not imported as a proved
result or assumed by compactness. The proof uses this actual inner-ball
compression comparison. The manuscript records the printed discrepancy;
its displayed proposed repair is not an additional public theorem.

Hilbert weak extraction and interior Rellich compactness give one Sobolev
limit. Comparison with every original $W^{1,2}_0$ competitor proves limit
minimality. Applying the energy comparison to arbitrary subsubsequences
gives full energy convergence on contained balls. Hilbert norm identities
then give strong gradient columns; finite interior-ball covers yield strong
convergence on every compact subset of the source domain. One common
subsequence and one limit retain all these conclusions.

## Whole-sequence density upper semicontinuity

For prescribed weak local $L^2$ convergence, the given limit map has actual
local $L^2$ membership and convergence of its pairings against every
compact-set $L^2$ test. No Sobolev gradient, target membership, minimality or
energy convergence of the limit is assumed.

Strong extraction identifies the first limit with the prescribed map by
weak-limit uniqueness and constructs its actual gradient and minimizing
data. Every subsequence has a strong subsubsequence with the same map and
weak gradient. The subsequence criterion therefore gives strong convergence
of the whole original sequence and actual ball energy convergence.

For $y_k\to y$, take fixed admissible $r,h \gt 0$. Eventually
$B_r(y_k)\subset B_{r+h}(y)$, so

```math
\Theta_{u_k}(y_k)\le r^{2-n}E(u_k;B_{r+h}(y)).
```

Pass to the energy limit, then let $h\downarrow0$, and finally $r\downarrow0$.
Actual eventual upper bounds and nonnegative lower bounds justify the real
limsup. The result also gives an eventual upper bound at every positive
tolerance. Positive density levels persist with the correct non-strict
inequality, and singular points persist by the uniform density gap.

## Global tangents and their spines

Fix any positive sequence $\rho_k\to0$ at an interior point a. Actual affine
transport and monotonicity supply Sobolev, minimizing and energy data on
every fixed ball once k is large. Coherent diagonal extraction and agreement
on overlapping balls give **one global map and one original-index
subsequence**. For the same $\varphi,D\varphi$,

```math
u(a+\rho_{\kappa(k)}\,\cdot)\longrightarrow\varphi
\quad\text{strongly in }W^{1,2}_{\mathrm{loc}}(\mathbb R^n),
\qquad
R^{2-n}E(\varphi;B_R)=\Theta_u(a)\quad\text{for every }R \gt 0.
```

The named origin density of that tangent equals the same constant. Constant
normalized energy forces the radial derivative to vanish, giving a.e.
zero homogeneity for every fixed positive dilation.

`IsTangentAt` is the raw convergence relation with actual $L^2$
qualifications. `IsTangentAt.qualification` derives the global weak graph,
target values, local minimality, all-radius energy and homogeneity for every
map and gradient in that relation. Source regularity is equivalent to the
a.e. constancy of any actual tangent. Every tangent at a singular point is
therefore nonconstant.

For a global homogeneous minimizer, centered-energy bounds and increasing
outer radii give $\Theta_\varphi(z)\le\Theta_\varphi(0)$. Equality gives
homogeneity about z and a.e. translation invariance in that direction.
The equality carrier is one genuine linear subspace, the named `spine`.
Its full characterization retains the carrier, density bound and all
fixed-parameter translations. For a nonconstant tangent its spine lies in
its singular set. The preliminary Hausdorff-null theorem then forces
$\dim S(\varphi)\le n-3$ when $n\ge3$.

## Concentration, covering and the final joint

`singularStratum` quantifies over **all** raw tangent maps and gradients;
their qualifications are derived individually. Its strata are monotone,
and for $n\ge3$ the top three stated strata equal $\Sigma(u)$.

At $a\in S_j(u)$, $j\le n$, and for every $\delta \gt 0$, the source proof gives
one $\varepsilon \gt 0$ such that every admissible $0 \lt \rho\le\varepsilon$ admits
a j-plane $L_{a,\rho}$ with

```math
\Theta_u(x)\ge\Theta_u(a)-\varepsilon,\quad x\in B_\rho(a)
\quad\Longrightarrow\quad
\mathrm{dist}(x,a+L_{a,\rho}) \lt \delta\rho.
```

The same epsilon controls scale and density tolerance, and the implication
covers all source-domain points x meeting those conditions. A failure would
produce a prescribed shrinking sequence and high-density points outside a
plane containing the tangent spine. Compactness of the closed unit ball and
actual blow-up density upper semicontinuity place the limiting point in the
same spine, a contradiction.

`HasDeltaApproximation` is the literal uniform affine approximation property
for an actual set. The complete covering theorem gives one positive
$\beta(\delta)\to0$ with $\mathcal H^{j+\beta(\delta)}(A)=0$ whenever that
property holds, for $j\le n$. Actual child balls are recentered in the set;
cardinality, radius and diameter factors are retained at every iteration.

For each fixed delta, form countably many radius/density pieces of the
stratum and apply the covering theorem to each piece. Take that countable
union before letting delta tend to zero for the whole stratum. This yields
$\mathcal H^s(S_j(u))=0$ for every $s \gt j$, hence $\dim_{\mathrm H}S_j(u)\le j$.
The bound implies the printed $\le n-3$ consequence on its index range.

In dimension three, a putative interior accumulation of singular points
would give a nonzero unit-direction point of a homogeneous tangent with
positive density. Homogeneity creates a singular ray, contradicting the
preliminary $\mathcal H^1$ singular nullity. This proves actual interior
no-accumulation of the entire singular set. It does not infer discreteness
from Hausdorff dimension zero, or exclude boundary accumulation.
In dimension two, vanishing small-ball energy and small-energy regularity
give the separate exact conclusion $\Sigma(u)=\varnothing$.

## Lean examples

Every example uses only the public entry point. The following checks the
complete original finite-input strong compactness interface.

```lean
module
public import StratificationTheory

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
set_option autoImplicit false

example {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q)
    (Du : ℕ → Domain n → Gradient n q)
    (hSobolev : ∀ k, MemW12 Ω (u k) (Du k))
    (hTarget : ∀ k, TakesValuesIn N Ω (u k))
    (hMinimizer : ∀ k, IsLocallyEnergyMinimizing N Ω (u k) (Du k))
    (hEnergy : ∀ (a : Domain n) (r : ℝ), 0 < r →
      Metric.closedBall a r ⊆ Ω.val →
      ∃ C : ℝ≥0, ∀ k, dirichletEnergy (Du k) (Metric.ball a r) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Domain n → Ambient q)
      (Dv : Domain n → Gradient n q),
      StrictMono κ ∧ MemW12Loc Ω v Dv ∧ TakesValuesIn N Ω v ∧
      IsLocallyEnergyMinimizing N Ω v Dv ∧
      ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K))
          atTop (𝓝 0) ∧
        ∀ i : Fin n,
          Tendsto (fun k => eLpNorm (fun x => Du (κ k) x i - Dv x i)
            2 (volume.restrict K)) atTop (𝓝 0) := by
  exact StratificationTheory.strongCompactness hn N Ω u Du
    hSobolev hTarget hMinimizer hEnergy
```

The low-dimensional endpoint has no subtraction convention in its type.

```lean
module
public import StratificationTheory

open HarmonicMaps Set
set_option autoImplicit false

example {q : ℕ} (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain 2)
    (u : Domain 2 → Ambient q) (Du : Domain 2 → Gradient 2 q)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) :
    StratificationTheory.singularSet Ω u = ∅ := by
  exact StratificationTheory.singularSet_eq_empty_two_dimensional N Ω u Du hu hN hmin
```

The prescribed-scale source returns a raw tangent without assuming tangent
qualifications as inputs. Its complete result additionally retains the
same witnesses' global minimizing graph, strong convergence, energy and
homogeneity.

```lean
module
public import StratificationTheory

open HarmonicMaps Filter
open scoped Topology
set_option autoImplicit false

example {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du)
    (a : Ω.val) (ρ : ℕ → PositiveRadius)
    (hρ : Tendsto (fun k => (ρ k).val) atTop (𝓝 (0 : ℝ))) :
    ∃ (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
      StratificationTheory.IsTangentAt u Du a.val φ Dφ := by
  obtain ⟨_κ, φ, Dφ, _hκ, _hW, _hTarget, _hMin,
    _hStrong, _hEnergy, _hHomogeneous, hTangent⟩ :=
    StratificationTheory.exists_tangent_along_prescribed_scales
      hn N Ω u Du hu hN hmin a ρ hρ
  exact ⟨φ, Dφ, hTangent⟩
```

## Verification and reuse

The [README](../README.md#build-and-verify) gives the reproducible build,
source/type/axiom checks and compiled-declaration kernel replay commands.
The pinned dependency provides the Sobolev and minimizer definitions,
small-energy regularity, monotonicity and affine transport; Mathlib provides
the surrounding analysis and geometry. The same imported definitions are
used by every theorem in the chain.

The scope is interior minimizing-map stratification for $n\ge2$, with the
empty singular-set theorem in dimension two and the stratification joint
for $n\ge3$. No conclusion here asserts finite total singular cardinality,
boundary regularity, rectifiability, quantitative stratification or uniqueness
of tangent maps. The mathematical manuscript preserves source statements
and their explicitly identified corrections; only the actual proved Lean
interfaces are advertised as theorems.
