module

public import HarmonicMaps.Sobolev
public import HarmonicMaps.Target
public import HarmonicMaps.Minimizer
public import HarmonicMaps.EnergyLemmas
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.Representative
public import HarmonicMaps.Analysis.Monotonicity
public import HarmonicMaps.Analysis.AffineBallSobolev
public import HarmonicMaps.Analysis.AffineZeroBoundary
public import HarmonicMaps.Analysis.AffineEnergyScaling
public import HarmonicMaps.Analysis.AffineMinimizerTransport
public import HarmonicMaps.Analysis.BallPolarIntegral
public import HarmonicMaps.Analysis.SphereSurfaceMeasure
public import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz
public import HarmonicMaps.Analysis.SobolevL2Closure
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HarmonicMaps.Analysis.SobolevPoincare
public import HarmonicMaps.Analysis.L2TranslationContinuity
public import HarmonicMaps.Analysis.SobolevPostcomposition
public import HarmonicMaps.Analysis.SobolevAECollar
public import HarmonicMaps.Analysis.ContinuousRepresentativeLocality
public import HarmonicMaps.Frozen.TubularProjection
public import HarmonicMaps.Frozen.SmallEnergyRegularity
public import HolderToCK.Frozen.SmallEnergySmoothRegularity
public import HolderToCK.Analysis.Bootstrap.AffineMinimizer
public import HolderToCK.Analysis.Bootstrap.SmoothRepresentativeTransport

/-!
# Imported harmonic-map interfaces

The domain, ambient space, displayed weak gradient, Sobolev predicates, target,
local minimizer, zero-boundary closure and energy are the upstream definitions.
The import list supplies existing monotonicity, affine transport, projection,
polar integration and small-energy regularity. It does not assert compactness,
boundary trace, density, tangent-map or stratification results.
-/
