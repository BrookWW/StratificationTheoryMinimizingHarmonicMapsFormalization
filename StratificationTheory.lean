module

public import StratificationTheory.Upstream
public import StratificationTheory.Frozen.RegularDensity
public import StratificationTheory.Frozen.SingularSetNull
public import StratificationTheory.Frozen.SpineWellDefined
public import StratificationTheory.Frozen.SpineCharacterization
public import StratificationTheory.Frozen.SpineCodimension
public import StratificationTheory.Frozen.FlatCover
public import StratificationTheory.Frozen.SphereSobolev
public import StratificationTheory.Frozen.SphereTargetValues
public import StratificationTheory.Frozen.SphereSlices

public import StratificationTheory.Frozen.SphereGradientWellDefined

public import StratificationTheory.Frozen.SphereGradientCharacterization

public import StratificationTheory.Frozen.UnitCylinder
public import StratificationTheory.Frozen.CylinderSobolev
public import StratificationTheory.Frozen.CylinderTraceWellDefined
public import StratificationTheory.Frozen.CylinderTraceCharacterization

public import StratificationTheory.Frozen.SphereSliceEnergy

public import StratificationTheory.Frozen.AmbientRadialTraceWellDefined
public import StratificationTheory.Frozen.SphereRadialBallExtension
public import StratificationTheory.Frozen.CylinderAnnularTransfer
public import StratificationTheory.Frozen.RadialTraceGluing

public import StratificationTheory.Frozen.FullGridSobolevPairV2
public import StratificationTheory.Frozen.CoordinateTraceJoint
public import StratificationTheory.Frozen.ClosedTargetGridJoint
public import StratificationTheory.Frozen.AffineAnnularPostcomposition
public import StratificationTheory.Frozen.CubicalFaceConeExtensionV2
public import StratificationTheory.Frozen.LuckhausJoint
public import StratificationTheory.Frozen.StrongCompactness
public import StratificationTheory.Compactness.GeneralStrongEnergyCompactness
public import StratificationTheory.Compactness.PlanarStrongCompactness
public import StratificationTheory.Interpolation.CircleLuckhausJoint

public import StratificationTheory.Foundation.DensityJointUpperSemicontinuity
public import StratificationTheory.Foundation.DensityPersistence
public import StratificationTheory.Foundation.TwoDimensionalEnergy
public import StratificationTheory.TangentMaps.PrescribedTangentExtraction
public import StratificationTheory.TangentMaps.TangentQualification
public import StratificationTheory.TangentMaps.TangentNonconstant
public import StratificationTheory.Stratification.StratificationComplete
public import StratificationTheory.Stratification.DeltaApproximationCover
public import StratificationTheory.Frozen.Stratification

/-!
# Minimizer stratification

The entry point exposes the imported harmonic-map interfaces and the proved
source density, regularity, singular-set, spine, slicing, trace, interpolation,
arbitrary-dimensional Luckhaus and strong compactness declarations. The same
compactness subsequence retains actual local energy convergence. Prescribed
weak local L2 map limits have whole-sequence strong convergence and joint
moving-center density upper semicontinuity. Prescribed positive scales yield
one global locally minimizing tangent with the original density energy and
zero homogeneity, and every actual raw tangent has these qualifications.
The universal actual-tangent strata have the stated top strata, density
concentration and stratified Hausdorff bounds. In dimension three the singular
set has no accumulation inside the original domain. All objects use the
upstream Sobolev map, displayed weak gradient and original ball-competitor
local minimality predicates.
-/
