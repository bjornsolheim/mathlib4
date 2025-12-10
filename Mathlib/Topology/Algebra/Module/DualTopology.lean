/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.LocallyConvex.StrongTopology
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# Automatic topology on the algebraic dual

This file provides scoped instances that, when activated via `open DualTopology`,
equip the algebraic dual `Dual 𝕜 E` with topological structure induced from the
continuous dual `E →L[𝕜] 𝕜`. This applies when `E` is a finite-dimensional
Hausdorff topological vector space over a complete nontrivially normed field `𝕜`.

In addition, this file provides:

* `LocallyConvexSpace ℝ (Dual ℝ E)` for real vector spaces
* `(dualPairing 𝕜 E).IsContPerfPair` using the scoped topology instances
* `(dualPairing 𝕜 E).IsContPerfPair` using explicit topology assumptions on `Dual 𝕜 E`

## Motivation

For finite-dimensional spaces, the algebraic dual `Dual 𝕜 E` is linearly equivalent to
the continuous dual `E →L[𝕜] 𝕜`. This file makes the induced topology automatic,
reducing explicit assumptions in theorems about finite-dimensional duality.

## Namespaces

The instances are organized into four namespaces:

* `DualTopology`: Core topology instances
  - `[TopologicalSpace (Dual 𝕜 E)]`
  - `[IsTopologicalAddGroup (Dual 𝕜 E)]`
  - `[ContinuousSMul 𝕜 (Dual 𝕜 E)]`
  - `[T2Space (Dual 𝕜 E)]`

* `DualTopology.LocallyConvex`: Local convexity for real scalars
  - `[LocallyConvexSpace ℝ (Dual ℝ E)]`

* `DualTopology.ContPerfPair`: Continuous perfect pairing instance
(uses DualTopology core topology instances)
  - `(dualPairing 𝕜 E).IsContPerfPair`

* `ContPerfPairExplicit`: Continuous perfect pairing with explicit topology assumptions
  - `(dualPairing 𝕜 E).IsContPerfPair` (independent of `DualTopology`)

## Usage

```
open DualTopology                      -- basic topology
open DualTopology.LocallyConvex        -- adds LocallyConvexSpace
open DualTopology.ContPerfPair         -- adds IsContPerfPair (uses DualTopology topology instances)
open ContPerfPairExplicit              -- adds IsContPerfPair (using declared topology)
```

## Implementation notes

The typeclass assumptions are those needed for `Dual 𝕜 E ≃L[𝕜] E →L[𝕜] 𝕜` via
`continuous_of_finiteDimensional`.

Instances are **scoped** because:
1. Avoids instance diamonds when `Dual 𝕜 E` has a topology from elsewhere
2. Explicit choice via opening "instance namespace"

## Assumptions still required on the base space

The base space `E` still requires explicit assumptions:
- `[TopologicalSpace E]`
- `[IsTopologicalAddGroup E]`
- `[ContinuousSMul 𝕜 E]`
- `[T2Space E]`

This is because `isModuleTopologyOfFiniteDimensional` needs existing TVS structure
to prove the topology equals the module topology.

-/

@[expose] public section

namespace DualTopology

open Module

variable {𝕜 E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [T2Space E]
variable [NontriviallyNormedField 𝕜] [Module 𝕜 E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
variable [ContinuousSMul 𝕜 E]

/-- The canonical topology on the algebraic dual of a finite-dimensional space,
induced by the linear equivalence to the continuous dual `E →L[𝕜] 𝕜`. -/
scoped instance instTopologicalSpaceDual : TopologicalSpace (Dual 𝕜 E) :=
  TopologicalSpace.induced
    (LinearMap.toContinuousLinearMap : Dual 𝕜 E → E →L[𝕜] 𝕜) inferInstance

/-- The map from the algebraic dual to the continuous dual is inducing with respect to the
topology on `Dual 𝕜 E` defined by `instTopologicalSpaceDual`. -/
private lemma isInducing_toContinuousLinearMap :
    @Topology.IsInducing (Dual 𝕜 E) (E →L[𝕜] 𝕜) instTopologicalSpaceDual _
      LinearMap.toContinuousLinearMap :=
  ⟨rfl⟩

/-- The map from the algebraic dual to the continuous dual is a topological embedding. -/
private lemma isEmbedding_toContinuousLinearMap :
    @Topology.IsEmbedding (Dual 𝕜 E) (E →L[𝕜] 𝕜) instTopologicalSpaceDual _
      LinearMap.toContinuousLinearMap :=
  ⟨isInducing_toContinuousLinearMap, LinearEquiv.injective _⟩

/-- The algebraic dual is a topological add group under the induced topology. -/
scoped instance instIsTopologicalAddGroupDual : IsTopologicalAddGroup (Dual 𝕜 E) :=
  Topology.IsInducing.topologicalAddGroup
    (LinearMap.toContinuousLinearMap.toAddMonoidHom : Dual 𝕜 E →+ (E →L[𝕜] 𝕜))
    isInducing_toContinuousLinearMap

/-- The algebraic dual has continuous scalar multiplication under the induced topology. -/
scoped instance instContinuousSMulDual : ContinuousSMul 𝕜 (Dual 𝕜 E) :=
  isInducing_toContinuousLinearMap.continuousSMul continuous_id
    (fun {c x} => LinearEquiv.map_smul LinearMap.toContinuousLinearMap c x)

/-- The algebraic dual is Hausdorff under the induced topology. -/
scoped instance instT2SpaceDual : T2Space (Dual 𝕜 E) :=
  isEmbedding_toContinuousLinearMap.t2Space

end DualTopology

/-!
## LocallyConvexSpace for real scalars

For real scalars, we can derive `LocallyConvexSpace` automatically.
Usage: Use `open DualTopology.LocallyConvex` to enable this instance.
-/

namespace DualTopology.LocallyConvex

open DualTopology

variable {E : Type*} [AddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

/-- The algebraic dual over ℝ is locally convex under the induced topology.

This follows because `E →L[ℝ] ℝ` is a normed space, hence locally convex. -/
scoped instance instLocallyConvexSpaceDualReal : LocallyConvexSpace ℝ (Module.Dual ℝ E) :=
  LocallyConvexSpace.induced LinearMap.toContinuousLinearMap.toLinearMap

end DualTopology.LocallyConvex

/-!
## The (continuous perfect) dual pairing with automatic topology

Usage: Use `open DualTopology.ContPerfPair` to enable the `IsContPerfPair` instance.
This requires `open DualTopology` as well for the underlying topology.
-/

namespace DualTopology.ContPerfPair

open Module DualTopology

variable {E : Type*} [AddCommGroup E]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
variable [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The dual pairing is a continuous perfect pairing for finite-dimensional Hausdorff spaces
over complete nontrivially normed fields.

This version uses `DualTopology` scoped instances, so no explicit topological assumptions
on `Dual 𝕜 E` are required. -/
scoped instance instIsContPerfPair : (dualPairing 𝕜 E).IsContPerfPair where
  continuous_uncurry := by
    haveI : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional
    haveI : IsModuleTopology 𝕜 (Dual 𝕜 E) := isModuleTopologyOfFiniteDimensional
    exact IsModuleTopology.continuous_bilinear_of_finite_left (dualPairing 𝕜 E)
  bijective_left := LinearMap.toContinuousLinearMap.bijective
  bijective_right := LinearMap.toContinuousLinearMap.bijective.comp (evalEquiv 𝕜 E).bijective

end DualTopology.ContPerfPair

/-!
## Continuous perfect pairing with explicit topology assumptions

Usage: Use `open ContPerfPairExplicit` when you have explicit topological assumptions on both
`E` and `Dual 𝕜 E`. This is independent of the `DualTopology` scoped instances.
-/

namespace ContPerfPairExplicit

open Module

-- [CompleteSpace 𝕜] is required for `isModuleTopologyOfFiniteDimensional`
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [FiniteDimensional 𝕜 E] [T2Space E]
variable [TopologicalSpace (Dual 𝕜 E)] [IsTopologicalAddGroup (Dual 𝕜 E)]
variable [ContinuousSMul 𝕜 (Dual 𝕜 E)] [T2Space (Dual 𝕜 E)]

/-- The dual pairing is a continuous perfect pairing for finite-dimensional Hausdorff spaces
over complete nontrivially normed fields.

This version requires explicit topological assumptions on `Dual 𝕜 E` and is independent
of the `DualTopology` scoped instances. -/
scoped instance instIsContPerfPairDualPairing : (dualPairing 𝕜 E).IsContPerfPair where
  continuous_uncurry := by
    haveI : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional
    haveI : IsModuleTopology 𝕜 (Dual 𝕜 E) := isModuleTopologyOfFiniteDimensional
    exact IsModuleTopology.continuous_bilinear_of_finite_left (dualPairing 𝕜 E)
  bijective_left := LinearMap.toContinuousLinearMap.bijective
  bijective_right := LinearMap.toContinuousLinearMap.bijective.comp (evalEquiv 𝕜 E).bijective

end ContPerfPairExplicit

/-
/-
## Various instance tests for review

Verify that instance synthesis works correctly with the scoped instances.
-/

variable (n : ℕ)
variable {E : Type*} [AddCommGroup E]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
variable [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

noncomputable section InstanceTests_ToBeDeleted

-- access the first of the above "instance namespaces"
open DualTopology

-- Basic instance synthesis over 𝕜 (from DualTopology)
example : TopologicalSpace (Module.Dual 𝕜 (Fin n → E)) := inferInstance
example : IsTopologicalAddGroup (Module.Dual 𝕜 (Fin n → E)) := inferInstance
example : ContinuousSMul 𝕜 (Module.Dual 𝕜 (Fin n → E)) := inferInstance
example : T2Space (Module.Dual 𝕜 (Fin n → E)) := inferInstance

-- Basic instance synthesis over ℝ (from DualTopology)
example : TopologicalSpace (Module.Dual ℝ (Fin n → ℝ)) := inferInstance
example : IsTopologicalAddGroup (Module.Dual ℝ (Fin n → ℝ)) := inferInstance
example : ContinuousSMul ℝ (Module.Dual ℝ (Fin n → ℝ)) := inferInstance
example : T2Space (Module.Dual ℝ (Fin n → ℝ)) := inferInstance

/-
-- Over ℂ (no LocallyConvexSpace since ℂ doesn't have PartialOrder)

public import Mathlib.Analysis.Complex.Basic

example : TopologicalSpace (Module.Dual ℂ (Fin n → ℂ)) := inferInstance
example : IsTopologicalAddGroup (Module.Dual ℂ (Fin n → ℂ)) := inferInstance
example : ContinuousSMul ℂ (Module.Dual ℂ (Fin n → ℂ)) := inferInstance
example : T2Space (Module.Dual ℂ (Fin n → ℂ)) := inferInstance
-/

-- access the second of the above "instance namespaces"
open DualTopology.LocallyConvex

-- LocallyConvexSpace (from DualTopology.LocallyConvex)
example : LocallyConvexSpace ℝ (Module.Dual ℝ (Fin n → ℝ)) := inferInstance
-- not possible
--example : LocallyConvexSpace 𝕜 (Module.Dual 𝕜 (Fin n → E)) := inferInstance

-- access the third of the above "instance namespaces"
open DualTopology.ContPerfPair

-- IsContPerfPair (from DualTopology.PerfectPairing)
example : (Module.dualPairing ℝ (Fin n → ℝ)).IsContPerfPair := inferInstance
example : (Module.dualPairing 𝕜 (Fin n → E)).IsContPerfPair := inferInstance

end InstanceTests_ToBeDeleted

section InstanceTests2_ToBeDeleted

-- access the last of the above "instance namespaces"
open ContPerfPairExplicit

variable [TopologicalSpace (Module.Dual 𝕜 E)] [IsTopologicalAddGroup (Module.Dual 𝕜 E)]
variable [ContinuousSMul 𝕜 (Module.Dual 𝕜 E)] [T2Space (Module.Dual 𝕜 E)]

--continuous perfect pairing
example : (Module.dualPairing 𝕜 E).IsContPerfPair := inferInstance

end InstanceTests2_ToBeDeleted

-/
