# Gauss–Bonnet–Chern in Lean

A Lean 4 formalization of the Gauss–Bonnet–Chern theorem in every positive even dimension. For every integer `n ≥ 1` and every compact, oriented, smooth Riemannian manifold `M` of dimension `2n` without boundary,

```math
\int_M \mathrm{Pf}\!\left(\frac{\Omega^{\mathrm{LC}}}{2\pi}\right)=\chi(M).
```

Here `Ωᴸᶜ` is the Levi–Civita curvature matrix, and `χ(M)` is defined independently using real singular homology. Empty and disconnected manifolds are included. The statement covers every compatible finite oriented atlas, smooth metric, and subordinate smooth partition of unity.

The public theorem in [MainTheorem.lean](GaussBonnetChern/MainTheorem.lean) is

```lean
GaussBonnetChern.gaussBonnetChern :
  GaussBonnetChern.GaussBonnetChernStatement.{u}
```

It proves the full proposition in [Statement.lean](GaussBonnetChern/Statement.lean), uniformly in the universe `u`, without additional geometric hypotheses. The proof follows Chern’s unit tangent sphere bundle transgression argument; Morse theory identifies the resulting zero-index sum with the topological Euler characteristic.

All project modules have been built in the pinned environment. The main theorem passed a source check with `--trust=0`; its audited axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`. Independent mathematical review remains pending.

## Building

The toolchain is **Lean 4.34.1**, including its matching Lake. Mathlib is pinned to **`d13f23b723b8a846827a245b89c10fc7d3f11612`**. The nine dependency packages—mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, and Cli—are included under `vendor/`, together with their configurations, upstream licenses, and required assets. Relative-path manifests resolve these local sources; no additional dependency repositories need to be cloned.

Exact dependency revisions are listed in [vendor/VERSIONS.json](vendor/VERSIONS.json).
With Lean 4.34.1 already installed, run from the repository root:

```sh
LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true MATHLIB_NO_CACHE_ON_UPDATE=1 lake --no-cache build
```

On PowerShell:

```powershell
$env:LAKE_ARTIFACT_CACHE = 'false'
$env:LAKE_NO_CACHE = 'true'
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
lake --no-cache build
```

Keep the bundled assets and licenses, and use the root toolchain when building.
No dependency update or cache download is needed. Compiler limits are
`-j1 -M4096` per Lean worker; sufficient memory is needed for parallel Lake builds.

[GaussBonnetChern.lean](GaussBonnetChern.lean) is the library entry point. The main declaration can be inspected with:

```lean
import GaussBonnetChern.MainTheorem

#check GaussBonnetChern.gaussBonnetChern
#print axioms GaussBonnetChern.gaussBonnetChern
```

## Proof structure

All paths below are in `GaussBonnetChern/`.

| Part | Content | Principal modules |
| --- | --- | --- |
| A | Manifold data, orientation, and the exact statement | [Geometry](GaussBonnetChern/Geometry.lean), [Statement](GaussBonnetChern/Statement.lean) |
| B | Levi–Civita curvature, Pfaffians, and the Euler form | [CovariantCurvature](GaussBonnetChern/CovariantCurvature.lean), [Pfaffian](GaussBonnetChern/Pfaffian.lean), [EulerForm](GaussBonnetChern/EulerForm.lean) |
| C | Differential forms and exterior calculus | [DifferentialForms](GaussBonnetChern/DifferentialForms.lean), [ExteriorDerivative](GaussBonnetChern/ExteriorDerivative.lean), [ExteriorLeibniz](GaussBonnetChern/ExteriorLeibniz.lean) |
| D | Integration and Stokes on punctured domains | [FormIntegration](GaussBonnetChern/FormIntegration.lean), [CoordinateStokes](GaussBonnetChern/CoordinateStokes.lean), [PuncturedStokes](GaussBonnetChern/PuncturedStokes.lean) |
| E | Singular homology and the Morse index sum | [Topology](GaussBonnetChern/Topology.lean), [MorseExistence](GaussBonnetChern/MorseExistence.lean), [HandleHomology](GaussBonnetChern/HandleHomology.lean), [MorseTopologicalIndex](GaussBonnetChern/MorseTopologicalIndex.lean) |
| F | Sphere bundle geometry and Chern transgression | [UnitTangentSphere](GaussBonnetChern/UnitTangentSphere.lean), [ChernAngularForm](GaussBonnetChern/ChernAngularForm.lean), [ChernGeometricTransgression](GaussBonnetChern/ChernGeometricTransgression.lean) |
| G | Local index limits and the global integral identity | [ChernLocalIndexLimit](GaussBonnetChern/ChernLocalIndexLimit.lean), [NormalizedFieldTransgression](GaussBonnetChern/NormalizedFieldTransgression.lean), [IntegrationAssembly](GaussBonnetChern/IntegrationAssembly.lean) |

[MainTheorem.lean](GaussBonnetChern/MainTheorem.lean) assembles these results into the all-dimensional theorem.

## References

- S.-S. Chern, *A Simple Intrinsic Proof of the Gauss-Bonnet Formula for Closed Riemannian Manifolds*, **Annals of Mathematics** 45(4) (1944), 747–752. [Original article](https://doi.org/10.2307/1969302).
- J. Milnor, *Morse Theory*, **Annals of Mathematics Studies** 51, Princeton University Press (1963). [Publisher edition](https://doi.org/10.1515/9781400881802).

The source formalization task is [windows-lean-loop Issue #1701](https://github.com/pd4st8hb95-hub/windows-lean-loop/issues/1701). Third-party packages retain their respective upstream licenses.
