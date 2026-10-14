import GaussBonnetChern.AcceptanceRegression

/-! # Exact acceptance-regression statement inventory and axiom audit

This audit input covers all 13 declarations of the frozen source module.
Target source SHA256:
025B2EAF016D4EE3E7354E10F4E7981A4BF467C9404986B96BDD8B2086D65CD0

Preparation status: SOURCE_ONLY. This file has not been run by its writer.
Each `#check` emits the actual elaborated type, followed by the corresponding
`#print axioms` for its full transitive proof dependencies. The root agent
must run this file using the verified module object and record actual output.
The inventory below retains the conditional metric-model hypotheses and
keeps real sphere homology distinct from tangent-fiber normalization.
No declaration here is a standard closed even-sphere metric GBC regression.
-/

-- 01 actualMetricEndpointSign: actual critical gradient; index 0 or 2*n.
#check GaussBonnetChern.AcceptanceRegression.actual_gradient_endpoint_sign
#print axioms GaussBonnetChern.AcceptanceRegression.actual_gradient_endpoint_sign

-- 02 conditionalActualHessianModels: actual Hessian diagonal +1 premise.
#check GaussBonnetChern.AcceptanceRegression.actual_positive_hessian_endpoint
#print axioms GaussBonnetChern.AcceptanceRegression.actual_positive_hessian_endpoint

-- 03 conditionalActualHessianModels: actual Hessian diagonal -1 premise.
#check GaussBonnetChern.AcceptanceRegression.actual_negative_hessian_endpoint
#print axioms GaussBonnetChern.AcceptanceRegression.actual_negative_hessian_endpoint

-- 04 actualSameValueMultiplicity: full actual critical fiber cardinality jump.
#check GaussBonnetChern.AcceptanceRegression.actual_sameValue_euler_jump
#print axioms GaussBonnetChern.AcceptanceRegression.actual_sameValue_euler_jump

-- 05 actualSameValueMultiplicity: two same-value index-zero critical points.
#check GaussBonnetChern.AcceptanceRegression.actual_two_sameValue_minima_jump
#print axioms GaussBonnetChern.AcceptanceRegression.actual_two_sameValue_minima_jump

-- 06 actualFiniteMorseInduction: all actual critical values and all fiber points.
#check GaussBonnetChern.AcceptanceRegression.actual_morse_euler_grouped_by_value
#print axioms GaussBonnetChern.AcceptanceRegression.actual_morse_euler_grouped_by_value

-- 07 actualOrientationCompatibility: top form negation and scalar/integral equality.
#check GaussBonnetChern.AcceptanceRegression.opposite_orientation_euler_compatibility
#print axioms GaussBonnetChern.AcceptanceRegression.opposite_orientation_euler_compatibility

-- 08 actualOrientationCompatibility: fixed smooth top form integral negation.
#check GaussBonnetChern.AcceptanceRegression.opposite_orientation_fixed_form
#print axioms GaussBonnetChern.AcceptanceRegression.opposite_orientation_fixed_form

-- 09 realEulerHomology: actual singular-homology Euler value of all even spheres.
#check GaussBonnetChern.AcceptanceRegression.even_unitSphere_euler
#print axioms GaussBonnetChern.AcceptanceRegression.even_unitSphere_euler

-- 10 realEulerHomology: literal sphere in EuclideanSpace real (Fin 3).
#check GaussBonnetChern.AcceptanceRegression.standard_twoSphere_euler
#print axioms GaussBonnetChern.AcceptanceRegression.standard_twoSphere_euler

-- 11 realEulerHomology: literal sphere in EuclideanSpace real (Fin 5).
#check GaussBonnetChern.AcceptanceRegression.standard_fourSphere_euler
#print axioms GaussBonnetChern.AcceptanceRegression.standard_fourSphere_euler

-- 12 conditionalActualSurfaceNormalization: actual curvature component = 1 premise.
#check GaussBonnetChern.AcceptanceRegression.actual_unit_curvature_surface_density
#print axioms GaussBonnetChern.AcceptanceRegression.actual_unit_curvature_surface_density

-- 13 unitFiberNormalization: actual angular form integral on S^(2*n-1) fiber = 1.
#check GaussBonnetChern.AcceptanceRegression.actual_angular_fiber_normalization
#print axioms GaussBonnetChern.AcceptanceRegression.actual_angular_fiber_normalization
