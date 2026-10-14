/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Tests that terms used in category theory pretty-print as expected
-/

section

open Opposite

/-- info: Opposite.op_unop.{u} {α : Sort u} (x : αᵒᵖ) : op (unop x) = x -/
#guard_msgs in
#check Opposite.op_unop

end

section

open CategoryTheory

/--
info: CategoryTheory.Functor.map_id.{v₁, v₂, u₁, u₂} {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂} [Category.{v₂, u₂} D]
  (self : C ⥤ D) (X : C) : self.map (𝟙 X) = 𝟙 (self.obj X)
-/
#guard_msgs in
#check CategoryTheory.Functor.map_id

end
