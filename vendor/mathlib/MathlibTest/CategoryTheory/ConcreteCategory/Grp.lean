module
import Mathlib.Algebra.Category.Grp.Basic

universe v u

open CategoryTheory GrpCat

set_option maxHeartbeats 10000
set_option synthInstance.maxHeartbeats 2000

/- We test if all the coercions and `map_add` lemmas trigger correctly. -/

example (X : Type u) [Group X] : ⇑(𝟙 (of X)) = id := by simp

example {X Y : Type u} [Group X] [Group Y] (f : X →* Y) :
    ⇑(ofHom f) = ⇑f := by simp

example {X Y : Type u} [Group X] [Group Y] (f : X →* Y)
    (x : X) : (ofHom f) x = f x := by simp

example {X Y Z : GrpCat} (f : X ⟶ Y) (g : Y ⟶ Z) : ⇑(f ≫ g) = ⇑g ∘ ⇑f := by simp

example {X Y Z : Type u} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) :
    ⇑(ofHom f ≫ ofHom g) = g ∘ f := by simp

example {X Y : Type u} [Group X] [Group Y] {Z : GrpCat}
    (f : X →* Y) (g : of Y ⟶ Z) :
    ⇑(ofHom f ≫ g) = g ∘ f := by simp

example {X Y : GrpCat} {Z : Type u} [Group Z] (f : X ⟶ Y) (g : Y ⟶ of Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {Y Z : GrpCat} {X : Type u} [Group X] (f : of X ⟶ Y) (g : Y ⟶ Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {X Y Z : GrpCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp

example {X Y : GrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by simp

example {X Y : GrpCat} (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by simp

example (X : GrpCat) : ⇑(𝟙 X) = id := by simp

example {X : Type*} [Group X] : ⇑(MonoidHom.id X) = id := by simp

example {M N : GrpCat} (f : M ⟶ N) (x y : M) : f (x * y) = f x * f y := by
  simp

example {M N : GrpCat} (f : M ⟶ N) : f 1 = 1 := by
  simp
