module
import Mathlib.Algebra.Category.MonCat.Basic

universe v u

open CategoryTheory MonCat

set_option maxHeartbeats 10000
set_option synthInstance.maxHeartbeats 2000

/- We test if all the coercions and `map_mul` lemmas trigger correctly. -/

example (X : Type u) [Monoid X] : ⇑(𝟙 (of X)) = id := by simp

example {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) :
    ⇑(ofHom f) = ⇑f := by simp

example {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y)
    (x : X) : (ofHom f) x = f x := by simp

example {X Y Z : MonCat} (f : X ⟶ Y) (g : Y ⟶ Z) : ⇑(f ≫ g) = ⇑g ∘ ⇑f := by simp

example {X Y Z : Type u} [Monoid X] [Monoid Y] [Monoid Z]
    (f : X →* Y) (g : Y →* Z) :
    ⇑(ofHom f ≫ ofHom g) = g ∘ f := by simp

example {X Y : Type u} [Monoid X] [Monoid Y] {Z : MonCat}
    (f : X →* Y) (g : of Y ⟶ Z) :
    ⇑(ofHom f ≫ g) = g ∘ f := by simp

example {X Y : MonCat} {Z : Type u} [Monoid Z] (f : X ⟶ Y) (g : Y ⟶ of Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {Y Z : MonCat} {X : Type u} [Monoid X] (f : of X ⟶ Y) (g : Y ⟶ Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {X Y Z : MonCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp

example {X Y : MonCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by simp

example {X Y : MonCat} (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by simp

example (X : MonCat) : ⇑(𝟙 X) = id := by simp

example {X : Type*} [Monoid X] : ⇑(MonoidHom.id X) = id := by simp

example {M N : MonCat} (f : M ⟶ N) (x y : M) : f (x * y) = f x * f y := by
  simp

example {M N : MonCat} (f : M ⟶ N) : f 1 = 1 := by
  simp
