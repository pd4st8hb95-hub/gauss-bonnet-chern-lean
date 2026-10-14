module
import Mathlib.Algebra.Category.Ring.Basic

universe v u

open CategoryTheory SemiRingCat

set_option maxHeartbeats 10000
set_option synthInstance.maxHeartbeats 2000

/- We test if all the coercions and `map_add` lemmas trigger correctly. -/

example (X : Type u) [Semiring X] : ⇑(𝟙 (of X)) = id := by simp

example {X Y : Type u} [Semiring X] [Semiring Y] (f : X →+* Y) :
    ⇑(ofHom f) = ⇑f := by simp

example {X Y : Type u} [Semiring X] [Semiring Y] (f : X →+* Y)
    (x : X) : (ofHom f) x = f x := by simp

example {X Y Z : SemiRingCat} (f : X ⟶ Y) (g : Y ⟶ Z) : ⇑(f ≫ g) = ⇑g ∘ ⇑f := by simp

example {X Y Z : Type u} [Semiring X] [Semiring Y] [Semiring Z]
    (f : X →+* Y) (g : Y →+* Z) :
    ⇑(ofHom f ≫ ofHom g) = g ∘ f := by simp

example {X Y : Type u} [Semiring X] [Semiring Y] {Z : SemiRingCat}
    (f : X →+* Y) (g : of Y ⟶ Z) :
    ⇑(ofHom f ≫ g) = g ∘ f := by simp

example {X Y : SemiRingCat} {Z : Type u} [Semiring Z] (f : X ⟶ Y) (g : Y ⟶ of Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {Y Z : SemiRingCat} {X : Type u} [Semiring X] (f : of X ⟶ Y) (g : Y ⟶ Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {X Y Z : SemiRingCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp

example {X Y : SemiRingCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by simp

example {X Y : SemiRingCat} (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by simp

example (X : SemiRingCat) : ⇑(𝟙 X) = id := by simp

example {X : Type*} [Semiring X] : ⇑(RingHom.id X) = id := by simp

example {M N : SemiRingCat} (f : M ⟶ N) (x y : M) : f (x + y) = f x + f y := by
  simp

example {M N : SemiRingCat} (f : M ⟶ N) (x y : M) : f (x * y) = f x * f y := by
  simp

example {M N : SemiRingCat} (f : M ⟶ N) : f 0 = 0 := by
  simp
