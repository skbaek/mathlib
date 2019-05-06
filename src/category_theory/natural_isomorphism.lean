-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.functor_category
import category_theory.whiskering

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory.nat_iso

variables {C : Sort u₁} [𝒞 : category.{v₁} C] {D : Sort u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

def app {F G : C ⥤ D} (α : F ≅ G) (X : C) : F.obj X ≅ G.obj X :=
{ hom := α.hom.app X,
  inv := α.inv.app X,
  hom_inv_id' := begin rw [← functor.category.comp_app, iso.hom_inv_id], refl, end,
  inv_hom_id' := begin rw [← functor.category.comp_app, iso.inv_hom_id], refl, end }

@[simp] lemma comp_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
  app (α ≪≫ β) X = app α X ≪≫ app β X := rfl

@[simp] lemma app_hom {F G : C ⥤ D} (α : F ≅ G) (X : C) : (app α X).hom = α.hom.app X := rfl
@[simp] lemma app_inv {F G : C ⥤ D} (α : F ≅ G) (X : C) : (app α X).inv = α.inv.app X := rfl

@[simp] lemma hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) :=
congr_fun (congr_arg nat_trans.app α.hom_inv_id) X

@[simp] lemma inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X) :=
congr_fun (congr_arg nat_trans.app α.inv_hom_id) X

variables {F G : C ⥤ D}

instance hom_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.hom.app X) :=
{ inv := α.inv.app X,
  hom_inv_id' := begin rw [←functor.category.comp_app, iso.hom_inv_id, ←functor.category.id_app] end,
  inv_hom_id' := begin rw [←functor.category.comp_app, iso.inv_hom_id, ←functor.category.id_app] end }
instance inv_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.inv.app X) :=
{ inv := α.hom.app X,
  hom_inv_id' := begin rw [←functor.category.comp_app, iso.inv_hom_id, ←functor.category.id_app] end,
  inv_hom_id' := begin rw [←functor.category.comp_app, iso.hom_inv_id, ←functor.category.id_app] end }

@[simp] lemma hom_app_inv_app_id (α : F ≅ G) (X : C) : α.hom.app X ≫ α.inv.app X = 𝟙 _ :=
begin
  rw ←functor.category.comp_app,
  simp,
end
@[simp] lemma inv_app_hom_app_id (α : F ≅ G) (X : C) : α.inv.app X ≫ α.hom.app X = 𝟙 _ :=
begin
  rw ←functor.category.comp_app,
  simp,
end

variables {X Y : C}
@[simp] lemma naturality_1 (α : F ≅ G) (f : X ⟶ Y) :
  (α.inv.app X) ≫ (F.map f) ≫ (α.hom.app Y) = G.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end
@[simp] lemma naturality_2 (α : F ≅ G) (f : X ⟶ Y) :
  (α.hom.app X) ≫ (G.map f) ≫ (α.inv.app Y) = F.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end

instance is_iso_of_is_iso_app (α : F ⟶ G) [∀ X : C, is_iso (α.app X)] : is_iso α :=
{ inv :=
  { app := λ X, inv (α.app X),
    naturality' := λ X Y f,
    by simpa using congr_arg (λ f, inv (α.app X) ≫ (f ≫ inv (α.app Y))) (α.naturality f).symm } }

def of_components (app : ∀ X : C, (F.obj X) ≅ (G.obj X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ ((app Y).hom) = ((app X).hom) ≫ (G.map f)) :
  F ≅ G :=
as_iso { app := λ X, (app X).hom }

@[simp] def of_components.app (app' : ∀ X : C, (F.obj X) ≅ (G.obj X)) (naturality) (X) :
  app (of_components app' naturality) X = app' X :=
by tidy
@[simp] def of_components.hom_app (app : ∀ X : C, (F.obj X) ≅ (G.obj X)) (naturality) (X) :
  (of_components app naturality).hom.app X = (app X).hom := rfl
@[simp] def of_components.inv_app (app : ∀ X : C, (F.obj X) ≅ (G.obj X)) (naturality) (X) :
  (of_components app naturality).inv.app X = (app X).inv := rfl

end category_theory.nat_iso

open category_theory

namespace category_theory.functor

section
variables {C : Sort u₁} [𝒞 : category.{v₁} C]
          {D : Sort u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

@[simp] protected def id_comp (F : C ⥤ D) : functor.id C ⋙ F ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }
@[simp] protected def comp_id (F : C ⥤ D) : F ⋙ functor.id D ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

universes v₄ u₄

variables {A : Sort u₃} [𝒜 : category.{v₃} A]
          {B : Sort u₄} [ℬ : category.{v₄} B]
include 𝒜 ℬ
variables (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)

@[simp] protected def assoc : (F ⋙ G) ⋙ H ≅ F ⋙ (G ⋙ H ):=
{ hom := { app := λ X, 𝟙 (H.obj (G.obj (F.obj X))) },
  inv := { app := λ X, 𝟙 (H.obj (G.obj (F.obj X))) } }

-- When it's time to define monoidal categories and 2-categories,
-- we'll need to add lemmas relating these natural isomorphisms,
-- in particular the pentagon for the associator.
end

section
variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

def ulift_down_up : ulift_down.{v₁} C ⋙ ulift_up C ≅ functor.id (ulift.{u₂} C) :=
{ hom := { app := λ X, @category_struct.id (ulift.{u₂} C) _ X },
  inv := { app := λ X, @category_struct.id (ulift.{u₂} C) _ X } }

def ulift_up_down : ulift_up.{v₁} C ⋙ ulift_down C ≅ functor.id C :=
{ hom := { app := λ X, 𝟙 X },
  inv := { app := λ X, 𝟙 X } }

end

end category_theory.functor
