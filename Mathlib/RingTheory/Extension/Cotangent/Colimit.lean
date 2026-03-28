/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Cotangent complex under colimit

-/

open CategoryTheory Limits

universe u v

variable {J : Type u} [SmallCategory J] {FR : J ⥤ CommRingCat.{u}} {FS : J ⥤ CommRingCat.{u}}

variable (fRS : FR ⟶ FS)

--variable (CR : Cocone FR) (CS : Cocone FS) (iscR : IsColimit CR) (iscS : IsColimit CS)

noncomputable def CotangentFunctor.obj' (j : J) : AddCommGrpCat.{u} :=
  letI := (fRS.app j).hom.toAlgebra
  AddCommGrpCat.of (Algebra.Generators.self (FR.obj j) (FS.obj j)).toExtension.Cotangent

set_option backward.isDefEq.respectTransparency false in
noncomputable def CotangentFunctor.map' {j₁ j₂ : J} (fj : j₁ ⟶ j₂) :
    CotangentFunctor.obj' fRS j₁ ⟶ CotangentFunctor.obj' fRS j₂ := by
  algebraize [(fRS.app j₁).hom, (fRS.app j₂).hom, (FR.map fj).hom, (FS.map fj).hom,
    (fRS.app j₂).hom.comp (FR.map fj).hom]
  exact AddCommGrpCat.ofHom (Algebra.Extension.Cotangent.map {
    toRingHom :=
      (MvPolynomial.rename (FS.map fj).hom).toRingHom.comp (MvPolynomial.map (FR.map fj).hom)
    toRingHom_algebraMap x := by simp [RingHom.algebraMap_toAlgebra]
    algebraMap_toRingHom x := by
      simp only [Algebra.Generators.self, AlgHom.toRingHom_eq_coe,
        Algebra.Generators.toExtension_Ring, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        Algebra.Generators.algebraMap_apply]
      simp only [RingHom.algebraMap_toAlgebra, MvPolynomial.aeval_rename]
      sorry
    }).toAddMonoidHom

noncomputable def CotangentFunctor : J ⥤ AddCommGrpCat.{u} where
  obj := CotangentFunctor.obj' fRS
  map := CotangentFunctor.map' fRS
  map_id := sorry
  map_comp := sorry
