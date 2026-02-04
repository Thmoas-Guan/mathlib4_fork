/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.RingTheory.KoszulComplex.Defs

/-!
# Basic Properties of Koszul complex
-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

section change_generators

variable [IsNoetherianRing R] [IsLocalRing R]

theorem koszulCocomplex.nonempty_iso_of_minimal_generators {I : Ideal R} {l l' : List R}
    (hl : Ideal.ofList l = I) (hl' : Ideal.ofList l' = I)
    (hl_min : l.length = I.spanFinrank) (hl'_min : l'.length = I.spanFinrank) :
    Nonempty <| ofList R l ≅ ofList R l' := by
  refine ⟨isoOfEquiv R ?_ ?_⟩
  · sorry
  · sorry

theorem koszulCocomplex.nonempty_iso_of_minimal_generators' {I : Ideal R} {l : List R}
    (eq : Ideal.ofList l = I) (min : l.length = I.spanFinrank) :
    Nonempty <| ofList R I.finite_generators_of_isNoetherian.toFinset.toList ≅ ofList R l := by
  refine nonempty_iso_of_minimal_generators R ?_ eq ?_ min
  · simp only [Ideal.ofList, Finset.mem_toList, Set.Finite.mem_toFinset, Set.setOf_mem_eq]
    exact I.span_generators
  · simp only [Finset.length_toList, ← Set.ncard_eq_toFinset_card _ _]
    exact Submodule.FG.generators_ncard Submodule.FG.of_finite

end change_generators

section basechange

variable (S : Type (max u v)) [CommRing S] (f : R →+* S)

instance (T : Type v) [CommRing T] (g : R →+* T) :
    (ModuleCat.extendScalars.{u, v, u} g).Additive where
  map_add {X Y a b} := by
    simp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map', Algebra.algebraMap_self,
      ModuleCat.hom_add, LinearMap.baseChange_add]
    rfl

open TensorProduct in
def koszulCocomplex.baseChange_iso (l : List R) (l' : List S) (eqmap : l.map f = l') :
    koszulCocomplex.ofList S l' ≅ ((ModuleCat.extendScalars f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulCocomplex.ofList R l) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ LinearEquiv.toModuleIso ?_) (fun i j ↦ ?_)
  · sorry
  · sorry

end basechange

section IsRegular

open RingTheory.Sequence

lemma koszulCocomplex.exactAt_of_lt_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i < rs.length) : (koszulCocomplex.ofList R rs).ExactAt i := by
  sorry

theorem koszulCocomplex.exactAt_of_ne_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i ≠ rs.length) : (koszulCocomplex.ofList R rs).ExactAt i := by
  sorry

end IsRegular
