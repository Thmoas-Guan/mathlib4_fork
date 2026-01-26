/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.CohenMacaulay.Catenary
public import Mathlib.RingTheory.CohenMacaulay.Maximal
public import Mathlib.RingTheory.KoszulComplex.Defs

/-!

# Define Complete Intersection Ring

-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

universe u

variable (R : Type u) [CommRing R]

section preliminaries

lemma spanFinrank_le_of_surjective {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (f : R →+* R') (surj : Function.Surjective f) :
    (maximalIdeal R').spanFinrank ≤ (maximalIdeal R).spanFinrank := by
  let fin := Submodule.FG.finite_generators (maximalIdeal R).fg_of_isNoetherianRing
  have hspan : Ideal.span (maximalIdeal R).generators = (maximalIdeal R) :=
    (maximalIdeal R).span_generators
  have hspan_t : Ideal.span (f '' (maximalIdeal R).generators) = maximalIdeal R' := by
    simpa [← Ideal.map_span, hspan, ((local_hom_TFAE f).out 0 4).mp (surj.isLocalHom f)] using
      (Ideal.map_comap_of_surjective f surj (maximalIdeal R'))
  have hle : (maximalIdeal R').spanFinrank ≤ (f '' (maximalIdeal R).generators).ncard := by
    simpa [← hspan_t] using (Submodule.spanFinrank_span_le_ncard_of_finite (fin.image _))
  apply le_trans hle (le_of_le_of_eq (Set.ncard_image_le fin)
    (Submodule.FG.generators_ncard (maximalIdeal R).fg_of_isNoetherianRing))

lemma spanFinrank_eq_of_ringEquiv {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (e : R ≃+* R') : (maximalIdeal R).spanFinrank = (maximalIdeal R').spanFinrank :=
  le_antisymm (spanFinrank_le_of_surjective e.symm.toRingHom e.symm.surjective)
    (spanFinrank_le_of_surjective e.toRingHom e.surjective)

lemma spanFinrank_eq_of_surjective_of_ker_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (f : R →+* R') (surj : Function.Surjective f) (le : RingHom.ker f ≤ (maximalIdeal R) ^ 2) :
    (maximalIdeal R').spanFinrank = (maximalIdeal R).spanFinrank := by
  apply le_antisymm (spanFinrank_le_of_surjective f surj)

  classical
  let g : R' → R := fun x => Classical.choose (surj x)
  have hg : ∀ x, f (g x) = x := fun x => Classical.choose_spec (surj x)
  have hcomap : Ideal.comap f (maximalIdeal R') = maximalIdeal R := by
    exact ((local_hom_TFAE f).out 0 4).mp (surj.isLocalHom f)
  let S : Set R' := (maximalIdeal R').generators
  let T : Set R := g '' S
  have fin : S.Finite := by
    simpa [S] using
      (Submodule.FG.finite_generators (maximalIdeal R').fg_of_isNoetherianRing)
  have hTsubset : T ⊆ maximalIdeal R := by
    intro x hx
    rcases hx with ⟨y, hyS, rfl⟩
    have hy : (y : R') ∈ maximalIdeal R' := by
      simpa [S] using (Submodule.FG.generators_mem (maximalIdeal R') hyS)
    have : g y ∈ Ideal.comap f (maximalIdeal R') := by
      show f (g y) ∈ maximalIdeal R'
      simpa [hg y] using hy
    simpa [hcomap] using this
  have hspanT_le : Ideal.span T ≤ maximalIdeal R := by
    exact Ideal.span_le.mpr hTsubset
  have himage : f '' T = S := by
    ext y; constructor
    · rintro ⟨x, hxT, rfl⟩
      rcases hxT with ⟨z, hz, rfl⟩
      simpa [hg z, S] using hz
    · intro hy
      refine ⟨g y, ?_, hg y⟩
      exact ⟨y, hy, rfl⟩
  have hmap_span : Ideal.map f (Ideal.span T) = maximalIdeal R' := by
    simpa [Ideal.map_span, himage, S, (maximalIdeal R').span_generators]
  have hle : maximalIdeal R ≤ Ideal.span T ⊔ (maximalIdeal R)^2 := by
    intro x hx
    have hx' : f x ∈ maximalIdeal R' := by
      have : x ∈ Ideal.comap f (maximalIdeal R') := by
        simpa [hcomap] using hx
      simpa using this
    have hxmap : f x ∈ Ideal.map f (Ideal.span T) := by
      simpa [hmap_span] using hx'
    rcases (Ideal.mem_map_iff_of_surjective (f := f) surj).1 hxmap with ⟨y, hyT, hfy⟩
    have hker : x - y ∈ RingHom.ker f := by
      show f (x - y) = 0
      calc
        f (x - y) = f x - f y := by simp
        _ = 0 := by simpa [hfy]
    have hker' : x - y ∈ (maximalIdeal R)^2 := le hker
    refine Submodule.mem_sup.2 ?_
    refine ⟨y, hyT, x - y, hker', by
      simpa [add_comm] using (sub_add_cancel x y)⟩
  have hle' : (maximalIdeal R : Ideal R) ≤ Ideal.span T := by
    have hle'': maximalIdeal R ≤ Ideal.span T ⊔ (maximalIdeal R) • maximalIdeal R := by
      simpa [Ideal.smul_eq_mul, pow_two] using hle
    have hfg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
    have hjac : (maximalIdeal R) ≤ Ideal.jacobson (⊥ : Ideal R) := by
      simpa using (IsLocalRing.maximalIdeal_le_jacobson (R := R) (I := ⊥))
    exact Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (N := Ideal.span T)
      (N' := maximalIdeal R) hfg hjac hle''
  have hspanT : Ideal.span T = maximalIdeal R := le_antisymm hle' hspanT_le
  have hleT : (maximalIdeal R).spanFinrank ≤ T.ncard := by
    simpa [T, hspanT] using
      (Submodule.spanFinrank_span_le_ncard_of_finite (fin.image _))
  have hleS : T.ncard ≤ S.ncard := by
    simpa [T] using (Set.ncard_image_le fin)
  have hS : S.ncard = (maximalIdeal R').spanFinrank := by
    simpa [S] using (Submodule.FG.generators_ncard (maximalIdeal R').fg_of_isNoetherianRing)
  exact le_trans hleT (le_trans hleS (le_of_eq hS))

variable [IsNoetherianRing R] [IsLocalRing R]

instance : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) := sorry

instance : IsLocalRing (AdicCompletion (maximalIdeal R) R) := sorry

instance : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
    (AdicCompletion (maximalIdeal R) R) := sorry

lemma ringKrullDim_adicCompletion_eq :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  --!!!
  sorry

lemma spanFinrank_maximalIdeal_adicCompletion_eq :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  --!!!
  sorry

end preliminaries
