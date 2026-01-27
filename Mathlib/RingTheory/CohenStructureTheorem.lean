/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Basic

/-!

# Define Complete Intersection Ring

-/

@[expose] public section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R]

variable [IsNoetherianRing R] [IsLocalRing R]

lemma exist_isRegularLocalRing_surjective_of_isAdicComplete [IsAdicComplete (maximalIdeal R) R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (f : S →+* R),
    Function.Surjective f := by
  sorry

lemma exist_isRegularLocalRing_surjective_ker_le_of_isAdicComplete
    [IsAdicComplete (maximalIdeal R) R] : ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* R), Function.Surjective f ∧ RingHom.ker f ≤ (maximalIdeal S) ^ 2 := by
  --quotient by elements outside of `m²`
  sorry

lemma exist_isRegularLocalRing_surjective_adicCompletion :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* (AdicCompletion (maximalIdeal R) R)), Function.Surjective f :=
  exist_isRegularLocalRing_surjective_of_isAdicComplete _

lemma exist_isRegularLocalRing_surjective_adicCompletion_ker_le :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* (AdicCompletion (maximalIdeal R) R)),
    Function.Surjective f ∧ RingHom.ker f ≤ (maximalIdeal S) ^ 2 :=
  exist_isRegularLocalRing_surjective_ker_le_of_isAdicComplete _
