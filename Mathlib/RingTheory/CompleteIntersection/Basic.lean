/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!

# Define Complete Intersection Ring

-/

@[expose] public section

open IsLocalRing  RingTheory.Sequence

universe u

variable (R : Type u) [CommRing R]

def Epsilon1 [IsNoetherianRing R] [IsLocalRing R] : ℕ := sorry

section

variable [IsNoetherianRing R] [IsLocalRing R]

instance : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) := sorry

instance : IsLocalRing (AdicCompletion (maximalIdeal R) R) := sorry

lemma completion_epsilon1_eq : Epsilon1 R = Epsilon1 (AdicCompletion (maximalIdeal R) R) := by
  sorry

lemma epsilon1_add_ringKrullDim_ge :
    Epsilon1 R + ringKrullDim R ≥ (maximalIdeal R).spanFinrank := by
  sorry

end

variable [IsNoetherianRing R] [IsLocalRing R]

class IsCompleteIntersectionLocalRing extends IsLocalRing R, IsNoetherianRing R where
  ci : Epsilon1 R + ringKrullDim R = (maximalIdeal R).spanFinrank

lemma quotient_isCompleteIntersectionLocalRing (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (I : Ideal S) [IsCompleteIntersectionLocalRing (S ⧸ I)] :
    ∃(rs : List S), I = Ideal.ofList rs ∧ IsRegular S rs := by
  sorry

lemma completion_isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    IsCompleteIntersectionLocalRing (AdicCompletion (maximalIdeal R) R) := by
  sorry

theorem isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    ∃ (S : Type u) (_ : CommRing S) (f : S →+* (AdicCompletion (maximalIdeal R) R)) (rs : List S),
      IsRegularLocalRing S ∧ Function.Surjective f ∧
      RingHom.ker f = Ideal.ofList rs ∧ IsRegular S rs := by
  sorry
