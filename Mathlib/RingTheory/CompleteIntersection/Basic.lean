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

open IsLocalRing RingTheory.Sequence

universe u

variable (R : Type u) [CommRing R]

section preliminaries

variable [IsNoetherianRing R] [IsLocalRing R]

instance : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) := sorry

instance : IsLocalRing (AdicCompletion (maximalIdeal R) R) := sorry

end preliminaries

section Cohen

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
    (f : S →+* (AdicCompletion (maximalIdeal R) R)), Function.Surjective f := by
  -- use `exist_isRegularLocalRing_surjective_of_isAdicComplete`
  sorry

lemma exist_isRegularLocalRing_surjective_adicCompletion_ker_le :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* (AdicCompletion (maximalIdeal R) R)),
    Function.Surjective f ∧ RingHom.ker f ≤ (maximalIdeal S) ^ 2 := by
  -- use `exist_isRegularLocalRing_surjective_ker_le_of_isAdicComplete`
  sorry

end Cohen

def Epsilon1 [IsNoetherianRing R] [IsLocalRing R] : ℕ := sorry

lemma epsilon1_eq_of_equiv {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R'] (e : R ≃+* R') :
    Epsilon1 R = Epsilon1 R' := by
  sorry

section

variable [IsNoetherianRing R] [IsLocalRing R]

lemma epsilon1_eq_spanFinrank (S : Type u) [CommRing S] [IsRegularLocalRing S] (I : Ideal S)
    (le : I ≤ (maximalIdeal S) ^ 2) :
    letI : IsLocalRing (S ⧸ I) :=
      have : Nontrivial (S ⧸ I) :=
        Submodule.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top Ideal.IsPrime.ne_top'
          (le.trans (Ideal.pow_le_self (Nat.zero_ne_add_one 1).symm)))
      have : IsLocalHom (Ideal.Quotient.mk I) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Epsilon1 (S ⧸ I) = I.spanFinrank := by
  sorry

lemma completion_epsilon1_eq : Epsilon1 R = Epsilon1 (AdicCompletion (maximalIdeal R) R) := by
  sorry

lemma epsilon1_add_ringKrullDim_ge :
    Epsilon1 R + ringKrullDim R ≥ (maximalIdeal R).spanFinrank := by
  --take completion, `R = S ⧸ I` with `S` regular, `I ≤ m²`
  --use catenary from CM to obtain `ht(I) = dim(S) - dim(R)`
  sorry

end

variable [IsNoetherianRing R] [IsLocalRing R]

class IsCompleteIntersectionLocalRing extends IsLocalRing R, IsNoetherianRing R where
  ci : Epsilon1 R + ringKrullDim R = (maximalIdeal R).spanFinrank

lemma isCompleteIntersectionLocalRing_of_equiv {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (e : R ≃+* R') [IsCompleteIntersectionLocalRing R] : IsCompleteIntersectionLocalRing R' := by
  sorry

lemma quotient_isCompleteIntersectionLocalRing (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (I : Ideal S) [IsCompleteIntersectionLocalRing (S ⧸ I)] :
    ∃ (rs : List S), I = Ideal.ofList rs ∧ IsRegular S rs := by
  -- `ht(I) = dim(S) - dim(S⧸I) = Epsilon1 (S⧸I) = I.spanFinrank`
  -- generate by regular by results in CM
  sorry

lemma completion_isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    IsCompleteIntersectionLocalRing (AdicCompletion (maximalIdeal R) R) := by
  --use invariance of `Epsilon1`, `dim`!!, span rank of maximal ideal!.
  sorry

theorem isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    ∃ (S : Type u) (_ : CommRing S) (f : S →+* (AdicCompletion (maximalIdeal R) R)) (rs : List S),
      IsRegularLocalRing S ∧ Function.Surjective f ∧
      RingHom.ker f = Ideal.ofList rs ∧ IsRegular S rs := by
  sorry
