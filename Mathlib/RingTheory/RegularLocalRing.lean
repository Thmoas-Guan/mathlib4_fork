/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Polynomial.Basic

/-!
# Define Regular Local Ring
-/

open IsLocalRing

variable (R : Type*) [CommRing R]

class IsRegularLocalRing : Prop extends IsLocalRing R, IsNoetherianRing R where
  reg : (Submodule.spanFinrank (maximalIdeal R)) = ringKrullDim R

variable [IsLocalRing R]

lemma spanFinrank_eq_finrank_quotient (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : (⊤ : Submodule R M).spanFinrank =
    Module.finrank (R ⧸ (maximalIdeal R)) (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) := by
  sorry

lemma spanFinrank_maximalIdeal (fg : (maximalIdeal R).FG) :
    (Submodule.spanFinrank (maximalIdeal R)) =
    Module.finrank (ResidueField R) (CotangentSpace R) := by
  sorry

lemma quotient_isRegularLocalRing_tfae (S : Finset R) (sub : (S : Set R) ⊆ maximalIdeal R)
    [IsRegularLocalRing R] :
    [∃ (T : Finset R), S ⊆ T ∧ T.card = ringKrullDim R ∧ Ideal.span T = maximalIdeal R,
     LinearIndependent (ResidueField R) ((⇑(maximalIdeal R).toCotangent).comp (Set.inclusion sub)),
     IsRegularLocalRing (R ⧸ Ideal.span (S : Set R)) ∧
     (ringKrullDim (R ⧸ Ideal.span (S : Set R)) + S.card = ringKrullDim R),
     IsRegularLocalRing (R ⧸ Ideal.span (S : Set R))].TFAE := by
  sorry

theorem isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R := by
  sorry

open RingTheory.Sequence in
theorem isRegular_of_span_eq_maximalIdeal (rs : List R) (eq : Ideal.ofList rs = maximalIdeal R)
    (len : rs.length = ringKrullDim R) : IsRegular R rs := by
  sorry

class IsRegularRing : Prop where
  localization_isRegular : ∀ p : Ideal R, ∀ (_ : p.IsPrime),
    IsRegularLocalRing (Localization.AtPrime p)

open Polynomial in
lemma polynomial_isRegularRing_of_isRegularRing [IsRegularRing R] : IsRegularRing R[X] := by
  sorry

lemma mvPolynomial_isRegularRing_of_isRegularRing [IsRegularRing R] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) R) := by
  sorry
