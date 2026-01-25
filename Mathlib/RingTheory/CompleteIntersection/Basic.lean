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

lemma spanFinrank_eq_of_ringEquiv {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (e : R ≃+* R') : (maximalIdeal R).spanFinrank = (maximalIdeal R').spanFinrank := by
  sorry

lemma spanFinrank_le_of_surjective {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (f : R →+* R') (surj : Function.Surjective f) :
    (maximalIdeal R').spanFinrank ≤ (maximalIdeal R).spanFinrank := by
  sorry
lemma spanFinrank_eq_of_surjective_of_ker_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (f : R →+* R') (surj : Function.Surjective f) (le : RingHom.ker f ≤ (maximalIdeal R) ^ 2) :
    (maximalIdeal R').spanFinrank = (maximalIdeal R).spanFinrank := by
  sorry

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

lemma epsilon1_eq_of_ringEquiv {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R'] (e : R ≃+* R') :
    Epsilon1 R = Epsilon1 R' := by
  sorry

section epsilon1

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

lemma epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (I : Ideal S) (ne : I ≠ ⊤) :
    letI : IsLocalRing (S ⧸ I) :=
      have : Nontrivial (S ⧸ I) :=
        Submodule.Quotient.nontrivial_iff.mpr ne
      have : IsLocalHom (Ideal.Quotient.mk I) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Epsilon1 (S ⧸ I) + ringKrullDim S = I.spanFinrank + (maximalIdeal (S ⧸ I)).spanFinrank := by
  --quotient by elements outside of `m²`
  sorry

lemma adicCompletion_epsilon1_eq : Epsilon1 (AdicCompletion (maximalIdeal R) R) = Epsilon1 R := by
  sorry

lemma epsilon1_add_ringKrullDim_ge :
    Epsilon1 R + ringKrullDim R ≥ (maximalIdeal R).spanFinrank := by
  rcases exist_isRegularLocalRing_surjective_adicCompletion_ker_le R with ⟨S, _, _, f, surj, le⟩
  let e := RingHom.quotientKerEquivOfSurjective surj
  let _ : Nontrivial (S ⧸ RingHom.ker f) := e.nontrivial
  have ne : RingHom.ker f ≠ ⊤ := by simpa [← Submodule.Quotient.nontrivial_iff]
  let _ : IsLocalRing (S ⧸ RingHom.ker f) :=
    have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (RingHom.ker f)) Ideal.Quotient.mk_surjective
  rw [← adicCompletion_epsilon1_eq, ← ringKrullDim_adicCompletion_eq,
    ← spanFinrank_maximalIdeal_adicCompletion_eq, ← epsilon1_eq_of_ringEquiv e,
    ← ringKrullDim_eq_of_ringEquiv e, epsilon1_eq_spanFinrank S (RingHom.ker f) le, ge_iff_le]
  apply le_trans _ (add_le_add_left (WithBot.coe_le_coe.mpr (Ideal.height_le_spanFinrank _ ne))
    (ringKrullDim (S ⧸ RingHom.ker f)))
  --use catenary from CM to obtain `ht(I) = dim(S) - dim(R)`
  sorry

end epsilon1

variable [IsNoetherianRing R] [IsLocalRing R]

class IsCompleteIntersectionLocalRing extends IsLocalRing R, IsNoetherianRing R where
  ci : Epsilon1 R + ringKrullDim R = (maximalIdeal R).spanFinrank

lemma isCompleteIntersectionLocalRing_def : IsCompleteIntersectionLocalRing R ↔
    Epsilon1 R + ringKrullDim R = (maximalIdeal R).spanFinrank :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isCompleteIntersectionLocalRing_of_ringEquiv {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (e : R ≃+* R') [IsCompleteIntersectionLocalRing R] : IsCompleteIntersectionLocalRing R' := by
  simpa [isCompleteIntersectionLocalRing_def, ← epsilon1_eq_of_ringEquiv e,
    ← ringKrullDim_eq_of_ringEquiv e, ← spanFinrank_eq_of_ringEquiv e]
    using (isCompleteIntersectionLocalRing_def R).mp ‹_›

lemma quotient_isCompleteIntersectionLocalRing (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (I : Ideal S) [IsCompleteIntersectionLocalRing (S ⧸ I)] :
    ∃ (rs : List S), I = Ideal.ofList rs ∧ IsRegular S rs := by
  have : I.height = I.spanFinrank := by
    have ne : I ≠ ⊤ :=  Submodule.Quotient.nontrivial_iff.mp inferInstance
    have := epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank S I ne
    rw [← (isCompleteIntersectionLocalRing_def (S ⧸ I)).mp ‹_›] at this
    rw [add_comm (Epsilon1 (S ⧸ I) : WithBot ℕ∞), add_comm (Epsilon1 (S ⧸ I) : WithBot ℕ∞),
      ← add_assoc] at this

    --from CM, `I.height + ringKrullDim (S ⧸ I) = ringKrullDim S`
    sorry
  -- generate by regular by results in CM
  sorry

lemma adicCompletion_isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    IsCompleteIntersectionLocalRing (AdicCompletion (maximalIdeal R) R) := by
  simp [isCompleteIntersectionLocalRing_def, adicCompletion_epsilon1_eq,
    spanFinrank_maximalIdeal_adicCompletion_eq, ringKrullDim_adicCompletion_eq]

theorem isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    ∃ (S : Type u) (_ : CommRing S) (f : S →+* (AdicCompletion (maximalIdeal R) R)) (rs : List S),
      IsRegularLocalRing S ∧ Function.Surjective f ∧
      RingHom.ker f = Ideal.ofList rs ∧ IsRegular S rs := by
  sorry
