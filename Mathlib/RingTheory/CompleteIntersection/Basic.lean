/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.CohenMacaulay.Catenary
public import Mathlib.RingTheory.CohenMacaulay.Maximal
public import Mathlib.RingTheory.CohenStructureTheorem
public import Mathlib.RingTheory.KoszulComplex.Basic

/-!

# Define Complete Intersection Ring

-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

universe u

variable (R : Type u) [CommRing R]

section preliminaries

lemma spanFinrank_eq_of_surjective_of_ker_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (f : R →+* R') (surj : Function.Surjective f) (le : RingHom.ker f ≤ (maximalIdeal R) ^ 2) :
    (maximalIdeal R').spanFinrank = (maximalIdeal R).spanFinrank := by
  classical
  apply le_antisymm (spanFinrank_le_of_surjective f surj)
  let fin := Submodule.FG.finite_generators (maximalIdeal R').fg_of_isNoetherianRing
  let _ := fin.fintype
  rcases surj.list_map (maximalIdeal R').generators.toFinset.toList with ⟨l, hl⟩
  apply le_of_le_of_eq _ (Submodule.FG.generators_ncard (maximalIdeal R').fg_of_isNoetherianRing)
  have leneq : l.length = (maximalIdeal R').generators.ncard := by
    rw [← List.length_map (as := l) f, hl, Set.ncard_eq_toFinset_card', Finset.length_toList]
  rw [← leneq]
  have := ((local_hom_TFAE f).out 0 4).mp (surj.isLocalHom f)
  have mapeq : (maximalIdeal R).map f = maximalIdeal R' := by
    simpa [this] using Ideal.map_comap_of_surjective f surj (maximalIdeal R')
  have hspan : Ideal.span (maximalIdeal R').generators = _ := (maximalIdeal R').span_generators
  have supeq : Ideal.ofList l ⊔ RingHom.ker f = maximalIdeal R := by
    simp [← Ideal.comap_map_of_surjective' f surj, Ideal.map_ofList, hl, Ideal.ofList, hspan, this]
  have : Ideal.ofList l = maximalIdeal R :=
    le_antisymm (by simp [← supeq]) (Submodule.le_of_le_smul_of_le_jacobson_bot
      (maximalIdeal R).fg_of_isNoetherianRing (maximalIdeal_le_jacobson ⊥)
      (le_of_eq_of_le supeq.symm (sup_le_sup_left (by simpa [← pow_two]) _)))
  have spaneq : Submodule.span R (l.toFinset : Set R) = maximalIdeal R := by simp [← this]
  rw [← spaneq]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _))
  exact le_of_eq_of_le (Set.ncard_coe_finset _) (List.toFinset_card_le l)

variable [IsNoetherianRing R] [IsLocalRing R]

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

noncomputable abbrev koszulAlgebra [IsNoetherianRing R] [IsLocalRing R] :=
  koszulComplex.ofList R (maximalIdeal R).finite_generators_of_isNoetherian.toFinset.toList

lemma koszulAlgebra.annihilator_homology [IsNoetherianRing R] [IsLocalRing R] (i : ℕ) :
    maximalIdeal R ≤ Module.annihilator R ((koszulAlgebra R).homology i) := by
  apply le_of_eq_of_le _ (koszulComplex.mem_annihilator_homology_ofList R _ i)
  simpa [Ideal.ofList] using (maximalIdeal R).span_generators.symm

noncomputable instance [IsNoetherianRing R] [IsLocalRing R] (i : ℕ) :
    Module (ResidueField R) ((koszulAlgebra R).homology i) :=
  Module.IsTorsionBySet.module (fun x a ↦
    Module.mem_annihilator.mp ((koszulAlgebra.annihilator_homology R i) a.2) x)

noncomputable def Epsilon1 [IsNoetherianRing R] [IsLocalRing R] : ℕ :=
  Module.finrank (ResidueField R) ((koszulAlgebra R).homology ((maximalIdeal R).spanFinrank - 1))

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

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
lemma epsilon1_add_ringKrullDim_ge :
    Epsilon1 R + ringKrullDim R ≥ (maximalIdeal R).spanFinrank := by
  rcases exist_isRegularLocalRing_surjective_adicCompletion_ker_le R with ⟨S, _, reg, f, surj, le⟩
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
  apply le_of_eq_of_le _ (add_le_add_left
    (WithBot.coe_le_coe.mpr (Ideal.height_le_spanFinrank _ ne)) (ringKrullDim (S ⧸ RingHom.ker f)))
  rw [Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim _ ne]
  simp only [← (isRegularLocalRing_def S).mp reg, Nat.cast_inj]
  rw [spanFinrank_eq_of_surjective_of_ker_le f surj le]

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

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
lemma quotient_isCompleteIntersectionLocalRing (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (I : Ideal S) [IsCompleteIntersectionLocalRing (S ⧸ I)] :
    ∃ (rs : List S), I = Ideal.ofList rs ∧ IsRegular S rs := by
  obtain ⟨d, hd⟩ : ∃ (d : ℕ), ringKrullDim (S ⧸ I) = d := by
    generalize hn : ringKrullDim (S ⧸ I) = n
    induction n with
    | bot =>
      absurd hn
      exact ringKrullDim_ne_bot
    | coe n =>
      induction n with
      | top =>
        absurd hn
        exact ringKrullDim_ne_top
      | coe n => exact ⟨n, rfl⟩
  have ne : I ≠ ⊤ :=  Submodule.Quotient.nontrivial_iff.mp inferInstance
  have := epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank S I ne
  rw [← (isCompleteIntersectionLocalRing_def (S ⧸ I)).mp ‹_›,
    add_comm (Epsilon1 (S ⧸ I) : WithBot ℕ∞), add_comm (Epsilon1 (S ⧸ I) : WithBot ℕ∞),
    ← add_assoc, WithBot.add_natCast_cancel,
    ← Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim I ne, hd,
    WithBot.add_natCast_cancel] at this
  let fin := Submodule.FG.finite_generators I.fg_of_isNoetherianRing
  let _ : Fintype I.generators := fin.fintype
  let rs := I.generators.toFinset.toList
  have spaneq : Ideal.ofList rs = I := by
    simpa [Ideal.ofList, rs] using I.span_generators
  use rs
  refine ⟨spaneq.symm, ?_⟩
  have mem : ∀ r ∈ rs, r ∈ maximalIdeal S := by
    intro r hr
    simp only [Finset.mem_toList, Set.mem_toFinset, rs] at hr
    exact le_maximalIdeal ne (Submodule.FG.generators_mem I hr)
  apply isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing rs mem
  simp only [spaneq, Finset.length_toList, ← Set.ncard_eq_toFinset_card',
    Submodule.FG.generators_ncard I.fg_of_isNoetherianRing, rs]
  rw [← WithBot.coe_inj, this]
  rfl

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
