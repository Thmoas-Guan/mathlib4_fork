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

lemma ringKrullDim_adicCompletion_eq [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  --!!!
  sorry

lemma spanFinrank_maximalIdeal_adicCompletion_eq [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  --!!!
  sorry

lemma spanFinrank_eq_finrank_quotient [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (fg : N.FG) : N.spanFinrank =
    Module.finrank (R ⧸ maximalIdeal R) (N ⧸ (maximalIdeal R) • (⊤ : Submodule R N)) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  let N' := (N ⧸ (maximalIdeal R) • (⊤ : Submodule R N))
  let f : N →ₛₗ[Ideal.Quotient.mk (maximalIdeal R)] N' := {
    __ := Submodule.mkQ ((maximalIdeal R) • (⊤ : Submodule R N))
    map_smul' r x := by simp }
  have surjf : Function.Surjective f := Submodule.mkQ_surjective _
  let fin' : Module.Finite R N := Module.Finite.iff_fg.mpr fg
  let fin := Module.Finite.of_surjective _ surjf
  have : Submodule.spanFinrank (⊤ : Submodule (R ⧸ maximalIdeal R) N') =
    Module.rank (R ⧸ maximalIdeal R) N' := by
    rw [← Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fin.1,
      Submodule.rank_eq_spanRank_of_free]
  simp only [← Module.finrank_eq_rank, Nat.cast_inj] at this
  rw [← this]
  apply le_antisymm
  · sorry
  · sorry

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

lemma epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank_of_surjective (S : Type u)
    [CommRing S] [IsRegularLocalRing S] (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (f : S →+* R) (surj : Function.Surjective f) :
    Epsilon1 R + ringKrullDim S = (RingHom.ker f).spanFinrank + (maximalIdeal R).spanFinrank := by
  obtain ⟨n, hn⟩ : ∃ n, (maximalIdeal R).spanFinrank + n = (maximalIdeal S).spanFinrank :=
    Nat.le.dest (spanFinrank_le_of_surjective f surj)
  induction n generalizing S with
  | zero =>
    let e := RingHom.quotientKerEquivOfSurjective surj
    let _ : Nontrivial (S ⧸ RingHom.ker f) := e.nontrivial
    let _ : IsLocalRing (S ⧸ RingHom.ker f) :=
      have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (RingHom.ker f)) Ideal.Quotient.mk_surjective
    simp only [← (isRegularLocalRing_def S).mp ‹_›, ← Nat.cast_add, Nat.cast_inj]
    have : RingHom.ker f ≤ (maximalIdeal S) ^ 2 := by
      intro x hx
      by_contra nmem
      have le : RingHom.ker f ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
      obtain ⟨reg, dim⟩ := quotient_span_singleton S (le hx) nmem
      have : ∀ y ∈ Ideal.span {x}, f y = 0 := by
        intro y hy
        rcases Ideal.mem_span_singleton.mp hy with ⟨z, hz⟩
        simp [hz, RingHom.mem_ker.mp hx]
      have surj' := Ideal.Quotient.lift_surjective_of_surjective _ this surj
      rw [← (isRegularLocalRing_def _).mp reg, ← (isRegularLocalRing_def _).mp ‹_›,
        ← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj] at dim
      absurd spanFinrank_le_of_surjective _ surj'
      omega
    rw [spanFinrank_eq_of_surjective_of_ker_le f surj this,
      ← epsilon1_eq_of_ringEquiv e, epsilon1_eq_spanFinrank S _ this]
  | succ n ih =>
    obtain ⟨x, hx, nmem⟩ : ∃ x ∈ RingHom.ker f, x ∉ (maximalIdeal S) ^ 2 := by
      by_contra! mem
      simp [spanFinrank_eq_of_surjective_of_ker_le f surj mem] at hn
    have le : RingHom.ker f ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
    obtain ⟨reg, dim⟩ := quotient_span_singleton S (le hx) nmem
    have : ∀ y ∈ Ideal.span {x}, f y = 0 := by
      intro y hy
      rcases Ideal.mem_span_singleton.mp hy with ⟨z, hz⟩
      simp [hz, RingHom.mem_ker.mp hx]
    have surj' := Ideal.Quotient.lift_surjective_of_surjective _ this surj
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
  let _ := Submodule.Quotient.nontrivial_iff.mpr ne
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  convert epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank_of_surjective S (S ⧸ I)
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact Ideal.mk_ker.symm

lemma adicCompletion_epsilon1_eq : Epsilon1 (AdicCompletion (maximalIdeal R) R) = Epsilon1 R := by
  sorry

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
lemma epsilon1_add_ringKrullDim_ge :
    Epsilon1 R + ringKrullDim R ≥ (maximalIdeal R).spanFinrank := by
  rcases exist_isRegularLocalRing_surjective_adicCompletion_ker_le R with ⟨S, _, reg, f, surj, le⟩
  let e := RingHom.quotientKerEquivOfSurjective surj
  let _ : Nontrivial (S ⧸ RingHom.ker f) := e.nontrivial
  let _ : IsLocalRing (S ⧸ RingHom.ker f) :=
    have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (RingHom.ker f)) Ideal.Quotient.mk_surjective
  rw [← adicCompletion_epsilon1_eq, ← ringKrullDim_adicCompletion_eq,
    ← spanFinrank_maximalIdeal_adicCompletion_eq, ← epsilon1_eq_of_ringEquiv e,
    ← ringKrullDim_eq_of_ringEquiv e, epsilon1_eq_spanFinrank S (RingHom.ker f) le, ge_iff_le]
  apply le_of_eq_of_le _ (add_le_add_left (WithBot.coe_le_coe.mpr
    (Ideal.height_le_spanFinrank _ (RingHom.ker_ne_top f))) (ringKrullDim (S ⧸ RingHom.ker f)))
  rw [Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim _ (RingHom.ker_ne_top f)]
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

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
lemma quotient_isCompleteIntersectionLocalRing_iff (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (I : Ideal S) (ne : I ≠ ⊤) : IsCompleteIntersectionLocalRing (S ⧸ I) ↔
    ∃ (rs : List S), I = Ideal.ofList rs ∧ IsRegular S rs := by
  refine ⟨fun h ↦ quotient_isCompleteIntersectionLocalRing S I, fun ⟨rs, hrs, reg⟩ ↦ ?_⟩
  let _ : Nontrivial (S ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr ne
  let _ : IsLocalRing (S ⧸ I) :=
    have : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have eqht : (I.spanFinrank : WithBot ℕ∞) = I.height := by
    change ((I.spanFinrank : ℕ∞) : WithBot ℕ∞) = _
    classical
    apply WithBot.coe_inj.mpr (le_antisymm _ (Ideal.height_le_spanFinrank _ ne))
    have : Ideal.span (rs.toFinset : Set S) = I := by simp [hrs]
    nth_rw 2 [hrs]
    rw [Ideal.ofList_height_eq_length_of_isWeaklyRegular rs reg.1 (by simpa using reg.2.symm),
      Nat.cast_le, ← this]
    exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite rs.toFinset.finite_toSet)
      (le_of_eq_of_le (Set.ncard_coe_finset rs.toFinset) rs.toFinset_card_le)
  rw [isCompleteIntersectionLocalRing_def,
    ← WithBot.add_natCast_cancel (c := (maximalIdeal S).spanFinrank),
    (isRegularLocalRing_def S).mp ‹_›, add_assoc, add_comm _ (ringKrullDim _), ← add_assoc,
    epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank _ _ ne,
    add_assoc, add_comm _ (ringKrullDim (S ⧸ I)), ← add_assoc, eqht,
    Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim _ ne, add_comm]

lemma adicCompletion_isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    IsCompleteIntersectionLocalRing (AdicCompletion (maximalIdeal R) R) := by
  simp [isCompleteIntersectionLocalRing_def, adicCompletion_epsilon1_eq,
    spanFinrank_maximalIdeal_adicCompletion_eq, ringKrullDim_adicCompletion_eq]

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
theorem isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
      (f : S →+* (AdicCompletion (maximalIdeal R) R)) (rs : List S), Function.Surjective f ∧
      RingHom.ker f = Ideal.ofList rs ∧ IsRegular S rs := by
  rw [adicCompletion_isCompleteIntersectionLocalRing_iff]
  refine ⟨fun h ↦ ?_, fun ⟨S, _, regS, f, rs, surj, hrs, reg⟩ ↦ ?_⟩
  · rcases exist_isRegularLocalRing_surjective_adicCompletion R with ⟨S, _, regS, f, surj⟩
    let e := RingHom.quotientKerEquivOfSurjective surj
    let _ : Nontrivial (S ⧸ RingHom.ker f) := e.nontrivial
    let _ : IsLocalRing (S ⧸ RingHom.ker f) :=
      have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (RingHom.ker f)) Ideal.Quotient.mk_surjective
    let _ := isCompleteIntersectionLocalRing_of_ringEquiv e.symm
    rcases quotient_isCompleteIntersectionLocalRing S (RingHom.ker f) with ⟨rs, hrs⟩
    use S, inferInstance, inferInstance, f, rs
  · let e := RingHom.quotientKerEquivOfSurjective surj
    let _ : IsCompleteIntersectionLocalRing (S ⧸ RingHom.ker f) :=
      (quotient_isCompleteIntersectionLocalRing_iff S _ (RingHom.ker_ne_top f)).mpr ⟨rs, hrs, reg⟩
    exact isCompleteIntersectionLocalRing_of_ringEquiv e
