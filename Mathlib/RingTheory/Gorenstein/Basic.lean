/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.CohenMacaulay.Basic
/-!

# The Definition of Gorenstein (Local) Ring

-/

section ENat

lemma WithTop.add_le_add_right_iff (a b : ℕ∞) (c : ℕ) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a with
  | top => simp only [_root_.top_add, top_le_iff]; exact WithTop.add_coe_eq_top_iff
  | coe a => induction b with
    | top => simp
    | coe b => norm_cast; exact Nat.add_le_add_iff_right

lemma WithBot.add_le_add_right_iff (a b : WithBot ℕ∞) (c : ℕ) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a with
  | bot => simp
  | coe a =>
    induction b with
    | bot => simp
    | coe b => norm_cast; exact WithTop.add_le_add_right_iff a b c

lemma WithBot.add_one_le_zero_iff_eq_bot (a : WithBot ℕ∞) :
    a + 1 ≤ 0 ↔ a = ⊥ := by
  induction a with
  | bot => simp
  | coe a => norm_cast; simp

end ENat

universe v u

variable (R : Type u) [CommRing R]

local instance small_of_quotient [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

open CategoryTheory Abelian IsLocalRing Module RingTheory.Sequence

section

universe w

variable [UnivLE.{v, w}]

local instance hasExt_of_small [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

variable {R}

omit [UnivLE.{v, w}] in
lemma mem_quotSMulTop_annihilator (x : R) (M : Type*) [AddCommGroup M] [Module R M] :
    x ∈ Module.annihilator R (QuotSMulTop x M) := by
  refine mem_annihilator.mpr (fun m ↦ ?_)
  rcases Submodule.Quotient.mk_surjective _ m with ⟨m', hm'⟩
  simpa [← hm', ← Submodule.Quotient.mk_smul] using Submodule.smul_mem_pointwise_smul m' x ⊤ trivial

variable [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

lemma projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (M : ModuleCat.{v} R) [Nontrivial M]
    [Module.Finite R M] (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) = projectiveDimension M + 1 := by
  have sub : Subsingleton M ↔ Subsingleton (QuotSMulTop x M) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact Submodule.instSubsingletonQuotient
    · by_contra!
      rw [not_subsingleton_iff_nontrivial] at this
      replace := quotSMulTop_nontrivial mem M
      exact false_of_nontrivial_of_subsingleton (QuotSMulTop x ↑M)

  have aux (n : ℕ) : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) ≤ n ↔
    projectiveDimension M + 1 ≤ n := by
    match n with
    | 0 =>
      have : projectiveDimension M + 1 ≤ 0 ↔ projectiveDimension M = ⊥ :=
        WithBot.add_one_le_zero_iff_eq_bot (projectiveDimension M)
      rw [projectiveDimension_le_iff]
      simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      simp only [CharP.cast_eq_zero, this, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton, sub]
      sorry
    | n + 1 =>
      nth_rw 2 [← Nat.cast_one, Nat.cast_add]
      rw [WithBot.add_le_add_right_iff _ _ 1, projectiveDimension_le_iff,
        projectiveDimension_le_iff]
      simp only [HasProjectiveDimensionLE, hasProjectiveDimensionLT_iff]

      sorry
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simpa only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff,
      ModuleCat.isZero_iff_subsingleton, WithBot.add_eq_bot, WithBot.one_ne_bot, or_false]
      using sub.symm
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

lemma projectiveDimension_quotient_regular_sequence (M : ModuleCat.{v} R) [Nontrivial M]
    [Module.Finite R M] (rs : List R) (reg : IsWeaklyRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) =
    projectiveDimension M + rs.length := by
  generalize len : rs.length = n
  induction n generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using projectiveDimension_eq_of_iso (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  · rename_i n hn _ _
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      let _ : Nontrivial (QuotSMulTop x M) := quotSMulTop_nontrivial mem.1 M
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [projectiveDimension_eq_of_iso
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso, add_comm _ 1,
        ← add_assoc, ← projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular M x this mem.1,
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
          mem.2 len]

noncomputable def ext_quotient_regular_sequence_length (M : ModuleCat.{v} R) [Nontrivial M]
    [Module.Finite R M] (rs : List R) :
    (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) M rs.length) ≃ₗ[R]
    M ⧸ Ideal.ofList rs • (⊤ : Submodule R M) := by
  sorry

lemma ext_subsingleton_of_support_subset (N M : ModuleCat.{v} R) [Nontrivial N] (n : ℕ)
    (h : support R N ⊆ {p | Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ p.1))) M n)}) :
    Subsingleton (Ext.{w} N M n) := by
  --For wjt
  sorry

open Pointwise in
lemma ext_subsingleton_of_all_gt (M : ModuleCat.{v} R) (n : ℕ) (p : Ideal R) [p.IsPrime]
    (ne : p ≠ maximalIdeal R) (h : ∀ q > p, q.IsPrime →
      Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ q))) M (n + 1))) :
    Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ p))) M n) := by
  have plt : p < maximalIdeal R :=  lt_of_le_of_ne (le_maximalIdeal_of_isPrime p) ne
  obtain ⟨x, hx, nmem⟩ : ∃ x ∈ maximalIdeal R, x ∉ p := Set.exists_of_ssubset plt
  let _ : Small.{v} (QuotSMulTop x (R ⧸ p)) :=
    small_of_surjective (Submodule.Quotient.mk_surjective _)
  let _ : Module.Finite R (Shrink.{v, u} (R ⧸ p)) :=
    Module.Finite.equiv (Shrink.linearEquiv R _).symm
  let _ : Nontrivial (QuotSMulTop x (Shrink.{v, u} (R ⧸ p))) :=
    quotSMulTop_nontrivial hx _
  have : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x (Shrink.{v, u} (R ⧸ p)))) M (n + 1)) := by
    apply ext_subsingleton_of_support_subset
    intro q hq
    apply h q.1 _ q.2
    simp only [support_quotSMulTop, (Shrink.linearEquiv R (R ⧸ p)).support_eq, Set.mem_inter_iff,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hq
    have : q.asIdeal ≠ p := ne_of_mem_of_not_mem' hq.2 nmem
    apply lt_of_le_of_ne _ (ne_of_mem_of_not_mem' hq.2 nmem).symm
    apply le_of_eq_of_le Ideal.annihilator_quotient.symm (Module.annihilator_le_of_mem_support hq.1)
  let S := (ModuleCat.of R (Shrink.{v, u} (R ⧸ p))).smulShortComplex x
  have reg : IsSMulRegular (Shrink.{v, u} (R ⧸ p)) x := by
    rw [(Shrink.linearEquiv R _).isSMulRegular_congr, isSMulRegular_iff_right_eq_zero_of_smul]
    intro r hr
    simpa [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, nmem] using hr
  have S_exact : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact reg
  have exac := Ext.contravariant_sequence_exact₁' S_exact M n (n + 1) (add_comm 1 n)
  have epi := exac.epi_f ((@AddCommGrp.isZero_of_subsingleton _ this).eq_zero_of_tgt _)
  have : S.f = x • 𝟙 (ModuleCat.of R (Shrink.{v, u} (R ⧸ p))) := by
    ext
    simp [S]
  simp only [S, this, AddCommGrp.epi_iff_surjective, AddCommGrp.hom_ofHom] at epi
  have : Function.Surjective (x • (LinearMap.id (R := R) (M := Ext S.X₂ M n))) := by

    sorry
  have : x ∈ (Module.annihilator R (Ext S.X₂ M n)).jacobson := by
    sorry
  by_contra ntr
  let _ : Nontrivial (Ext S.X₂ M n) := not_subsingleton_iff_nontrivial.mp ntr
  --absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this

  sorry

lemma injectiveDimension_eq_sSup (M : ModuleCat.{v} R) :
    injectiveDimension M = ⨆ n ∈ {i | Nontrivial
      (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)}, (n : ℕ∞) := by

  sorry

lemma supportDim_le_injectiveDimension (M : ModuleCat.{v} R)
    (h : injectiveDimension M ≠ ⊤) : supportDim R M ≤ injectiveDimension M := by

  sorry

lemma injectiveDimension_eq_depth (M : ModuleCat.{v} R) (h : injectiveDimension M ≠ ⊤) :
    injectiveDimension M = IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by

  sorry

end

class IsGorensteinLocalRing : Prop extends IsLocalRing R, IsNoetherianRing R where
  injdim : injectiveDimension (ModuleCat.of R R) ≠ ⊤

theorem isCohenMacaulayLocalRing_of_isGorensteinLocalRing [IsGorensteinLocalRing R] :
    IsCohenMacaulayLocalRing R := by
  sorry

/-
variable {R} in
class Ideal.isIrreducible (I : Ideal R) : Prop where
  irr : ∀ {J₁ J₂ : Ideal R}, J₁ ⊓ J₂ = I → (J₁ = I ∨ J₂ = I)

local instance hasExt_self : CategoryTheory.HasExt.{u} (ModuleCat.{u} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{u} (ModuleCat.{u} R)

variable [IsLocalRing R] [IsNoetherianRing R]

lemma injectiveDimension_self_eq_ringKrullDim_of_ne_top
    (h : injectiveDimension (ModuleCat.of R R) ≠ ⊤) :
    injectiveDimension (ModuleCat.of R R) = ringKrullDim R := by
  sorry

lemma ext_subsingleton_or_isPrincipal_of_injectiveDimension_eq_ringKrullDim (n : ℕ)
    (h : injectiveDimension (ModuleCat.of R R) = ringKrullDim R) (h : ringKrullDim R = n) :
    (∀ i ≠ n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal := by
  sorry

lemma isGorensteinLocalRing_of_exist_ext_vanish (n : ℕ) (h : ringKrullDim R = n) (h : ∃ i > n,
    Subsingleton (Ext (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) :
    IsGorensteinLocalRing R := by
  sorry

theorem isGroensteinLocalRing_tfae (n : ℕ) (h : ringKrullDim R = n) :
    [IsGorensteinLocalRing R, injectiveDimension (ModuleCat.of R R) = n,
     (∀ i ≠ n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal,
     ∃ i > n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i),
     (∀ i < n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal,
     IsCohenMacaulayLocalRing R ∧ (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R))
      (ModuleCat.of R R) n)).IsPrincipal,
     IsCohenMacaulayLocalRing R ∧ ∀ {J : Ideal R}, maximalIdeal R ∈ J.minimalPrimes →
      J.spanFinrank = n → J.isIrreducible,
     IsCohenMacaulayLocalRing R ∧ ∃ J : Ideal R, maximalIdeal R ∈ J.minimalPrimes ∧
      J.spanFinrank = n ∧ J.isIrreducible
     ].TFAE := by
  tfae_have 1 → 2 := by

    sorry
  tfae_have 2 → 3 := by

    sorry
  tfae_have 3 → 4 := by
    --trivial
    sorry
  tfae_have 4 → 1 := by

    sorry
  tfae_have 3 → 5 := by
    --trivial
    sorry
  tfae_have 5 → 6 := by
    --CM basic
    sorry
  tfae_have 6 → 7 := by

    sorry
  tfae_have 7 → 8 := by
    --trivial
    sorry
  tfae_have 8 → 3 := by

    sorry
  sorry
-/
