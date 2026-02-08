module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.Depth
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Flat

@[expose] public section

section ENat

variable {α : Type*} [Add α] (a : α)

section

open WithTop

lemma _root_.IsAddLeftRegular.withTop (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

lemma _root_.IsAddRightRegular.withTop (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

end

section

open WithBot

lemma _root_.IsAddLeftRegular.withBot (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

lemma _root_.IsAddRightRegular.withBot (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

end


lemma WithBot.add_natCast_cancel {a b : WithBot ℕ∞} {c : ℕ} : a + c = b + c ↔ a = b :=
  (IsAddRightRegular.all c).withTop.withBot.eq_iff

lemma WithBot.add_one_cancel {a b : WithBot ℕ∞} : a + 1 = b + 1 ↔ a = b :=
  (IsAddRightRegular.all 1).withTop.withBot.eq_iff

lemma WithBot.natCast_add_cancel {a b : WithBot ℕ∞} {c : ℕ} : c + a = c + b ↔ a = b :=
  (IsAddLeftRegular.all c).withTop.withBot.eq_iff

lemma WithBot.one_add_cancel {a b : WithBot ℕ∞} : 1 + a = 1 + b ↔ a = b :=
  (IsAddLeftRegular.all 1).withTop.withBot.eq_iff

end ENat

universe v u

open CategoryTheory Abelian Limits ModuleCat

open RingTheory.Sequence IsLocalRing Ideal Pointwise IsSMulRegular LinearMap Module


variable {R : Type u} [CommRing R]

section

lemma Submodule.smul_top_eq_comap_smul_top_of_surjective {R M M₂ : Type*} [CommSemiring R]
    [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R M₂] (I : Ideal R) (f : M →ₗ[R] M₂)
    (h : Function.Surjective f) : I • ⊤ ⊔ (LinearMap.ker f) = comap f (I • ⊤) := by
  refine le_antisymm (sup_le (smul_top_le_comap_smul_top I f) (LinearMap.ker_le_comap f)) ?_
  rw [← Submodule.comap_map_eq f (I • (⊤ : Submodule R M)),
    Submodule.comap_le_comap_iff_of_surjective h,
    Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr h]

lemma smul_id_postcomp_eq_zero_of_mem_ann [Small.{v} R] {M N : ModuleCat.{v} R}
    {r : R} (mem_ann : r ∈ Module.annihilator R N) (n : ℕ) :
    AddCommGrpCat.ofHom (((Ext.mk₀ (r • (𝟙 M)))).postcomp N (add_zero n)) = 0 := by
  ext h
  have eq0 : r • (𝟙 N) = 0 := ModuleCat.hom_ext
    (LinearMap.ext (fun x ↦ Module.mem_annihilator.mp mem_ann _))
  have : r • h = (Ext.mk₀ (r • (𝟙 N))).comp h (zero_add n) := by simp [Ext.mk₀_smul]
  simp [Ext.mk₀_smul, this, eq0]

end

section Rees

lemma Ideal.quotient_smul_top_lt_of_le_smul_top (I : Ideal R) {M : Type*} [AddCommGroup M]
    [Module R M] {p : Submodule R M} (h : I • (⊤ : Submodule R M) < ⊤)
    (le : p ≤ I • (⊤ : Submodule R M)) : I • (⊤ : Submodule R (M ⧸ p)) < ⊤ := by
  rw [lt_top_iff_ne_top]
  by_contra eq
  absurd lt_top_iff_ne_top.mp h
  have := Submodule.smul_top_eq_comap_smul_top_of_surjective I p.mkQ p.mkQ_surjective
  simpa [eq, le] using this

variable [Small.{v} R]

lemma exists_isRegular_of_exists_subsingleton_ext [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (exists_N : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
    let : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    rcases exists_N with ⟨N, ntr, fin, h_supp, h_ext⟩
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    -- use `Ext N M 0` vanish to obtain an `M`-regular element `x` in `Ann(N)`
    let _ : Subsingleton (N ⟶ M) := Ext.addEquiv₀.subsingleton_congr.mp (h_ext 0 n.zero_lt_succ)
    have : Subsingleton (N →ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
    rcases subsingleton_linearMap_iff.mp this with ⟨x, mem_ann, hx⟩
    -- take a power of it to make `xᵏ` fall into `I`
    have := Ideal.le_radical mem_ann
    rw [h_supp', Ideal.mem_radical_iff] at this
    rcases this with ⟨k, hk⟩
    -- prepare to apply induction hypotesis to `M ⧸ xᵏM`
    have le_smul : x ^ k • (⊤ : Submodule R M) ≤ I • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact (Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk))
    have smul_lt' := I.quotient_smul_top_lt_of_le_smul_top smul_lt le_smul
    -- verify that `N` indeed make `M ⧸ xᵏM` satisfy the induction hypothesis
    have exists_N' : (∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi
      -- the vanishing of `Ext` is obtained from the (covariant) long exact sequence given by
      -- `M.smulShortComplex (x ^ k)`
      have zero1 : IsZero (AddCommGrpCat.of (Ext N M i)) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext i (Nat.lt_add_right 1 hi))
      have zero2 : IsZero (AddCommGrpCat.of (Ext N M (i + 1))) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N (hx.pow k).smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    rcases ih (ModuleCat.of R (QuotSMulTop (x ^ k) M)) smul_lt' exists_N' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hx.pow k, reg⟩

lemma CategoryTheory.Abelian.Ext.pow_mono_of_mono
    (a : R) {k : ℕ} (kpos : k > 0) (i : ℕ) {M N : ModuleCat.{v} R}
    (f_mono : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp
    N (add_zero i)))) : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M (a ^ k)).f).postcomp
    N (add_zero i))) := by
  induction k with
  | zero => simp at kpos
  | succ k ih =>
    rw [pow_succ]
    by_cases eq0 : k = 0
    · rw [eq0, pow_zero, one_mul]
      exact f_mono
    · have : (a ^ k * a) • (LinearMap.id (R := R) (M := M)) =
        (a • (LinearMap.id (M := M))).comp ((a ^ k) • (LinearMap.id (M := M))) := by
        rw [LinearMap.comp_smul, LinearMap.smul_comp, smul_smul, LinearMap.id_comp]
      simpa [smulShortComplex, this, ModuleCat.ofHom_comp, ← extFunctorObj_map,
        (extFunctorObj N i).map_comp] using mono_comp' (ih (Nat.zero_lt_of_ne_zero eq0)) f_mono

lemma ext_subsingleton_of_exists_isRegular [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (N : ModuleCat.{v} R) [Nntr : Nontrivial N] [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (exists_rs : ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs) :
    ∀ i < n, Subsingleton (Ext N M i) := by
  induction n generalizing M with
  | zero => simp
  | succ n ih =>
    rcases exists_rs with ⟨rs, len, mem, reg⟩
    rintro i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] =>
      absurd len
      simp
    | a :: rs' =>
      -- find a positive power of `a` lying in `Ann(N)`
      rcases le_rad (mem a List.mem_cons_self) with ⟨k, hk⟩
      have kpos : k > 0 := by
        by_contra h
        simp only [Nat.eq_zero_of_not_pos h, pow_zero, Module.mem_annihilator, one_smul] at hk
        exact (not_nontrivial_iff_subsingleton.mpr (subsingleton_of_forall_eq 0 hk)) Nntr
      simp only [isRegular_cons_iff] at reg
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [List.length_cons, Nat.add_left_inj] at len
      -- prepare to apply induction hypothesis to `M/aM`
      let M' := (QuotSMulTop a M)
      have le_smul : a • ⊤ ≤ I • (⊤ : Submodule R M) := by
        rw [← Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr mem.1)
      have smul_lt' := I.quotient_smul_top_lt_of_le_smul_top smul_lt le_smul
      by_cases eq0 : i = 0
      · -- vanishing of `Ext N M 0` follows from `aᵏ ∈ Ann(N)`
        rw [eq0]
        have : Subsingleton (N →ₗ[R] M) := subsingleton_linearMap_iff.mpr ⟨a ^ k, hk, reg.1.pow k⟩
        exact (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton
      · let g := (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp N (add_zero i)))
        -- from the (covariant) long exact sequence given by `M.smulShortComplex a`
        -- we obtain scalar multiple by `a` on `Ext N M i` is injective
        have mono_g : Mono g := by
          apply (Ext.covariant_sequence_exact₁' N reg.1.smulShortComplex_shortExact (i - 1) i
            (Nat.succ_pred_eq_of_ne_zero eq0)).mono_g (IsZero.eq_zero_of_src _ _)
          exact @AddCommGrpCat.isZero_of_subsingleton _
            (ih (ModuleCat.of R M') smul_lt' ⟨rs', len, mem.2, reg.2⟩ (i - 1) (by omega))
        let gk := (AddCommGrpCat.ofHom
          ((Ext.mk₀ (smulShortComplex M (a ^ k)).f).postcomp N (add_zero i)))
        have mono_gk := Ext.pow_mono_of_mono a kpos i mono_g
        -- scalar multiple by `aᵏ` on `Ext N M i` is zero since `aᵏ ∈ Ann(N)`, so `Ext N M i` vanish
        have zero_gk : gk = 0 := smul_id_postcomp_eq_zero_of_mem_ann hk i
        exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ zero_gk)

/--
The Rees theorem
For any `n : ℕ`, noetherian ring `R`, `I : Ideal R`, and finitely generated and nontrivial
`R`-module `M` satisfying `IM < M`, we proved TFAE:
· for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· `∀ i < n, Ext (A⧸I) M i = 0`
· there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· there exists a `M`-regular sequence of length `n` with every element in `I`
-/
lemma exists_isRegular_tfae [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    [∀ N : ModuleCat.{v} R, (Nontrivial N ∧ Module.Finite R N ∧
     Module.support R N ⊆ PrimeSpectrum.zeroLocus I) → ∀ i < n, Subsingleton (Ext N M i),
     ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
     ∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
     Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i),
     ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs
     ].TFAE := by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, annihilator_quotient]
  tfae_have 1 → 2 := fun h1 i hi ↦ h1 (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    ⟨inferInstance, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm, suppQ.subset⟩ i hi
  tfae_have 2 → 3 := fun h2 ↦ ⟨(ModuleCat.of R (Shrink.{v} (R ⧸ I))),
    inferInstance, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm, suppQ, h2⟩
  tfae_have 3 → 4 := exists_isRegular_of_exists_subsingleton_ext I n M smul_lt
  tfae_have 4 → 1 := fun h4 N ⟨Nntr, Nfin, Nsupp⟩ i hi ↦
    ext_subsingleton_of_exists_isRegular I n N Nsupp M smul_lt h4 i hi
  tfae_finish

end Rees

section depth

variable [Small.{v} R]

/-- The depth between two `R`-modules defined as the minimal nontrivial `Ext` between them. -/
noncomputable def moduleDepth (N M : ModuleCat.{v} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}

/-- The depth of a `R`-module `M` with respect to an ideal `I`,
defined as `moduleDepth (R⧸ I, M)`. -/
noncomputable def Ideal.depth (I : Ideal R) (M : ModuleCat.{v} R) : ℕ∞ :=
  moduleDepth (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M

/-- For a local ring `R`, the depth of a `R`-module with respect to the maximal ideal. -/
noncomputable def IsLocalRing.depth [IsLocalRing R] (M : ModuleCat.{v} R) : ℕ∞ :=
  (IsLocalRing.maximalIdeal R).depth M

open Classical in
lemma moduleDepth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext N M n)) :
    moduleDepth N M = Nat.find h := by
  apply le_antisymm
  · simp only [moduleDepth, sSup_le_iff, Set.mem_setOf_eq]
    intro n hn
    by_contra gt
    absurd Nat.find_spec h
    exact not_nontrivial_iff_subsingleton.mpr (hn (Nat.find h) (not_le.mp gt))
  · simp only [moduleDepth]
    apply le_sSup
    simp only [Set.mem_setOf_eq, Nat.cast_lt, Nat.lt_find_iff]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mp (hi i (le_refl i))

lemma moduleDepth_eq_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  refine ⟨fun h ↦ ?_, fun h ↦ csSup_eq_top_of_top_mem (fun i _ ↦ h i)⟩
  by_contra! exist
  rw [moduleDepth_eq_find N M exist] at h
  simp at h

lemma moduleDepth_lt_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M < ⊤ ↔ ∃ n, Nontrivial (Ext N M n) := by
  convert (moduleDepth_eq_top_iff N M).not
  · exact lt_top_iff_ne_top
  · push_neg
    rfl

lemma moduleDepth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : moduleDepth N M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨ntr, h⟩ ↦ ?_⟩
  · have exist := (moduleDepth_lt_top_iff N M).mp (by simp [h])
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj] at h
    refine ⟨h ▸ Nat.find_spec exist, fun i hi ↦ ?_⟩
    exact not_nontrivial_iff_subsingleton.mp (Nat.find_min exist (lt_of_lt_of_eq hi h.symm))
  · have exist : ∃ n, Nontrivial (Ext N M n) := by use n
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj, Nat.find_eq_iff, ntr, true_and]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mpr (h i hi)

lemma ext_subsingleton_of_lt_moduleDepth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < moduleDepth N M) : Subsingleton (Ext N M i) := by
  by_cases lttop : moduleDepth N M < ⊤
  · let _ : Nonempty {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)} :=
      Nonempty.intro ⟨(0 : ℕ∞), by simp⟩
    exact ENat.sSup_mem_of_nonempty_of_lt_top lttop i lt
  · simp only [not_lt, top_le_iff, moduleDepth_eq_top_iff] at lttop
    exact lttop i

lemma moduleDepth_eq_sup_nat (N M : ModuleCat.{v} R) : moduleDepth N M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  simp only [moduleDepth]
  by_cases h : ⊤ ∈ {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)}
  · rw [csSup_eq_top_of_top_mem h, eq_comm, ENat.eq_top_iff_forall_ge]
    intro m
    apply le_sSup
    simp only [Set.mem_setOf_eq, ENat.coe_lt_top, forall_const] at h
    simpa using fun i _ ↦ h i
  · congr
    ext n
    exact ⟨fun mem ↦ ⟨top_notMem_iff.mp h n mem, mem⟩, fun mem ↦ mem.2⟩

lemma moduleDepth_eq_depth_of_supp_eq [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Nfin : Module.Finite R N]
    [Nntr : Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = I.depth M := by
  have (n : ℕ) : (∀ i < n, Subsingleton (Ext N M i)) ↔
    (∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply ((exists_isRegular_tfae I n M smul_lt).out 1 2).mpr
      use N
    · have rees := ((exists_isRegular_tfae I n M smul_lt).out 0 1).mpr h
      apply rees N
      simp [Nfin, Nntr, hsupp]
  simp only [moduleDepth_eq_sup_nat, Ideal.depth]
  congr
  ext n
  simp only [and_congr_right_iff]
  intro lt_top
  convert this n.toNat
  <;> nth_rw 1 [← ENat.coe_toNat (LT.lt.ne_top lt_top), ENat.coe_lt_coe]

open Opposite in
lemma moduleDepth_eq_of_iso_fst (M : ModuleCat.{v} R) {N N' : ModuleCat.{v} R} (e : N ≅ N') :
    moduleDepth N M = moduleDepth N' M := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    (((extFunctor.{v} i).mapIso e.symm.op).app M).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma moduleDepth_eq_of_iso_snd (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    moduleDepth N M = moduleDepth N M' := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    ((extFunctorObj N i).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma Ideal.depth_eq_of_iso (I : Ideal R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    I.depth M = I.depth M' :=
  moduleDepth_eq_of_iso_snd (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) e

lemma IsLocalRing.depth_eq_of_iso [IsLocalRing R] {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    IsLocalRing.depth M = IsLocalRing.depth M' :=
  (maximalIdeal R).depth_eq_of_iso e

lemma moduleDepth_eq_zero_of_hom_nontrivial (N M : ModuleCat.{v} R) :
    moduleDepth N M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [moduleDepth] at h
    have : 1 ∉ {n : ℕ∞ | ∀ (i : ℕ), i < n → Subsingleton (Ext N M i)} := by
      by_contra mem
      absurd le_sSup mem
      simp [h]
    simp only [Set.mem_setOf_eq, Nat.cast_lt_one, forall_eq,
      not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr] at this
    exact (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mp this
  · apply nonpos_iff_eq_zero.mp (sSup_le (fun n mem ↦ ?_))
    by_contra pos
    absurd mem 0 (lt_of_not_ge pos)
    simpa [not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr]
      using (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mpr h

lemma moduleDepth_ge_min_of_shortExact (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₂ N ≥ moduleDepth S.X₁ N ⊓ moduleDepth S.X₃ N := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrpCat.of (Ext S.X₁ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N i)) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₂' hS N i)
    (zero3.eq_zero_of_src _) (zero1.eq_zero_of_tgt _)

lemma moduleDepth_eq_sSup_length_regular [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Nfin : Module.Finite R N]
    [Nntr : Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  rw [moduleDepth_eq_sup_nat]
  congr
  ext m
  simp only [exists_prop]
  refine ⟨fun ⟨lt_top, h⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt lt_top) with ⟨n, hn⟩
    simp only [← hn, Nat.cast_lt, Nat.cast_inj] at h ⊢
    have : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i) := by
      use N
    rcases ((exists_isRegular_tfae I n M smul_lt).out 2 3).mp this with ⟨rs, len, mem, reg⟩
    use rs
  · simp only [← len, ENat.coe_lt_top, Nat.cast_lt, true_and]
    have rees := ((exists_isRegular_tfae I rs.length M smul_lt).out 3 0).mp (by use rs)
    apply rees N
    simp [Nntr, Nfin, hsupp]

lemma IsLocalRing.ideal_depth_eq_sSup_length_regular [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M]
    [Nontrivial M] : I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  let _ := Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr netop
  have smul_lt : I • (⊤ : Submodule R M) < ⊤ := lt_of_le_of_lt
      (Submodule.smul_mono (le_maximalIdeal netop) (le_refl _))
      (Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)))
  apply moduleDepth_eq_sSup_length_regular I (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M smul_lt
  rw [(Shrink.linearEquiv R (R ⧸ I)).support_eq, Module.support_eq_zeroLocus,
    Ideal.annihilator_quotient]

lemma IsLocalRing.depth_eq_sSup_length_regular [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ maximalIdeal R) } :=
  IsLocalRing.ideal_depth_eq_sSup_length_regular (maximalIdeal R) IsPrime.ne_top' M

lemma IsLocalRing.ideal_depth_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    I.depth M ≤ IsLocalRing.depth M := by
  rw [ideal_depth_eq_sSup_length_regular I netop, depth_eq_sSup_length_regular]
  apply sSup_le (fun n hn ↦ le_sSup ?_)
  rcases hn with ⟨rs, reg, mem, len⟩
  have : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r a ↦ (le_maximalIdeal netop) (mem r a)
  use rs

omit [Small.{v, u} R] in
lemma Submodule.comap_lt_top_of_lt_range {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (p : Submodule R N)
    (lt : p < LinearMap.range f) : Submodule.comap f p < ⊤ := by
  obtain ⟨x, ⟨y, hy⟩, nmem⟩ : ∃ x ∈ LinearMap.range f, x ∉ p := Set.exists_of_ssubset lt
  have : y ∉ Submodule.comap f p := by simpa [hy] using nmem
  exact lt_of_le_not_ge (fun _ a ↦ trivial) fun a ↦ this (a trivial)

lemma moduleDepth_quotSMulTop_succ_eq_moduleDepth (N M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (QuotSMulTop x M)) + 1 = moduleDepth N M := by
  simp only [moduleDepth, add_comm]
  have iff (i : ℕ) : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) ↔
    (Subsingleton (Ext N M i) ∧ Subsingleton (Ext N M (i + 1))) := by
    refine ⟨fun h ↦ ?_, fun ⟨h1, h3⟩ ↦ ?_⟩
    · constructor
      · exact @Function.Injective.subsingleton _ _ _ ((AddCommGrpCat.mono_iff_injective _).mp <|
          (Ext.covariant_sequence_exact₂' N reg.smulShortComplex_shortExact i).mono_g
          (smul_id_postcomp_eq_zero_of_mem_ann mem i)) h
      · exact @Function.Surjective.subsingleton _ _ _ h ((AddCommGrpCat.epi_iff_surjective _).mp <|
          (Ext.covariant_sequence_exact₁' N reg.smulShortComplex_shortExact i (i + 1) rfl).epi_f
          (smul_id_postcomp_eq_zero_of_mem_ann mem (i + 1)))
    · exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' N reg.smulShortComplex_shortExact i (i + 1) rfl)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h1).eq_zero_of_src _)
        ((@AddCommGrpCat.isZero_of_subsingleton _ h3).eq_zero_of_tgt _)
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    by_cases eq0 : i = 0
    · rw [eq0, Ext.addEquiv₀.subsingleton_congr, ModuleCat.homAddEquiv.subsingleton_congr]
      exact linearMap_subsingleton_of_mem_annihilator reg mem
    · have eq : i - 1 + 1 = i := Nat.sub_one_add_one eq0
      have : i - 1 < n := by
        enat_to_nat
        omega
      have := ((iff (i - 1)).mp (hn (i - 1) this)).2
      simpa only [eq] using this
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        enat_to_nat
        omega
      rw [add_comm, ← this]
      apply add_le_add_left
      apply le_sSup
      intro i hi
      have lt2 : i + 1 < n := by
        enat_to_nat
        omega
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

lemma Ideal.depth_quotSMulTop_succ_eq_moduleDepth (I : Ideal R) (M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ I) :
    I.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = I.depth M := by
  apply moduleDepth_quotSMulTop_succ_eq_moduleDepth _ M x reg
  simpa [LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ I)), Ideal.annihilator_quotient]

lemma IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth [IsLocalRing R] (M : ModuleCat.{v} R)
    (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 = IsLocalRing.depth M :=
  (maximalIdeal R).depth_quotSMulTop_succ_eq_moduleDepth M x reg mem

lemma moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth (N M : ModuleCat.{v} R)
    (rs : List R) (reg : IsWeaklyRegular M rs) (h : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    moduleDepth N M := by
  generalize len : rs.length = n
  induction n generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using moduleDepth_eq_of_iso_snd N (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  · rename_i n hn
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [moduleDepth_eq_of_iso_snd N
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso,
        ← moduleDepth_quotSMulTop_succ_eq_moduleDepth N M x this (h x List.mem_cons_self),
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
        (fun r hr ↦ h r (List.mem_cons_of_mem x hr)) len, add_assoc]

lemma ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth (I : Ideal R)
    (M : ModuleCat.{v} R) (rs : List R) (reg : IsWeaklyRegular M rs)
    (h : ∀ r ∈ rs, r ∈ I) :
    I.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    I.depth M := by
  apply moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth _ M rs reg
  simpa [(Shrink.linearEquiv R (R ⧸ I)).annihilator_eq , Ideal.annihilator_quotient] using h

lemma depth_quotient_regular_sequence_add_length_eq_depth [IsLocalRing R]
    (M : ModuleCat.{v} R) (rs : List R)
    (reg : IsRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    IsLocalRing.depth M := by
  apply ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth _ M rs reg.toIsWeaklyRegular
  intro r hr
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  by_contra isu
  absurd reg.2
  simp [eq_top_of_isUnit_mem (ofList rs) (Ideal.subset_span hr) isu]

section ring

local instance (R : Type*) [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
    IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

lemma IsLocalRing.depth_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] (e : R ≃+* R') :
    IsLocalRing.depth (ModuleCat.of R R) = IsLocalRing.depth (ModuleCat.of R' R') := by
  let _ : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let _ : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let e' : R ≃ₛₗ[e.toRingHom] R' := {
    __ := e
    map_smul' a b := by simp }
  simp only [depth_eq_sSup_length_regular]
  congr!
  rename_i n
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · use rs.map e.toRingHom, (e'.isRegular_congr' rs).mp reg
    simpa [len]
  · use rs.map e.symm.toRingHom, (e'.symm.isRegular_congr' rs).mp reg
    simpa [len]

lemma IsLocalRing.depth_eq_of_algebraMap_surjective [IsLocalRing R] [IsNoetherianRing R]
    {S : Type u} [CommRing S] [IsLocalRing S] [Algebra R S] [Small.{v} S] [IsNoetherianRing S]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module S M]
    [IsScalarTower R S M] [Nontrivial M] (surj : Function.Surjective (algebraMap R S)) :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S M) := by
  have : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  have loc_hom : IsLocalHom (algebraMap R S) := surj.isLocalHom _
  simp only [depth_eq_sSup_length_regular]
  congr!
  rename_i n
  refine ⟨fun ⟨rs, reg, mem, len⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · have mem' : ∀ r ∈ rs.map (algebraMap R S), r ∈ maximalIdeal S := by
      intro r hr
      simp only [List.mem_map] at hr
      rcases hr with ⟨r', hr', eq⟩
      simpa [← eq] using mem r' hr'
    have reg' : IsRegular M (rs.map (algebraMap R S)) := by
      refine ⟨(isWeaklyRegular_map_algebraMap_iff S M rs).mpr reg.1, ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs.map (algebraMap R S), reg', mem'
    simpa
  · rcases List.map_surjective_iff.mpr surj rs with ⟨rs', hrs'⟩
    have mem' : ∀ r ∈ rs', r ∈ maximalIdeal R := by
      intro r hr
      have : algebraMap R S r ∈ maximalIdeal S := by
        apply mem
        simp only [← hrs', List.mem_map]
        use r
      simpa using this
    have reg' : IsRegular M rs' := by
      refine ⟨(isWeaklyRegular_map_algebraMap_iff S M rs').mp (by simpa [hrs'] using reg.1), ?_⟩
      apply (ne_top_of_le_ne_top (Ne.symm _) (Submodule.smul_mono_left (span_le.mpr mem'))).symm
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      exact IsLocalRing.maximalIdeal_le_jacobson _
    use rs', reg', mem'
    simpa [← hrs'] using len

omit [Small.{v, u} R] in
lemma IsLocalRing.depth_quotient_regular_succ_eq_depth [IsLocalRing R] [IsNoetherianRing R] (x : R)
    (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    letI : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
      have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
    IsLocalRing.depth (ModuleCat.of (R ⧸ x • (⊤ : Ideal R)) (R ⧸ x • (⊤ : Ideal R))) + 1 =
    IsLocalRing.depth (ModuleCat.of R R) := by
  have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
        Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
  have loc_hom : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
  rw [← IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth (ModuleCat.of R R) x reg mem, eq_comm]
  congr 1
  apply depth_eq_of_algebraMap_surjective _
  simpa only [Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective

end ring

end depth

section Ischbeck

lemma quotSMulTop_nontrivial [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_iff.mpr (Ne.symm _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

theorem moduleDepth_ge_depth_sub_dim [IsNoetherianRing R] [IsLocalRing R] (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Nfin : Module.Finite R N] [Nontrivial M] [Nntr : Nontrivial N]
    [Small.{v} R] : moduleDepth N M ≥ IsLocalRing.depth M -
    (Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N) := by
  generalize dim :
    ((Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N)).toNat = r
  induction r using Nat.strong_induction_on generalizing N
  rename_i r ihr
  by_cases eq0 : r = 0
  · by_cases eqtop : (Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N) = ⊤
    · simp [eqtop]
    · rw [← ENat.coe_toNat eqtop, dim]
      show moduleDepth N M ≥ IsLocalRing.depth M - r
      simp only [eq0, ENat.toNat_eq_zero, WithBot.unbot_eq_iff, WithBot.coe_zero, eqtop,
        or_false] at dim
      have smul_lt : (maximalIdeal R) • (⊤ : Submodule R M) < (⊤ : Submodule R M) :=
        Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M)))
      simp [eq0, IsLocalRing.depth, moduleDepth_eq_depth_of_supp_eq (maximalIdeal R) N M smul_lt
        (support_of_supportDim_eq_zero R N dim)]
  · let _ : NeZero r := ⟨eq0⟩
    have eqr (n : ℕ∞) : n.toNat = r → n = r := by simp
    refine (IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
      (motive := fun L ↦ (∀ (Lntr : Nontrivial L),
        (((Module.supportDim R L).unbot (Module.supportDim_ne_bot_of_nontrivial R L))).toNat = r →
        (moduleDepth (ModuleCat.of R L) M ≥ IsLocalRing.depth M -
        (Module.supportDim R L).unbot (Module.supportDim_ne_bot_of_nontrivial R L)))) R Nfin)
        ?_ ?_ ?_ Nntr dim
    · intro L _ _ _ Ltr Lntr
      absurd Ltr
      exact (not_subsingleton_iff_nontrivial.mpr Lntr)
    · intro L _ _ _ p e Lntr dim_eq
      rw [eqr _ dim_eq]
      obtain ⟨x, hx⟩ : ((maximalIdeal R : Set R) \ (p.asIdeal: Set R)).Nonempty  := by
        rw [Set.diff_nonempty]
        by_contra sub
        have := Ideal.IsMaximal.eq_of_le (maximalIdeal.isMaximal R) IsPrime.ne_top' sub
        have : Module.supportDim R (R ⧸ p.asIdeal) = 0 := by
          let _ : Field (R ⧸ maximalIdeal R) := Quotient.field (maximalIdeal R)
          rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, ← this,
            Ideal.annihilator_quotient, ringKrullDim_eq_zero_of_field]
        absurd eqr _ dim_eq
        simpa only [Module.supportDim_eq_of_equiv e, this, WithBot.unbot_zero,
          ← ENat.coe_zero, ENat.coe_inj, eq_comm] using eq0
      let S := (ModuleCat.of R L).smulShortComplex x
      have reg' : Function.Injective (x • (LinearMap.id (R := R) (M := L))) := by
        rw [← LinearMap.ker_eq_bot]
        ext l
        simp only [mem_ker, smul_apply, id_coe, id_eq, Submodule.mem_bot]
        refine ⟨fun h ↦ ?_, fun h ↦ smul_eq_zero_of_right x h⟩
        apply e.injective
        have : (Ideal.Quotient.mk p.asIdeal x) * e l = 0 := by
          have : (Ideal.Quotient.mk p.asIdeal x) * e l = x • e l := rfl
          rw [this, ← map_smul, h, map_zero]
        rcases mul_eq_zero.mp this with xzero|zero
        · absurd xzero
          exact Ideal.Quotient.eq_zero_iff_mem.not.mpr (Set.notMem_of_mem_diff hx)
        · rw [zero, map_zero]
      have reg : IsSMulRegular (ModuleCat.of R L) x := reg'
      have hS := reg.smulShortComplex_shortExact
      apply le_sSup
      intro i hi
      have : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x L)) M (i + 1)) := by
        have ntr : Nontrivial (QuotSMulTop x L) := quotSMulTop_nontrivial (Set.mem_of_mem_diff hx) L
        have dimlt' : (Module.supportDim R (QuotSMulTop x L)).unbot
          (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) < r := by
          have : (Module.supportDim R (QuotSMulTop x L)) + 1 ≤ Module.supportDim R L := by
            simp only [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
            rw [LinearEquiv.annihilator_eq e, Ideal.annihilator_quotient]
            have ple : p.1 ≤ Module.annihilator R (QuotSMulTop x L) := by
              rw [← p.1.annihilator_quotient, ← LinearEquiv.annihilator_eq e]
              exact (Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _)
            let f := Quotient.factor ple
            have mem_ann : x ∈ Module.annihilator R (QuotSMulTop x L) := by
              apply Module.mem_annihilator.mpr (fun l ↦ ?_)
              induction l using Submodule.Quotient.induction_on
              rename_i l
              simpa [← Submodule.Quotient.mk_smul] using
                Submodule.smul_mem_pointwise_smul l x ⊤ trivial
            have : Ideal.Quotient.mk p.asIdeal x ∈ nonZeroDivisors (R ⧸ p.asIdeal) := by
              simpa [Ideal.Quotient.eq_zero_iff_mem] using Set.notMem_of_mem_diff hx
            exact ringKrullDim_succ_le_of_surjective (Quotient.factor ple)
              (Quotient.factor_surjective ple) this
              (by simpa [Quotient.eq_zero_iff_mem] using mem_ann)
          have succle : (Module.supportDim R (QuotSMulTop x L)).unbot
            (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) + 1 ≤ r := by
            simpa [← eqr _ dim_eq, WithBot.le_unbot_iff] using this
          have : (Module.supportDim R (QuotSMulTop x L)).unbot
            (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) ≠ ⊤ := by
            by_contra h
            simp [h] at succle
          exact (ENat.add_one_le_iff this).mp succle
        have dimlt : ((Module.supportDim R (QuotSMulTop x L)).unbot
          (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L))).toNat < r := by
          rw [← ENat.coe_lt_coe, ENat.coe_toNat (ne_top_of_lt dimlt')]
          exact dimlt'
        apply ext_subsingleton_of_lt_moduleDepth
        refine lt_of_lt_of_le ?_ (ihr _ dimlt (ModuleCat.of R (QuotSMulTop x L)) rfl)
        rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt dimlt') with ⟨m, hm⟩
        by_cases eqtop : IsLocalRing.depth M = ⊤
        · simp only [Nat.cast_add, eqtop, ← hm, ENat.top_sub_coe, ENat.add_lt_top,
            ENat.coe_lt_top, true_and]
        · rcases ENat.ne_top_iff_exists.mp eqtop with ⟨k, hk⟩
          have : (i + 1 : ℕ) ≤ IsLocalRing.depth M - r := by
            simpa [ENat.add_one_le_iff (ENat.coe_ne_top i)] using hi
          apply lt_of_le_of_lt this
          have le : r ≤ k := by
            simp only [← hk, ← ENat.coe_sub, Nat.cast_lt] at hi
            omega
          simp only [← hk, ← ENat.coe_sub, ← hm, Nat.cast_lt]
          simp only [← hm, Nat.cast_lt] at dimlt'
          omega
      have zero : IsZero (AddCommGrpCat.of (Ext (ModuleCat.of R (QuotSMulTop x L)) M (i + 1))) :=
        @AddCommGrpCat.isZero_of_subsingleton _ this
      have epi' : Function.Surjective
        ⇑(x • LinearMap.id (R := R) (M := (Ext (of R L) M i))) := by
        convert (AddCommGrpCat.epi_iff_surjective _).mp <| ShortComplex.Exact.epi_f
          (Ext.contravariant_sequence_exact₁' hS M i (i + 1) (Nat.add_comm 1 i))
          (zero.eq_zero_of_tgt _)
        ext a
        simp only [smul_apply, id_coe, id_eq, smulShortComplex_X₂, smulShortComplex_X₁,
          smulShortComplex_f, AddCommGrpCat.hom_ofHom, Ext.bilinearComp_apply_apply]
        nth_rw 1 [← Ext.mk₀_id_comp a, ← Ext.smul_comp, ← Ext.mk₀_smul]
        congr
      have range : LinearMap.range (x • LinearMap.id) =
        x • (⊤ : Submodule R (Ext (of R L) M i)) := by
        ext y
        simp only [mem_range, smul_apply, id_coe, id_eq, Submodule.mem_smul_pointwise_iff_exists,
          Submodule.mem_top, true_and]
      by_contra ntr
      rw [not_subsingleton_iff_nontrivial] at ntr
      have mem : x ∈ (Module.annihilator R (Ext (of R L) M i)).jacobson :=
        IsLocalRing.maximalIdeal_le_jacobson _ (Set.mem_of_mem_diff hx)
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator mem
      nth_rw 1 [← LinearMap.range_eq_top_of_surjective _ epi', ← range]
    · intro L1 _ _ _ L2 _ _ _ L3 _ _ _ f g inj surj exac ih1' ih3' L2ntr dim_eq
      rw [eqr _ dim_eq]
      by_cases ntr : Nontrivial L1 ∧ Nontrivial L3
      · let _ := ntr.1
        let _ := ntr.2
        have dimle1' : ((Module.supportDim R L1).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L1)) ≤ r := by
          rw [← (eqr _ dim_eq), ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
          exact Module.supportDim_le_of_injective f inj
        have dimle3' : ((Module.supportDim R L3).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L3)) ≤ r := by
          rw [← (eqr _ dim_eq), ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
          exact Module.supportDim_le_of_surjective g surj
        have ge1 : moduleDepth (of R L1) M ≥ IsLocalRing.depth M - ((Module.supportDim R L1).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L1)) := by
          rcases lt_or_eq_of_le (ENat.toNat_le_of_le_coe dimle1') with lt|eq
          · exact ihr _ lt (ModuleCat.of.{v} R L1) rfl
          · exact ih1' ntr.1 eq
        have ge3 : moduleDepth (of R L3) M ≥ IsLocalRing.depth M - ((Module.supportDim R L3).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L3)) := by
          rcases lt_or_eq_of_le (ENat.toNat_le_of_le_coe dimle3') with lt|eq
          · exact ihr _ lt (ModuleCat.of.{v} R L3) rfl
          · exact ih3' ntr.2 eq
        let S : ShortComplex (ModuleCat.{v} R) := {
          f := ModuleCat.ofHom f
          g := ModuleCat.ofHom g
          zero := by
            ext
            simp [exac.apply_apply_eq_zero] }
        have hS : S.ShortExact := {
          exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr exac
          mono_f := (ModuleCat.mono_iff_injective S.f).mpr inj
          epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surj }
        exact ge_trans (moduleDepth_ge_min_of_shortExact S hS M) (le_inf_iff.mpr
          ⟨le_trans (tsub_le_tsub_left dimle1' _) ge1, le_trans (tsub_le_tsub_left dimle3' _) ge3⟩)
      · have : Subsingleton L1 ∨ Subsingleton L3 := by
          simpa [← not_nontrivial_iff_subsingleton] using Classical.not_and_iff_not_or_not.mp ntr
        rcases this with sub1|sub3
        · have : Function.Injective g := by
            rw [← ker_eq_bot, exact_iff.mp exac, range_eq_bot, Subsingleton.eq_zero f]
          let eg : L2 ≃ₗ[R] L3 := LinearEquiv.ofBijective g ⟨this, surj⟩
          let L3ntr : Nontrivial L3 := Function.Injective.nontrivial this
          have dimeq3 : (((Module.supportDim R L3).unbot
            (Module.supportDim_ne_bot_of_nontrivial R L3))).toNat = r := by
            rw [← dim_eq]
            congr 2
            exact (Module.supportDim_eq_of_equiv eg).symm
          rw [moduleDepth_eq_of_iso_fst M eg.toModuleIso, ← eqr _ dimeq3]
          exact ih3' L3ntr dimeq3
        · have : Function.Surjective f := by
            rw [← range_eq_top, ← exact_iff.mp exac, ker_eq_top, Subsingleton.eq_zero g]
          let ef : L1 ≃ₗ[R] L2 := LinearEquiv.ofBijective f ⟨inj, this⟩
          let L1ntr : Nontrivial L1 := Function.Surjective.nontrivial this
          have dimeq1 : (((Module.supportDim R L1).unbot
            (Module.supportDim_ne_bot_of_nontrivial R L1))).toNat = r := by
            rw [← dim_eq]
            congr 2
            exact Module.supportDim_eq_of_equiv ef
          rw [← moduleDepth_eq_of_iso_fst M ef.toModuleIso, ← eqr _ dimeq1]
          exact ih1' L1ntr dimeq1

lemma quotient_prime_ringKrullDim_ne_bot {P : Ideal R} (prime : P.IsPrime) :
    ringKrullDim (R ⧸ P) ≠ ⊥ :=
  ne_bot_of_le_ne_bot WithBot.zero_ne_bot
    (@ringKrullDim_nonneg_of_nontrivial _ _ (Quotient.nontrivial_iff.mpr prime.ne_top'))

theorem depth_le_ringKrullDim_associatedPrime [IsNoetherianRing R] [IsLocalRing R]
    [Small.{v} R] (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] (P : Ideal R)
    (ass : P ∈ associatedPrimes R M) : IsLocalRing.depth M ≤ (ringKrullDim (R ⧸ P)).unbot
      (quotient_prime_ringKrullDim_ne_bot ass.1) := by
  let _ := Quotient.nontrivial_iff.mpr ass.1.ne_top'
  have dep0 : moduleDepth (of R (Shrink.{v} (R ⧸ P))) M = 0 := by
    rw [moduleDepth_eq_zero_of_hom_nontrivial,
      (LinearEquiv.congrLeft M R (Shrink.linearEquiv R (R ⧸ P))).nontrivial_congr]
    rcases ((isAssociatedPrime_iff_exists_injective_linearMap P M).mp
      (AssociatePrimes.mem_iff.mp ass)).2 with ⟨f, hf⟩
    exact nontrivial_of_ne f 0 (ne_zero_of_injective hf)
  have := moduleDepth_ge_depth_sub_dim M (ModuleCat.of R (Shrink.{v} (R ⧸ P)))
  simp only [dep0, ge_iff_le, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at this
  convert this
  rw [← Module.supportDim_quotient_eq_ringKrullDim,
    Module.supportDim_eq_of_equiv (Shrink.linearEquiv R (R ⧸ P))]

theorem depth_le_supportDim [IsNoetherianRing R] [IsLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≤ Module.supportDim R M := by
  rcases associatedPrimes.nonempty R M with ⟨p, hp⟩
  have := depth_le_ringKrullDim_associatedPrime M p hp
  rw [← WithBot.coe_le_coe, WithBot.coe_unbot] at this
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact this.trans (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
    (le_of_eq_of_le Submodule.annihilator_top.symm hp.annihilator_le)))

theorem depth_le_ringKrullDim [IsNoetherianRing R] [IsLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≤ ringKrullDim R :=
  (depth_le_supportDim M).trans (Module.supportDim_le_ringKrullDim R M)

theorem depth_ne_top [IsNoetherianRing R] [IsLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≠ ⊤ := by
  have := lt_of_le_of_lt (depth_le_ringKrullDim M) ringKrullDim_lt_top
  simp only [← WithBot.coe_top, WithBot.coe_lt_coe] at this
  exact this.ne_top

end Ischbeck

section CMdef

universe u' v'

/-- A `R`-module `M` is Cohen Macaulay if it is zero or
`Module.supportDim R M = IsLocalRing.depth M`. -/
class ModuleCat.IsCohenMacaulay [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M

lemma ModuleCat.isCohenMacaulay_iff [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) :
    M.IsCohenMacaulay ↔ Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma ModuleCat.depth_eq_supportDim_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay] [ntr : Nontrivial M] :
    Module.supportDim R M = IsLocalRing.depth M := by
  have : ¬ Subsingleton M := not_subsingleton_iff_nontrivial.mpr ntr
  have := M.isCohenMacaulay_iff.mp cm
  tauto

lemma ModuleCat.depth_eq_supportDim_unbot_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay] [ntr : Nontrivial M] :
    (Module.supportDim R M).unbot
    (Module.supportDim_ne_bot_of_nontrivial R M) = IsLocalRing.depth M := by
  simp [M.depth_eq_supportDim_of_cohenMacaulay]

lemma ModuleCat.IsCohenMacaulay_of_iso [IsLocalRing R] [Small.{v} R] {M M' : ModuleCat.{v} R}
    (e : M ≅ M') [M.IsCohenMacaulay] : M'.IsCohenMacaulay := by
  rw [M'.isCohenMacaulay_iff]
  by_cases ntr : Nontrivial M
  · right
    rw [← IsLocalRing.depth_eq_of_iso e, ← Module.supportDim_eq_of_equiv e.toLinearEquiv,
      M.depth_eq_supportDim_of_cohenMacaulay]
  · simp [← e.toLinearEquiv.subsingleton_congr, not_nontrivial_iff_subsingleton.mp ntr]

section IsLocalization

variable [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [Small.{v} R]

lemma depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M]
    (mem : p ∈ associatedPrimes R M) :
    IsLocalRing.depth M = (ringKrullDim (R ⧸ p)).unbot
    (quotient_prime_ringKrullDim_ne_bot mem.1) := by
  apply le_antisymm (depth_le_ringKrullDim_associatedPrime M p mem)
  rw [← M.depth_eq_supportDim_unbot_of_cohenMacaulay]
  rw [← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
    (le_of_eq_of_le Submodule.annihilator_top.symm (AssociatePrimes.mem_iff.mp mem).annihilator_le))

lemma associated_prime_minimal_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M]
    (mem : p ∈ associatedPrimes R M) : p ∈ (Module.annihilator R M).minimalPrimes := by
  have eq := Eq.trans M.depth_eq_supportDim_unbot_of_cohenMacaulay
    (depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay p M mem)
  rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_unbot, ringKrullDim_quotient,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator, ringKrullDim_quotient] at eq
  have : p.IsPrime := mem.1
  have ann_le : Module.annihilator R M ≤ p := (le_of_eq_of_le Submodule.annihilator_top.symm
    (AssociatePrimes.mem_iff.mp mem).annihilator_le)
  rcases Ideal.exists_minimalPrimes_le ann_le with ⟨p', hp', le⟩
  rcases lt_or_eq_of_le le with lt|eq
  · classical
    let f : WithBot (PrimeSpectrum.zeroLocus (p : Set R)) →
        (PrimeSpectrum.zeroLocus ((Module.annihilator R M) : Set R)) := fun I ↦ by
        by_cases eqbot : I = ⊥
        · exact ⟨⟨p', Ideal.minimalPrimes_isPrime hp'⟩, hp'.1.2⟩
        · exact ⟨(I.unbot eqbot).1, PrimeSpectrum.zeroLocus_anti_mono ann_le (I.unbot eqbot).2⟩
    have f_mono : StrictMono f := by
      intro a b alt
      by_cases eqbot : a = ⊥
      · simp only [eqbot, ↓reduceDIte, alt.ne_bot, Subtype.mk_lt_mk, f]
        apply lt_of_lt_of_le lt (b.unbot alt.ne_bot).2
      · simp only [eqbot, ↓reduceDIte, alt.ne_bot, Subtype.mk_lt_mk, Subtype.coe_lt_coe, f]
        rw [← WithBot.coe_lt_coe, WithBot.coe_unbot, WithBot.coe_unbot]
        exact alt
    have dim_le := Order.krullDim_le_of_strictMono f f_mono
    have : Nonempty (PrimeSpectrum.zeroLocus (p : Set R)) := Nonempty.intro ⟨⟨p, mem.1⟩, le_refl p⟩
    rw [Order.krullDim_withBot, eq, ← ringKrullDim_quotient] at dim_le
    have nebot : ringKrullDim (R ⧸ p) ≠ ⊥ := quotient_prime_ringKrullDim_ne_bot mem.1
    have netop : (ringKrullDim (R ⧸ p)).unbot nebot ≠ ⊤ := by
      have : FiniteRingKrullDim R := instFiniteRingKrullDimOfIsNoetherianRingOfIsLocalRing
      have : ringKrullDim (R ⧸ p) ≠ ⊤ :=
        ne_top_of_le_ne_top ringKrullDim_ne_top
         (ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) (Ideal.Quotient.mk_surjective))
      simpa [← WithBot.coe_inj.not]
    rcases ENat.ne_top_iff_exists.mp netop with ⟨m, hm⟩
    have : (ringKrullDim (R ⧸ p)).unbot nebot + 1 ≤ (ringKrullDim (R ⧸ p)).unbot nebot := by
      rw [← WithBot.coe_le_coe]
      simpa using dim_le
    absurd this
    rw [← hm, not_le, ← ENat.coe_one, ← ENat.coe_add, ENat.coe_lt_coe]
    exact lt_add_one m
  · simpa [← eq] using hp'

lemma associated_prime_eq_minimalPrimes_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M] :
    associatedPrimes R M = (Module.annihilator R M).minimalPrimes :=
  le_antisymm (fun p hp ↦ associated_prime_minimal_of_isCohenMacaulay p M hp)
    (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M)

lemma quotSMulTop_isCohenMacaulay_iff_isCohenMacaulay (M : ModuleCat.{v} R) [Module.Finite R M]
    (r : R) (reg : IsSMulRegular M r) (mem : r ∈ maximalIdeal R) :
     M.IsCohenMacaulay ↔ (ModuleCat.of R (QuotSMulTop r M)).IsCohenMacaulay := by
  simp only [ModuleCat.isCohenMacaulay_iff]
  by_cases ntr : Subsingleton M
  · have : Subsingleton (QuotSMulTop r M) := Function.Surjective.subsingleton
      (Submodule.mkQ_surjective _)
    simp [ntr, this]
  · have ntr1 : Nontrivial M := not_subsingleton_iff_nontrivial.mp ntr
    have ntr2 : Nontrivial (QuotSMulTop r M) := quotSMulTop_nontrivial mem M
    simp [not_subsingleton_iff_nontrivial.mpr ntr2, false_or, ntr,
      ← Module.supportDim_quotSMulTop_succ_eq_supportDim reg mem,
      ← IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth M r reg mem, WithBot.add_one_cancel]

lemma quotient_regular_isCohenMacaulay_iff_isCohenMacaulay
    (M : ModuleCat.{v} R) [Module.Finite R M] (rs : List R) (reg : IsRegular M rs) :
    M.IsCohenMacaulay ↔
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))).IsCohenMacaulay := by
  have ntr2 : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
    (IsRegular.quot_ofList_smul_nontrivial reg ⊤)
  have ntr1 : Nontrivial M := Function.Surjective.nontrivial (Submodule.mkQ_surjective
    (Ideal.ofList rs • (⊤ : Submodule R M)))
  simp only [isCohenMacaulay_iff, ← not_nontrivial_iff_subsingleton, ntr1, not_true_eq_false,
    false_or, ntr2]
  rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular rs reg,
    ← depth_quotient_regular_sequence_add_length_eq_depth M rs reg, WithBot.coe_add]
  exact WithBot.add_natCast_cancel

variable [p.IsPrime] {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]

/-- Turn a `R`-linear map into `algebraMap R A`-semilinear map if its target is an `A`-module. -/
abbrev SemiLinearMapAlgebraMapOfLinearMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R A] N where
  __ := f
  map_smul' m r := by simp

/-- Turn a `algebraMap R A`-semilinear map into a `R`-linear map. -/
abbrev LinearMapOfSemiLinearMapAlgebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₛₗ[algebraMap R A] N) : M →ₗ[R] N where
  __ := f
  map_smul' m r := by simp

variable (Rₚ) in
/-- Given `R`-algebra `Rₚ`, `R`-module `M` and `Rₚ`-module `Mₚ` and `f : M →ₗ[R] Mₚ`,
The linear map `QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ` lifted from `f`. -/
abbrev quotSMulTop_isLocalizedModule_map (x : R) (M : Type*) [AddCommGroup M] [Module R M]
    (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) :
    QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ :=
  LinearMapOfSemiLinearMapAlgebraMap (Submodule.mapQ _ _
    (SemiLinearMapAlgebraMapOfLinearMap f)
    (fun m hm ↦ by
      rw [← Submodule.ideal_span_singleton_smul] at hm
      simp only [Submodule.mem_comap, LinearMap.coe_mk, LinearMap.coe_toAddHom]
      refine Submodule.smul_induction_on hm (fun r hr m hm ↦ ?_)
        (fun m1 m2 hm1 hm2 ↦ by simpa using Submodule.add_mem _ hm1 hm2)
      rcases Ideal.mem_span_singleton'.mp hr with ⟨r', hr'⟩
      simpa only [← hr', map_smul, mul_comm r' x, ← smul_smul,
        algebra_compatible_smul Rₚ x (r' • f m)]
        using Submodule.smul_mem_pointwise_smul (r' • f m) ((algebraMap R Rₚ) x) ⊤ hm))

variable (Rₚ) in
omit [IsLocalRing R] [IsNoetherianRing R] [Small.{v, u} R] in
lemma isLocalizedModule_quotSMulTop_isLocalizedModule_map (x : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    IsLocalizedModule.AtPrime p (quotSMulTop_isLocalizedModule_map Rₚ x M Mₚ f) where
  map_units r := by
    let alg := (Algebra.algHom R Rₚ (Module.End Rₚ (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ)))
    rcases isUnit_iff_exists.mp (IsUnit.algebraMap_of_algebraMap (r := r.1) alg.toLinearMap
      (map_one alg) (IsLocalization.map_units Rₚ r)) with ⟨s, hs1, hs2⟩
    exact isUnit_iff_exists.mpr ⟨LinearMap.restrictScalars R s,
      ⟨LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs1 (Eq.refl x)),
        LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs2 (Eq.refl x))⟩⟩
  surj y := by
    induction y using Submodule.Quotient.induction_on
    rename_i y
    rcases IsLocalizedModule.surj (S := p.primeCompl) (f := f) y with ⟨z, hz⟩
    use (Submodule.Quotient.mk z.1, z.2)
    simp [← hz]
  exists_of_eq {y1 y2} h := by
    induction y1 using Submodule.Quotient.induction_on
    induction y2 using Submodule.Quotient.induction_on
    rename_i y1 y2
    simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, Submodule.mapQ_apply] at h
    have h := (Submodule.Quotient.mk_eq_zero _).mp (sub_eq_zero_of_eq h)
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨m, _, hm⟩
    rcases IsLocalizedModule.surj p.primeCompl f m with ⟨⟨z, s⟩, hz⟩
    have eq : f (s • (y1 - y2)) = f (x • z) := by simp [← hm, ← hz, smul_comm s x m]
    rcases IsLocalizedModule.exists_of_eq (S := p.primeCompl) eq with ⟨c, hc⟩
    use c * s
    apply sub_eq_zero.mp
    have h : (0 : QuotSMulTop x M) = Submodule.Quotient.mk (c • s • (y1 - y2)) := by
      simpa [hc] using (smul_eq_zero_of_right c <| (Submodule.Quotient.mk_eq_zero _).mpr <|
        Submodule.smul_mem_pointwise_smul z x ⊤ Submodule.mem_top).symm
    simp [h, smul_sub, mul_smul]

variable [Small.{v'} Rₚ] [IsNoetherianRing Rₚ]
  (M : ModuleCat.{v} R) (Mₚ : ModuleCat.{v'} Rₚ) [Module R Mₚ] [IsScalarTower R Rₚ Mₚ]
  (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]

include p f

lemma isLocalization_at_prime_prime_depth_le_depth [IsLocalRing Rₚ] [Module.Finite R M]
    [ntr : Nontrivial Mₚ] : p.depth M ≤ IsLocalRing.depth Mₚ := by
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  have : Nontrivial M := by
    by_contra h
    absurd not_subsingleton_iff_nontrivial.mpr ntr
    rw [IsLocalizedModule.subsingleton_iff_ker_eq_top p.primeCompl f]
    have := (Submodule.subsingleton_iff R).mpr (not_nontrivial_iff_subsingleton.mp h)
    apply Subsingleton.elim
  simp only [IsLocalRing.depth_eq_sSup_length_regular, Ideal.depth]
  have smul_lt : p • (⊤ : Submodule R M) < ⊤ :=
    Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      ((IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top')).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)))
  have h_supp : Module.support R (of R (Shrink.{v, u} (R ⧸ p))) = PrimeSpectrum.zeroLocus p := by
    rw [(Shrink.linearEquiv R (R ⧸ p)).support_eq, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient]
  rw [moduleDepth_eq_sSup_length_regular p _ _ smul_lt h_supp]
  apply sSup_le (fun n hn ↦ le_sSup ?_)
  rcases hn with ⟨rs, reg, mem, len⟩
  refine ⟨rs.map (algebraMap R Rₚ), reg.isRegular_of_isLocalizedModule_of_mem Rₚ p f mem,
    fun _ hr ↦ ?_, by simpa using len⟩
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p] using mem r hr

omit [Small.{v', u'} Rₚ] in
lemma isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay
    [Module.Finite R M] [M.IsCohenMacaulay] [ntr : Nontrivial Mₚ] :
    Module.supportDim Rₚ Mₚ = p.depth M := by
  have : IsLocalRing Rₚ := IsLocalization.AtPrime.isLocalRing Rₚ p
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  have : Nontrivial M := by
    by_contra h
    absurd not_subsingleton_iff_nontrivial.mpr ntr
    rw [IsLocalizedModule.subsingleton_iff_ker_eq_top p.primeCompl f]
    have := (Submodule.subsingleton_iff R).mpr (not_nontrivial_iff_subsingleton.mp h)
    apply Subsingleton.elim
  have : p.depth M ≠ ⊤ :=
    ne_top_of_le_ne_top (depth_ne_top M) (ideal_depth_le_depth p Ideal.IsPrime.ne_top' M)
  rcases ENat.ne_top_iff_exists.mp this with ⟨n, hn⟩
  induction n generalizing M Mₚ
  · simp only [← hn, CharP.cast_eq_zero, WithBot.coe_zero]
    have min : p ∈ (Module.annihilator R M).minimalPrimes := by
      simp only [CharP.cast_eq_zero, Ideal.depth] at hn
      rw [Eq.comm, moduleDepth_eq_zero_of_hom_nontrivial,
        ((Shrink.linearEquiv R (R ⧸ p)).congrLeft M R).nontrivial_congr] at hn
      obtain ⟨g, hg⟩ : ∃ g : R ⧸ p →ₗ[R] M, g ≠ 0 := exists_ne 0
      have : g 1 ≠ 0 := by
        by_contra eq0
        absurd hg
        apply LinearMap.ext (fun r ↦ ?_)
        induction r using Submodule.Quotient.induction_on
        rename_i r
        nth_rw 1 [← mul_one r, ← smul_eq_mul, Submodule.Quotient.mk_smul, map_smul]
        simp [eq0]
      have le : p ≤ LinearMap.ker (LinearMap.toSpanSingleton R M (g 1)) := by
        intro r hr
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul,
          ← map_one (Ideal.Quotient.mk p), ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul]
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      rcases exists_le_isAssociatedPrime_of_isNoetherianRing R (g 1) this with ⟨p', ass, hp'⟩
      let P : PrimeSpectrum R := ⟨p, ‹_›⟩
      have ntr : Nontrivial (LocalizedModule P.1.primeCompl M) :=
        (IsLocalizedModule.linearEquiv p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl M) f).nontrivial
      have mem_supp := Module.mem_support_iff.mpr ntr
      simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus,
        SetLike.coe_subset_coe, P] at mem_supp
      have min := associated_prime_minimal_of_isCohenMacaulay p' M ass
      convert min
      simp only [Ideal.minimalPrimes, Set.mem_setOf_eq] at min
      apply min.eq_of_le ⟨‹_›, mem_supp⟩ (le.trans (le_of_eq_of_le _ hp'))
      rw [Submodule.bot_colon', Submodule.annihilator_span_singleton (g 1)]
    have : Module.support Rₚ Mₚ = {closedPoint Rₚ} := by
      apply le_antisymm
      · intro I hI
        simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus,
          SetLike.coe_subset_coe] at hI
        have le : (Module.annihilator R M).map (algebraMap R Rₚ) ≤ Module.annihilator Rₚ Mₚ := by
          apply Ideal.map_le_iff_le_comap.mpr (fun r hr ↦ ?_)
          simp only [Ideal.mem_comap, Module.mem_annihilator, algebraMap_smul]
          intro m
          rcases (IsLocalizedModule.mk'_surjective p.primeCompl f) m with ⟨⟨l, s⟩, h⟩
          simp [← h, Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul,
            Module.mem_annihilator.mp hr l]
        have : maximalIdeal Rₚ ∈
          ((Module.annihilator R M).map (algebraMap R Rₚ)).minimalPrimes := by
          simpa [IsLocalization.minimalPrimes_map p.primeCompl,
            IsLocalization.AtPrime.comap_maximalIdeal Rₚ p] using min
        simp only [Ideal.minimalPrimes, Set.mem_setOf_eq] at this
        exact PrimeSpectrum.ext (this.eq_of_le ⟨I.2, le.trans hI⟩ (le_maximalIdeal_of_isPrime I.1))
      · simpa using IsLocalRing.closedPoint_mem_support Rₚ Mₚ
    have : Unique (Module.support Rₚ Mₚ) := by simpa [this] using Set.uniqueSingleton _
    exact Order.krullDim_eq_zero_of_unique
  · rename_i n ih _ _ _ _ _ _ _
    have : Subsingleton ((ModuleCat.of R (Shrink.{v} (R ⧸ p))) →ₗ[R] M) := by
      by_contra ntr
      rw [not_subsingleton_iff_nontrivial, ← moduleDepth_eq_zero_of_hom_nontrivial] at ntr
      simp [Ideal.depth, ntr] at hn
    rcases IsSMulRegular.subsingleton_linearMap_iff.mp
      (((Shrink.linearEquiv R (R ⧸ p)).congrLeft M R).symm.subsingleton) with ⟨a, mem, reg⟩
    rw [Ideal.annihilator_quotient] at mem
    let M' := ModuleCat.of R (QuotSMulTop a M)
    have : Nontrivial M' := quotSMulTop_nontrivial (le_maximalIdeal_of_isPrime p mem) M
    have : M'.IsCohenMacaulay := (quotSMulTop_isCohenMacaulay_iff_isCohenMacaulay M a reg
      (le_maximalIdeal_of_isPrime p mem)).mp ‹_›
    have netop' : p.depth M' ≠ ⊤ :=
      ne_top_of_le_ne_top (depth_ne_top M') (ideal_depth_le_depth p Ideal.IsPrime.ne_top' M')
    have depth_eq : p.depth M'= n := by
      simp only [Nat.cast_add, ← p.depth_quotSMulTop_succ_eq_moduleDepth M a reg mem] at hn
      exact (WithTop.add_right_inj (ENat.coe_ne_top 1)).mp hn.symm
    let M'ₚ := ModuleCat.of Rₚ (QuotSMulTop ((algebraMap R Rₚ) a) Mₚ)
    have map_mem : (algebraMap R Rₚ) a ∈ maximalIdeal Rₚ :=
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p a _).mpr mem)
    have : Nontrivial M'ₚ := quotSMulTop_nontrivial map_mem Mₚ
    have eq_succ : Module.supportDim Rₚ M'ₚ + 1 = Module.supportDim Rₚ Mₚ :=
      Module.supportDim_quotSMulTop_succ_eq_supportDim
        (reg.of_isLocalizedModule Rₚ p.primeCompl f) map_mem
    have := isLocalizedModule_quotSMulTop_isLocalizedModule_map p Rₚ a M Mₚ f
    simp [← eq_succ, ← hn, depth_eq, ih M' M'ₚ (quotSMulTop_isLocalizedModule_map Rₚ a M Mₚ f)
      inferInstance ‹_› netop' depth_eq.symm]

lemma isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay [IsLocalRing Rₚ] [Module.Finite R M]
    [M.IsCohenMacaulay] : Mₚ.IsCohenMacaulay := by
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  simp only [ModuleCat.isCohenMacaulay_iff]
  by_cases ntr : Subsingleton Mₚ
  · simp [ntr]
  · simp only [ntr, false_or]
    have ntr2 : Nontrivial Mₚ := not_subsingleton_iff_nontrivial.mp ntr
    apply le_antisymm _ (depth_le_supportDim Mₚ)
    rw [isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay p M Mₚ f]
    exact WithBot.coe_le_coe.mpr (isLocalization_at_prime_prime_depth_le_depth p M Mₚ f)

lemma isLocalize_at_prime_depth_eq_of_isCohenMacaulay [IsLocalRing Rₚ] [Module.Finite R M]
    [Nontrivial Mₚ] [M.IsCohenMacaulay] :
    p.depth M = IsLocalRing.depth Mₚ := by
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  apply le_antisymm (isLocalization_at_prime_prime_depth_le_depth p M Mₚ f)
  rw [← WithBot.coe_le_coe, ← isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay p M Mₚ f]
  exact (depth_le_supportDim Mₚ)

end IsLocalization

variable (R)

/-- A local ring is Cohen Macaulay if `ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)`. -/
class IsCohenMacaulayLocalRing : Prop extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

lemma isCohenMacaulayLocalRing_def [IsLocalRing R] : IsCohenMacaulayLocalRing R ↔
    ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isCohenMacaulayLocalRing_of_ringKrullDim_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (le : ringKrullDim R ≤ IsLocalRing.depth (ModuleCat.of R R)) : IsCohenMacaulayLocalRing R :=
  (isCohenMacaulayLocalRing_def _).mpr (le_antisymm le (depth_le_ringKrullDim _))

--may be able to remove noetherian condition here by modify `IsLocalRing.depth_eq_of_ringEquiv`
lemma isCohenMacaulayLocalRing_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsNoetherianRing R] (e : R ≃+* R') [CM : IsCohenMacaulayLocalRing R] :
    IsCohenMacaulayLocalRing R' := by
  have := e.isLocalRing
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R e
  simp only [isCohenMacaulayLocalRing_def] at CM ⊢
  rw [← ringKrullDim_eq_of_ringEquiv e, ← IsLocalRing.depth_eq_of_ringEquiv e, CM]

lemma isCohenMacaulayLocalRing_iff [IsLocalRing R] :
    IsCohenMacaulayLocalRing R ↔ (ModuleCat.of R R).IsCohenMacaulay := by
  simp [isCohenMacaulayLocalRing_def, isCohenMacaulay_iff,
    not_subsingleton_iff_nontrivial.mpr inferInstance, Module.supportDim_self_eq_ringKrullDim]

/-- A commutative ring is Cohen Macaulay if its localization at every prime
`IsCohenMacaulayLocalRing`. -/
class IsCohenMacaulayRing : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p)

lemma isCohenMacaulayRing_def : IsCohenMacaulayRing R ↔
    ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isCohenMacaulayRing_def' : IsCohenMacaulayRing R ↔
  ∀ p : PrimeSpectrum R, IsCohenMacaulayLocalRing (Localization.AtPrime p.1) :=
  ⟨fun ⟨h⟩ ↦ fun p ↦ h p.1 p.2, fun h ↦ ⟨fun p hp ↦ h ⟨p, hp⟩⟩⟩

lemma isCohenMacaulayRing_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsNoetherianRing R] (e : R ≃+* R') [CM : IsCohenMacaulayRing R] :
    IsCohenMacaulayRing R' := by
  apply (isCohenMacaulayRing_def R').mpr (fun p' hp' ↦ ?_)
  let p := p'.comap e
  have : Submonoid.map e.toMonoidHom p.primeCompl = p'.primeCompl := by
    ext x
    have : (∃ y, e y ∉ p' ∧ e y = x) ↔ x ∉ p' := ⟨fun ⟨y, hy, eq⟩ ↦ by simpa [← eq],
      fun h ↦ ⟨e.symm x, by simpa, RingEquiv.apply_symm_apply e x⟩⟩
    simpa only [Ideal.primeCompl, p]
  let _ := (isCohenMacaulayRing_def R).mp ‹_› p (Ideal.comap_isPrime e p')
  exact isCohenMacaulayLocalRing_of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime p') e this)

lemma quotient_regular_smul_top_isCohenMacaulay_iff_isCohenMacaulay [IsLocalRing R]
    [IsNoetherianRing R] (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    IsCohenMacaulayLocalRing R ↔ IsCohenMacaulayLocalRing (R ⧸ x • (⊤ : Ideal R)) := by
  have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
      Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
  have : ringKrullDim R = ringKrullDim (R ⧸ x • (⊤ : Ideal R)) + 1 := by
    rw [← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
    exact (Module.supportDim_quotSMulTop_succ_eq_supportDim reg mem).symm
  simp [isCohenMacaulayLocalRing_def, this, ← depth_quotient_regular_succ_eq_depth x reg mem,
    WithBot.add_one_cancel]

end CMdef

section CMcat

lemma Ideal.ofList_spanFinrank_le_length (rs : List R) :
  Submodule.spanFinrank (ofList rs) ≤ rs.length := by
  classical
  simp only [Ideal.ofList, ← List.coe_toFinset]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet rs.toFinset))
  rw [Set.ncard_coe_finset]
  apply List.toFinset_card_le

variable [IsNoetherianRing R]

lemma Ideal.ofList_height_le_length (rs : List R) (h : Ideal.ofList rs ≠ ⊤) :
    (Ideal.ofList rs).height ≤ rs.length := by
  apply le_trans (Ideal.height_le_spanFinrank _ h)
  exact (Nat.cast_le.mpr (ofList_spanFinrank_le_length rs))

lemma IsLocalRing.Ideal.ofList_height_le_length' [IsLocalRing R] (rs : List R)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) : (Ideal.ofList rs).height ≤ rs.length :=
  Ideal.ofList_height_le_length rs (lt_of_le_of_lt (span_le.mpr mem) IsPrime.ne_top'.lt_top).ne_top

lemma Ideal.ofList_height_eq_length_of_isWeaklyRegular (rs : List R) (reg : IsWeaklyRegular R rs)
    (h : Ideal.ofList rs ≠ ⊤) : (Ideal.ofList rs).height = rs.length := by
  apply le_antisymm (Ideal.ofList_height_le_length rs h)
  generalize len : rs.length = n
  induction n generalizing rs
  · simp
  · rename_i n hn
    simp only [Nat.cast_add, Nat.cast_one, height, le_iInf_iff]
    intro p hp
    let _ := hp.1.1
    have : Ideal.ofList (rs.take n) ≤ p :=
      le_trans (Ideal.span_mono (fun r hr ↦ List.mem_of_mem_take hr)) hp.1.2
    rcases Ideal.exists_minimalPrimes_le this with ⟨q, hq, lep⟩
    have len' : (List.take n rs).length = n := by simp [len]
    have reg' : IsWeaklyRegular R (List.take n rs) := by
      apply (isWeaklyRegular_iff R (List.take n rs)).mpr fun i hi ↦ ?_
      have : (rs.take n).take i  = rs.take i := by
        rw [len'] at hi
        simp [List.take_take, le_of_lt hi]
      rw [List.getElem_take, this]
      exact reg.1 i (lt_of_lt_of_le hi (rs.length_take_le' n))
    let _ := hq.1.1
    have le := le_trans (hn (rs.take n) reg' (ne_top_of_le_ne_top h (Ideal.span_mono
      (fun r hr ↦ List.mem_of_mem_take hr))) len') (Ideal.height_mono hq.1.2)
    rw [Ideal.height_eq_primeHeight] at le
    apply le_trans (add_le_add_left le 1) (Ideal.primeHeight_add_one_le_of_lt (lep.lt_of_ne _))
    by_contra eq
    have p_min : p ∈ (Module.annihilator R
      (R ⧸ Ideal.ofList (rs.take n) • (⊤ : Ideal R))).minimalPrimes := by
      simpa [← eq, Ideal.annihilator_quotient] using hq
    absurd IsSMulRegular.notMem_of_mem_minimalPrimes (reg.1 n (by simp [len])) p_min
    apply hp.1.2 (Ideal.subset_span _)
    simp

lemma Ideal.ofList_height_eq_length_of_isWeaklyRegular' [IsLocalRing R] (rs : List R)
    (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (Ideal.ofList rs).height = rs.length :=
  Ideal.ofList_height_eq_length_of_isWeaklyRegular rs reg
    (lt_of_le_of_lt (span_le.mpr mem) IsPrime.ne_top'.lt_top).ne_top

omit [IsNoetherianRing R] in
lemma IsLocalRing.height_eq_height_maximalIdeal_of_maximalIdeal_mem_minimalPrimes [IsLocalRing R]
    (I : Ideal R) (mem : maximalIdeal R ∈ I.minimalPrimes) :
    I.height = (maximalIdeal R).height := by
  rw [Ideal.height_eq_primeHeight (maximalIdeal R)]
  have : I.minimalPrimes = {maximalIdeal R} := by
    ext J
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simp [Minimal.eq_of_le mem.out ⟨h.1.1, h.1.2⟩ (IsLocalRing.le_maximalIdeal h.1.1.ne_top)]
    · simpa [Set.mem_singleton_iff.mp h] using mem
  simp [Ideal.height, this]

lemma maximalIdeal_mem_ofList_append_minimalPrimes_of_ofList_height_eq_length [IsLocalRing R]
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) (ht : (Ideal.ofList rs).height = rs.length) :
    ∃ rs' : List R, maximalIdeal R ∈ (Ideal.ofList (rs ++ rs')).minimalPrimes ∧
    rs.length + rs'.length = ringKrullDim R := by
  have ne : ringKrullDim R ≠ ⊥ ∧ ringKrullDim R ≠ ⊤ :=
    finiteRingKrullDim_iff_ne_bot_and_top.mp inferInstance
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim R = d := by
    have : (ringKrullDim R).unbot ne.1 ≠ ⊤ := by
      rw [ne_eq, ← WithBot.coe_inj]
      simpa using ne.2
    rcases ENat.ne_top_iff_exists.mp this with ⟨d, hd⟩
    use d
    rw [← WithBot.coe_inj, WithBot.coe_unbot] at hd
    exact hd.symm
  generalize len : d - rs.length = k
  induction k generalizing rs
  · have : Ideal.ofList rs ≤ maximalIdeal R := (span_le.mpr mem)
    have netop : Ideal.ofList rs ≠ ⊤ := (lt_of_le_of_lt this IsPrime.ne_top'.lt_top).ne_top
    have coe_eq : (d : WithBot ℕ∞) = (d : ℕ∞) := rfl
    have le : rs.length ≤ d := by
      simpa [ht, hd, coe_eq] using Ideal.height_le_ringKrullDim_of_ne_top netop
    rw [Nat.sub_eq_zero_iff_le] at len
    use []
    simp only [List.append_nil, le_antisymm le len, List.length_nil, CharP.cast_eq_zero, add_zero,
      hd, and_true]
    apply Ideal.mem_minimalPrimes_of_height_eq this
    rw [ht, le_antisymm le len, ← WithBot.coe_le_coe]
    simp [hd, coe_eq]
  · rename_i k hk
    classical
    have : Ideal.ofList rs ≤ maximalIdeal R := (span_le.mpr mem)
    have netop : Ideal.ofList rs ≠ ⊤ := (lt_of_le_of_lt this IsPrime.ne_top'.lt_top).ne_top
    have coe_eq : (d : WithBot ℕ∞) = (d : ℕ∞) := rfl
    have le : rs.length ≤ d := by
      simpa [ht, hd, coe_eq] using Ideal.height_le_ringKrullDim_of_ne_top netop
    obtain ⟨x, hx, nmem⟩ : ∃ x ∈ maximalIdeal R, ∀ p ∈ (Ideal.ofList rs).minimalPrimes, x ∉ p := by
      have : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ (Ideal.ofList rs).minimalPrimes, p := by
        by_contra subset
        rcases (Ideal.subset_union_prime_finite
          (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.ofList rs)) ⊤ ⊤
          (fun p mem _ _ ↦ mem.1.1)).mp subset with ⟨p, hp, le⟩
        let _ := hp.1.1
        have eq := Ideal.IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le
        rw [← eq] at hp
        rw [IsLocalRing.height_eq_height_maximalIdeal_of_maximalIdeal_mem_minimalPrimes _ hp,
          ← WithBot.coe_inj, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hd] at ht
        simp only [coe_eq, WithBot.coe_inj, Nat.cast_inj] at ht
        simp [ht] at len
      rcases Set.not_subset.mp this with ⟨x, hx1, hx2⟩
      simp at hx2
      use x
      tauto
    have mem' : ∀ r ∈ rs ++ [x], r ∈ maximalIdeal R := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      intro r hr
      rcases hr with mem_rs|eqx
      · exact mem r mem_rs
      · simpa [eqx] using hx
    have ht' : (ofList (rs ++ [x])).height = (rs ++ [x]).length := by
      apply le_antisymm (Ideal.ofList_height_le_length' _ mem')
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
        Nat.cast_one, height, ofList_append, ofList_cons, ofList_nil, bot_le, sup_of_le_left,
        le_iInf_iff]
      intro p hp
      let _ := hp.1.1
      rcases Ideal.exists_minimalPrimes_le (sup_le_iff.mp hp.1.2).1 with ⟨q, hq, qle⟩
      let _ := hq.1.1
      have lt : q < p := lt_of_le_of_ne qle (ne_of_mem_of_not_mem'
          ((sup_le_iff.mp hp.1.2).2 (mem_span_singleton_self x)) (nmem q hq)).symm
      apply le_trans _ (Ideal.primeHeight_add_one_le_of_lt lt)
      simpa only [← ht, ← height_eq_primeHeight] using add_le_add_left (Ideal.height_mono hq.1.2) 1
    have len' : d - (rs ++ [x]).length = k := by
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
      omega
    rcases hk (rs ++ [x]) mem' ht' len' with ⟨rs', hrs', hlen⟩
    use x :: rs'
    rw [List.append_cons]
    refine ⟨hrs', ?_⟩
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ← hlen, List.length_append,
      List.length_nil, zero_add]
    abel

lemma maximalIdeal_mem_minimalPrimes_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (h : Function.Surjective f) {I : Ideal R}
    {J : Ideal S} (le : I ≤ J.comap f) (min : maximalIdeal R ∈ I.minimalPrimes) (ne : J ≠ ⊤) :
    maximalIdeal S ∈ J.minimalPrimes := by
  refine ⟨⟨Ideal.IsMaximal.isPrime' _, le_maximalIdeal ne⟩, fun q ⟨hq, Jle⟩ _ ↦ ?_⟩
  have eq_map : maximalIdeal S = Ideal.map f (maximalIdeal R) := by
    have := ((local_hom_TFAE f).out 0 4).mp (Function.Surjective.isLocalHom f h)
    rw [← Ideal.map_comap_of_surjective f h (maximalIdeal S), this]
  rw [eq_map, Ideal.map_le_iff_le_comap]
  exact min.2 ⟨q.comap_isPrime f, le_trans le (Ideal.comap_mono Jle)⟩
    (le_maximalIdeal_of_isPrime (q.comap f))

open Pointwise in
lemma isRegular_of_maximalIdeal_mem_ofList_minimalPrimes
    [IsCohenMacaulayLocalRing R] (rs : List R)
    (mem : maximalIdeal R ∈ (Ideal.ofList rs).minimalPrimes)
    (dim : rs.length = ringKrullDim R) : IsRegular R rs := by
  refine ⟨?_, by simpa using (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' mem.1.2).symm⟩
  generalize len : rs.length = n
  induction n generalizing R rs
  · simp [List.length_eq_zero_iff.mp len]
  · rename_i n hn _ _ _
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have xmem : x ∈ maximalIdeal R := mem.1.2 (Ideal.subset_span (by simp))
      let R' := R ⧸ x • (⊤ : Ideal R)
      have : Nontrivial R' :=
        Ideal.Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      let _ : IsLocalRing R' := IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
      have xreg : IsSMulRegular R x := by
        by_contra nreg
        have mem_ass : x ∈ {r : R | IsSMulRegular R r}ᶜ := nreg
        simp only [← biUnion_associatedPrimes_eq_compl_regular, Set.mem_iUnion, SetLike.mem_coe,
          exists_prop] at mem_ass
        rcases mem_ass with ⟨p, ass, xmem⟩
        let _ := (isCohenMacaulayLocalRing_iff R).mp ‹_›
        have eq := ModuleCat.depth_eq_supportDim_of_cohenMacaulay (ModuleCat.of R R)
        rw [depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay p (ModuleCat.of R R) ass,
          Module.supportDim_self_eq_ringKrullDim, WithBot.coe_unbot] at eq
        have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ass.1)
        have : IsLocalHom (Ideal.Quotient.mk p) :=
          IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
        let _ : IsLocalRing (R ⧸ p) :=
          IsLocalRing.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
        have mem_max : ∀ r ∈ rs'.map (algebraMap R (R ⧸ p)), r ∈ maximalIdeal (R ⧸ p) := by
          simp only [Ideal.Quotient.algebraMap_eq, List.mem_map,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          intro r hr
          exact map_nonunit (Ideal.Quotient.mk p) r (mem.1.2 (Ideal.subset_span (by simp [hr])))
        have netop : Ideal.ofList (rs'.map (algebraMap R (R ⧸ p))) ≠ ⊤ :=
          ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr mem_max)
        have le : Ideal.ofList (x :: rs') ≤
          (Ideal.ofList (rs'.map (algebraMap R (R ⧸ p)))).comap (Ideal.Quotient.mk p) := by
          rw [Ideal.span_le]
          intro r hr
          rcases List.mem_cons.mp hr with eqx|mem_rs'
          · apply Ideal.ker_le_comap
            simpa [eqx] using xmem
          · apply Ideal.subset_span
            simp only [Ideal.Quotient.algebraMap_eq, List.mem_map, Set.mem_setOf_eq]
            use r
        have max_mem := maximalIdeal_mem_minimalPrimes_of_surjective (Ideal.Quotient.mk p)
          Ideal.Quotient.mk_surjective le mem netop
        have := Ideal.ofList_height_le_length' (rs'.map (algebraMap R (R ⧸ p))) mem_max
        have coe_eq : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = ((rs'.length + 1 : ℕ) : ℕ∞) := rfl
        rw [height_eq_height_maximalIdeal_of_maximalIdeal_mem_minimalPrimes _ max_mem,
          ← WithBot.coe_le_coe, List.length_map, maximalIdeal_height_eq_ringKrullDim,
          ← eq, ← dim, List.length_cons, coe_eq, WithBot.coe_le_coe, ENat.coe_le_coe] at this
        simp at this
      simp only [isWeaklyRegular_cons_iff, xreg, true_and]
      have min : maximalIdeal R' ∈ (Ideal.ofList (rs'.map (algebraMap R R'))).minimalPrimes := by
        have le : Ideal.ofList (x :: rs') ≤
          (Ideal.ofList (rs'.map (algebraMap R R'))).comap (algebraMap R R') := by
          rw [Ideal.span_le]
          intro r hr
          rcases List.mem_cons.mp hr with eqx|mem_rs'
          · apply Ideal.ker_le_comap
            simpa [R', eqx, ← Submodule.ideal_span_singleton_smul x] using
              Ideal.mem_span_singleton_self x
          · apply Ideal.subset_span
            simp only [List.mem_map, Set.mem_setOf_eq]
            use r
        apply maximalIdeal_mem_minimalPrimes_of_surjective (algebraMap R R')
          Ideal.Quotient.mk_surjective le mem
        have mem_max : ∀ r ∈ rs'.map (algebraMap R R'), r ∈ maximalIdeal R' := by
          simpa only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using
            fun r hr ↦ map_nonunit (Ideal.Quotient.mk (x • (⊤ : Ideal R))) r
            (mem.1.2 (Ideal.subset_span (by simp [hr])))
        exact ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr mem_max)
      let _ := (quotient_regular_smul_top_isCohenMacaulay_iff_isCohenMacaulay R x xreg xmem).mp ‹_›
      rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff R' R' rs']
      apply hn (rs'.map (algebraMap R R')) min _ (by simpa using len)
      have : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
        rw [← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
        exact Module.supportDim_quotSMulTop_succ_eq_supportDim xreg xmem
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ← this] at dim
      simpa [List.length_map] using WithBot.add_one_cancel.mp dim

lemma isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing [IsCohenMacaulayLocalRing R]
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) (ht : (Ideal.ofList rs).height = rs.length) :
    IsRegular R rs := by
  refine ⟨⟨fun i hi ↦ ?_⟩, ?_⟩
  · rcases maximalIdeal_mem_ofList_append_minimalPrimes_of_ofList_height_eq_length rs mem ht with
      ⟨rs', min, len⟩
    rw [← Nat.cast_add, ← List.length_append] at len
    have := (isRegular_of_maximalIdeal_mem_ofList_minimalPrimes _ min len).1.1 i
      (lt_of_lt_of_eq (Nat.lt_add_right rs'.length hi) List.length_append.symm)
    rw [List.take_append_of_le_length (le_of_lt hi)] at this
    simpa [List.getElem_append_left' hi rs'] using this
  · simpa using (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (span_le.mpr mem)).symm

end CMcat

section Unmixedness

/-- An ideal `I` is unmixed if every associated prime of `I` has height equal to `I.height`. -/
class Ideal.IsUnmixed (I : Ideal R) : Prop where
  height_eq : ∀ {p : Ideal R}, p ∈ associatedPrimes R (R ⧸ I) → p.height = I.height

lemma associatedPrimes_eq_minimalPrimes_of_isUnmixed [IsNoetherianRing R] {I : Ideal R}
    (unmix : I.IsUnmixed) : associatedPrimes R (R ⧸ I) = I.minimalPrimes := by
  apply le_antisymm
  · intro p hp
    let _ := hp.1
    apply Ideal.mem_minimalPrimes_of_height_eq _ (le_of_eq (unmix.1 hp))
    rw [← Ideal.annihilator_quotient (I := I), ← Submodule.annihilator_top]
    exact IsAssociatedPrime.annihilator_le hp
  · nth_rw 1 [← Ideal.annihilator_quotient (I := I)]
    exact associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R (R ⧸ I)

lemma Ideal.ofList_isUnmixed_of_associatedPrimes_eq_minimalPrimes [IsNoetherianRing R] (l : List R)
    (h : (Ideal.ofList l).height = l.length)
    (ass : associatedPrimes R (R ⧸ Ideal.ofList l) ⊆ (Ideal.ofList l).minimalPrimes) :
    (Ideal.ofList l).IsUnmixed := by
  refine ⟨fun {p} hp ↦ le_antisymm ?_ (Ideal.height_mono (ass hp).1.2)⟩
  let _ := hp.1
  rw [h, Ideal.height_le_iff_exists_minimalPrimes]
  use Ideal.ofList l
  have fg : (ofList l).FG := by
    classical
    simp only [ofList, ← List.coe_toFinset]
    use l.toFinset
  refine ⟨ass hp, ?_⟩
  simpa [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg] using Ideal.ofList_spanFinrank_le_length l

variable [IsNoetherianRing R]

lemma isCohenMacaulayRing_of_unmixed
    (unmix : ∀ (l : List R), (Ideal.ofList l).height = l.length → (Ideal.ofList l).IsUnmixed) :
    IsCohenMacaulayRing R := by
  apply (isCohenMacaulayRing_def R).mpr (fun p hp ↦ (isCohenMacaulayLocalRing_def _).mpr ?_)
  have netop : p.height ≠ ⊤ := by
    have := p.finiteHeight_of_isNoetherianRing.1
    have := Ideal.IsPrime.ne_top hp
    tauto
  have {i : ℕ} : i ≤ p.height → ∃ rs : List R, (∀ r ∈ rs, r ∈ p) ∧ IsWeaklyRegular R rs ∧
    rs.length = i := by
    induction i
    · intro _
      use []
      simp
    · rename_i i hi
      intro le
      have lt : i < p.height := lt_of_lt_of_le (ENat.coe_lt_coe.mpr (lt_add_one i)) le
      rcases hi (le_of_lt lt) with ⟨rs, mem, reg, len⟩
      have netop : Ideal.ofList rs ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsPrime.ne_top hp)
        (Ideal.span_le.mpr mem)
      have ht := (Ideal.ofList_height_eq_length_of_isWeaklyRegular rs reg netop)
      let _ := Ideal.Quotient.nontrivial_iff.mpr netop
      obtain ⟨r, rmem, hr⟩ : ∃ r ∈ p, IsSMulRegular (R ⧸ Ideal.ofList rs) r := by
        by_contra! h
        obtain ⟨q, qass, le⟩ : ∃ q ∈ associatedPrimes R (R ⧸ Ideal.ofList rs), p ≤ q := by
          rcases associatedPrimes.nonempty R (R ⧸ Ideal.ofList rs) with ⟨Ia, hIa⟩
          apply (Ideal.subset_union_prime_finite (associatedPrimes.finite R _) Ia Ia
            (fun I hin _ _ ↦ IsAssociatedPrime.isPrime hin)).mp
          rw [biUnion_associatedPrimes_eq_compl_regular R (R ⧸ Ideal.ofList rs)]
          exact fun r hr ↦ h r hr
        have := Ideal.height_mono le
        rw [(unmix rs ht).1 qass, ht, len] at this
        exact this.not_gt lt
      use rs.concat r
      simp only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.length_append, len, List.length_cons, List.length_nil, zero_add, and_true]
      refine ⟨fun s ↦ or_imp.mpr ⟨fun h ↦ mem s h, fun eq ↦ by simpa [eq]⟩, ⟨fun i hi ↦ ?_⟩⟩
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
        Nat.lt_succ_iff] at hi
      rw [List.take_append_of_le_length hi]
      rcases lt_or_eq_of_le hi with lt|eq
      · simpa [← List.getElem_append_left' lt [r]] using reg.1 i lt
      · rw [List.getElem_concat_length eq, Ideal.smul_eq_mul, Ideal.mul_top,
          List.take_of_length_le (ge_of_eq eq)]
        exact hr
  apply le_antisymm _ (depth_le_ringKrullDim _)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, IsLocalRing.depth_eq_sSup_length_regular,
    WithBot.coe_le_coe]
  apply le_sSup
  rcases this p.height.coe_toNat_le_self with ⟨rs, mem, reg, len⟩
  use List.map (algebraMap R (Localization.AtPrime p)) rs
  simp only [List.length_map, len, ENat.coe_toNat_eq_self, ne_eq, netop, not_false_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, exists_prop, and_true]
  have : ∀ a ∈ rs, (algebraMap R (Localization.AtPrime p)) a ∈
    IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    intro a ha
    simpa [← Ideal.mem_comap, Localization.AtPrime.comap_maximalIdeal] using mem a ha
  refine ⟨⟨IsWeaklyRegular.of_flat reg, ?_⟩, this⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top, ne_comm]
  apply ne_top_of_le_ne_top (b := maximalIdeal (Localization.AtPrime p)) Ideal.IsPrime.ne_top'
  simpa only [Ideal.ofList, List.mem_map, Ideal.span_le] using fun b ⟨a, mem, eq⟩ ↦
   (by simpa [← eq] using this a mem)

omit [IsNoetherianRing R] in
lemma IsLocalization.height_le_height_map (S : Submonoid R) {A : Type*} [CommRing A] [Algebra R A]
    [IsLocalization S A] (J : Ideal R) : J.height ≤ (Ideal.map (algebraMap R A) J).height := by
  apply le_iInf_iff.mpr (fun p ↦ (le_iInf_iff.mpr fun hp ↦ ?_))
  let _ := hp.1.1
  rw [← Ideal.height_eq_primeHeight, ← IsLocalization.height_comap S p]
  exact Ideal.height_mono (Ideal.le_comap_of_map_le hp.1.2)

theorem isCohenMacaulayRing_iff_unmixed : IsCohenMacaulayRing R ↔
    ∀ (l : List R), (Ideal.ofList l).height = l.length → (Ideal.ofList l).IsUnmixed := by
  refine ⟨fun ⟨cm⟩ l ht ↦ ⟨fun {p} hp ↦ ?_⟩, fun h ↦ isCohenMacaulayRing_of_unmixed h⟩
  have netop : Ideal.ofList l ≠ ⊤ := by
    by_contra eq
    simp [eq] at ht
  let _ := hp.1
  have le : Ideal.ofList l ≤ p := by
    apply le_of_eq_of_le _ (IsAssociatedPrime.annihilator_le hp)
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient]
  have ht_eq : (maximalIdeal (Localization.AtPrime p)).height = p.height := by
    rw [← IsLocalization.height_comap p.primeCompl, Localization.AtPrime.comap_maximalIdeal]
  have mem : ∀ r ∈ List.map (algebraMap R (Localization.AtPrime p)) l,
    r ∈ maximalIdeal (Localization.AtPrime p) := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ← Ideal.mem_comap, Localization.AtPrime.comap_maximalIdeal]
    intro a ha
    apply le (Ideal.subset_span ha)
  have ht_eq_len : (Ideal.ofList (l.map (algebraMap R (Localization.AtPrime p)))).height =
    (List.map (⇑(algebraMap R (Localization.AtPrime p))) l).length := by
    apply le_antisymm (Ideal.ofList_height_le_length' _ mem)
    simpa only [List.length_map, ← ht, ← Ideal.map_ofList]
      using IsLocalization.height_le_height_map p.primeCompl _
  let _ := cm p hp.1
  have reg := isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing _ mem ht_eq_len
  have CM := (quotient_regular_isCohenMacaulay_iff_isCohenMacaulay
    (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))
    (l.map (algebraMap R (Localization.AtPrime p))) reg).mp
    ((isCohenMacaulayLocalRing_iff _).mp (cm p hp.1))
  let _ := IsRegular.quot_ofList_smul_nontrivial reg ⊤
  let S := ((Localization.AtPrime p) ⧸ Ideal.ofList
    (l.map (algebraMap R (Localization.AtPrime p))) • (⊤ : Ideal (Localization.AtPrime p)))
  have ann : Module.annihilator (Localization.AtPrime p) S =
    Ideal.ofList (l.map (algebraMap R (Localization.AtPrime p))) := by
    simp [S, Ideal.annihilator_quotient]
  have eqmin : associatedPrimes (Localization.AtPrime p) S =
    (Module.annihilator (Localization.AtPrime p) S).minimalPrimes :=
    associated_prime_eq_minimalPrimes_isCohenMacaulay (ModuleCat.of (Localization.AtPrime p) S)
  have : maximalIdeal (Localization.AtPrime p) ∈ associatedPrimes (Localization.AtPrime p) S := by
    have := associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp
    simp only [smul_eq_mul, S]
    rw [Ideal.mul_top, ← Ideal.map_ofList]
    convert this
    rw [← Ideal.localized'_eq_map (Localization.AtPrime p) p.primeCompl]
    let f := Submodule.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p)) (Ideal.ofList l)
    exact LinearEquiv.AssociatedPrimes.eq (IsLocalizedModule.mapEquiv p.primeCompl f
      (LocalizedModule.mkLinearMap p.primeCompl (R ⧸ Ideal.ofList l)) (Localization.AtPrime p)
      (LinearEquiv.refl R _))
  rw [eqmin, ann] at this
  simp [← ht_eq, ← height_eq_height_maximalIdeal_of_maximalIdeal_mem_minimalPrimes _ this, ht,
    ht_eq_len]

end Unmixedness
