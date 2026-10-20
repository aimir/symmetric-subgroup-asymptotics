import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Literal ambient normal subgroups of an abelian normal subgroup are
exactly the submodules of its integral conjugation representation. This
retains all primes at once and does not invoke Maschke's theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule

variable {G : Type} [Group G]

def representation (N : Subgroup G) [N.Normal] [IsMulCommutative N] :
    Representation ℤ G (Additive N) where
  toFun g := (MonoidHom.toAdditive (MulAut.conjNormal g).toMonoidHom).toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (1 : G) * _ * (1 : G)⁻¹ = _
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (g * h) * (v.toMul : G) * (g * h)⁻¹ =
      g * (h * (v.toMul : G) * h⁻¹) * g⁻¹
    group

variable (N : Subgroup G) [N.Normal] [IsMulCommutative N]

@[simp] theorem representation_apply (g : G) (v : Additive N) :
    representation N g v = Additive.ofMul (MulAut.conjNormal g v.toMul) := rfl

def normalSubrepresentation (M : Subgroup G) [M.Normal] :
    Subrepresentation (representation N) where
  toSubmodule := {
    carrier := {v | (v.toMul : G) ∈ M}
    zero_mem' := M.one_mem
    add_mem' := fun ha hb => M.mul_mem ha hb
    smul_mem' z v hv := by
      change ((v.toMul : G) ^ z) ∈ M
      exact M.zpow_mem hv z }
  apply_mem_toSubmodule g v hv := by
    change g * (v.toMul : G) * g⁻¹ ∈ M
    exact (inferInstance : M.Normal).conj_mem _ hv g

def normalSubmodule (M : Subgroup G) [M.Normal] :
    Submodule ℤ[G] (representation N).asModule :=
  (normalSubrepresentation N M).asSubmodule

def submoduleGroup (S : Submodule ℤ[G] (representation N).asModule) : Subgroup G :=
  ({ carrier := {n : N | (Additive.ofMul n : (representation N).asModule) ∈ S}
     one_mem' := S.zero_mem
     mul_mem' := fun ha hb => S.add_mem ha hb
     inv_mem' := fun ha => S.neg_mem ha } : Subgroup N).map N.subtype

theorem mem_submoduleGroup (S : Submodule ℤ[G] (representation N).asModule) (n : N) :
    (n : G) ∈ submoduleGroup N S ↔
      (Additive.ofMul n : (representation N).asModule) ∈ S := by
  constructor
  · rintro ⟨m, hm, he⟩
    have hmn : m = n := Subtype.ext he
    simpa only [hmn] using hm
  · intro hn
    exact ⟨n, hn, rfl⟩

instance submoduleGroup_normal (S : Submodule ℤ[G] (representation N).asModule) :
    (submoduleGroup N S).Normal := by
  constructor
  rintro _ ⟨n, hn, rfl⟩ g
  refine ⟨MulAut.conjNormal g n, ?_, rfl⟩
  exact (Subrepresentation.ofSubmodule' S).apply_mem_toSubmodule g hn

theorem submoduleGroup_le (S : Submodule ℤ[G] (representation N).asModule) :
    submoduleGroup N S ≤ N := by
  rintro _ ⟨n, _, rfl⟩
  exact n.property

theorem submoduleGroup_mono {S T : Submodule ℤ[G] (representation N).asModule}
    (h : S ≤ T) : submoduleGroup N S ≤ submoduleGroup N T := by
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, h hn, rfl⟩

theorem normalSubmodule_mono {M K : Subgroup G} [M.Normal] [K.Normal]
    (h : M ≤ K) : normalSubmodule N M ≤ normalSubmodule N K := by
  intro v hv
  exact h hv

theorem submoduleGroup_normalSubmodule (M : Subgroup G) [M.Normal] (hMN : M ≤ N) :
    submoduleGroup N (normalSubmodule N M) = M := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact hn
  · intro g hg
    exact ⟨⟨g, hMN hg⟩, hg, rfl⟩

theorem normalSubmodule_submoduleGroup (S : Submodule ℤ[G] (representation N).asModule) :
    normalSubmodule N (submoduleGroup N S) = S := by
  ext v
  exact mem_submoduleGroup N S v.toMul

theorem submoduleGroup_eq_bot_iff (S : Submodule ℤ[G] (representation N).asModule) :
    submoduleGroup N S = ⊥ ↔ S = ⊥ := by
  constructor
  · intro he
    apply le_antisymm ?_ bot_le
    intro v hv
    apply (Submodule.mem_bot (R := ℤ[G])).mpr
    apply Additive.toMul.injective
    apply Subtype.ext
    have hvG := (mem_submoduleGroup N S v.toMul).mpr hv
    rw [he] at hvG
    exact Subgroup.mem_bot.mp hvG
  · intro he
    subst S
    apply le_antisymm ?_ bot_le
    rintro _ ⟨n, hn, rfl⟩
    change (Additive.ofMul n : (representation N).asModule) ∈
      (⊥ : Submodule ℤ[G] (representation N).asModule) at hn
    have hn0 : (Additive.ofMul n : (representation N).asModule) = 0 :=
      (Submodule.mem_bot (R := ℤ[G]) (M := (representation N).asModule)).mp hn
    have hn1 : n = 1 := congrArg (fun v : (representation N).asModule => v.toMul) hn0
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hn1)

/-- Ambient minimal normality is exactly simplicity in the integral
conjugation representation, whenever the factor lies in the carrier. -/
theorem minimalNormal_isSimple (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hMN : M ≤ N) :
    letI : M.Normal := hM.1
    IsSimpleModule ℤ[G] (normalSubmodule N M) := by
  letI : M.Normal := hM.1
  rw [isSimpleModule_iff_isAtom, isAtom_iff_le_of_ge]
  constructor
  · intro he
    have hbot := (submoduleGroup_eq_bot_iff N (normalSubmodule N M)).mpr he
    rw [submoduleGroup_normalSubmodule N M hMN] at hbot
    exact hM.2.1 hbot
  · intro S hS hle
    have hSne : submoduleGroup N S ≠ ⊥ := by
      intro hb
      exact hS ((submoduleGroup_eq_bot_iff N S).mp hb)
    have hSM : submoduleGroup N S ≤ M := by
      rw [← submoduleGroup_normalSubmodule N M hMN]
      exact submoduleGroup_mono N hle
    have hEq := hM.2.2 (submoduleGroup N S) inferInstance hSne hSM
    intro v hv
    apply (mem_submoduleGroup N S v.toMul).mp
    rw [hEq]
    exact hv

/-- A simple invariant submodule is a literal ambient minimal normal
subgroup, including its original normality. -/
theorem simple_isMinimalNormal (S : Submodule ℤ[G] (representation N).asModule)
    (hS : IsSimpleModule ℤ[G] S) : IsMinimalNormalSubgroup (submoduleGroup N S) := by
  have hAtom := (isSimpleModule_iff_isAtom.mp hS)
  have hA := isAtom_iff_le_of_ge.mp hAtom
  refine ⟨inferInstance, ?_, ?_⟩
  · intro hb
    exact hA.1 ((submoduleGroup_eq_bot_iff N S).mp hb)
  · intro M hM hMne hMS
    letI : M.Normal := hM
    have hMN : M ≤ N := hMS.trans (submoduleGroup_le N S)
    have hmodne : normalSubmodule N M ≠ ⊥ := by
      intro hb
      have hgroup := (submoduleGroup_eq_bot_iff N (normalSubmodule N M)).mpr hb
      rw [submoduleGroup_normalSubmodule N M hMN] at hgroup
      exact hMne hgroup
    have hmodle : normalSubmodule N M ≤ S := by
      intro v hv
      exact (mem_submoduleGroup N S v.toMul).mp (hMS hv)
    have hback : S ≤ normalSubmodule N M := hA.2 _ hmodne hmodle
    apply le_antisymm hMS
    rw [← submoduleGroup_normalSubmodule N M hMN]
    exact submoduleGroup_mono N hback

/-- Semisimplicity of the actual conjugation module puts its carrier in
the literal ambient socle. -/
theorem le_socle_of_semisimple
    [IsSemisimpleModule ℤ[G] (representation N).asModule] : N ≤ finiteGroupSocle G := by
  let T := normalSubmodule N (finiteGroupSocle G)
  have hall : (⊤ : Submodule ℤ[G] (representation N).asModule) ≤ T := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top ℤ[G] (representation N).asModule]
    apply sSup_le
    intro S hS v hv
    exact Subgroup.subset_normalClosure
      ⟨submoduleGroup N S, simple_isMinimalNormal N S hS,
        (mem_submoduleGroup N S v.toMul).mpr hv⟩
  intro g hg
  exact hall (show (Additive.ofMul (⟨g, hg⟩ : N) : (representation N).asModule) ∈
    (⊤ : Submodule ℤ[G] (representation N).asModule) from trivial)

end SymmetricSubgroupAsymptotics.SolubleSocleConjugationModule
