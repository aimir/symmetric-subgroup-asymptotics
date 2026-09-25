import SymmetricSubgroupAsymptotics.C1SplitCharacters
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Literal inverse-complement charts

The chart consists of an original subgroup N and an original order-three
element x normalizing it and meeting it trivially. It constructs the
actual group N<x> and the unique oriented quotient character.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

variable (G : Type*) [Group G]

structure TernaryComplementChart where
  kernel : Subgroup G
  generator : G
  generator_order : orderOf generator = 3
  normalizes : generator ∈ Subgroup.normalizer (kernel : Set G)
  disjoint : Disjoint kernel (Subgroup.zpowers generator)

namespace TernaryComplementChart
variable {G} (C : TernaryComplementChart G)

def source : Subgroup G := C.kernel ⊔ Subgroup.zpowers C.generator

def sourceGenerator : C.source := ⟨C.generator,(show Subgroup.zpowers C.generator ≤ C.source from le_sup_right)
  (Subgroup.mem_zpowers _)⟩

theorem cyclic_le_normalizer : Subgroup.zpowers C.generator ≤ Subgroup.normalizer (C.kernel : Set G) :=
  Subgroup.zpowers_le.mpr C.normalizes

instance kernel_normal : (C.kernel.subgroupOf C.source).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le C.kernel.le_normalizer C.cyclic_le_normalizer)

def quotientMap : C.source →* C.source ⧸ C.kernel.subgroupOf C.source :=
  QuotientGroup.mk' _

def cyclicQuotientMap : Subgroup.zpowers C.generator →*
    C.source ⧸ C.kernel.subgroupOf C.source :=
  C.quotientMap.comp (Subgroup.inclusion le_sup_right)

theorem cyclicQuotientMap_injective : Function.Injective C.cyclicQuotientMap := by
  apply (injective_iff_map_eq_one _).mpr
  intro z hz
  have hn : (z : G) ∈ C.kernel :=
    (QuotientGroup.eq_one_iff
      (Subgroup.inclusion (show Subgroup.zpowers C.generator ≤ C.source from le_sup_right) z)).mp hz
  apply Subtype.ext
  exact (Subgroup.disjoint_def.mp C.disjoint hn z.2)

theorem cyclicQuotientMap_surjective : Function.Surjective C.cyclicQuotientMap := by
  intro y
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (C.kernel.subgroupOf C.source) y
  have hk : (k : G) ∈ (C.kernel : Set G) * (Subgroup.zpowers C.generator : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ C.cyclic_le_normalizer]
    exact k.2
  obtain ⟨n,hn,z,hz,he⟩ := hk
  let n' : C.source := ⟨n,(show C.kernel ≤ C.source from le_sup_left) hn⟩
  let z' : Subgroup.zpowers C.generator := ⟨z,hz⟩
  have hnq : C.quotientMap n' = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hk' : n' * Subgroup.inclusion le_sup_right z' = k := Subtype.ext he
  refine ⟨z',?_⟩
  change C.quotientMap (Subgroup.inclusion le_sup_right z') = C.quotientMap k
  rw [← hk']
  exact ((C.quotientMap.map_mul n' _).trans (by rw [hnq,one_mul])).symm

def cyclicQuotientEquiv : Subgroup.zpowers C.generator ≃*
    C.source ⧸ C.kernel.subgroupOf C.source :=
  MulEquiv.ofBijective C.cyclicQuotientMap
    ⟨C.cyclicQuotientMap_injective,C.cyclicQuotientMap_surjective⟩

def cyclicEquiv : TernaryCyclic ≃* Subgroup.zpowers C.generator :=
  mulEquivOfOrderOfEq
    (g' := (⟨C.generator,Subgroup.mem_zpowers _⟩ : Subgroup.zpowers C.generator))
    ternaryGenerator_generates (by
    intro z
    obtain ⟨n,hn⟩ := z.2
    exact ⟨n,Subtype.ext hn⟩)
    (by rw [ternaryGenerator_order,Subgroup.orderOf_mk,C.generator_order])

theorem cyclicEquiv_generator :
    C.cyclicEquiv ternaryGenerator = ⟨C.generator,Subgroup.mem_zpowers _⟩ :=
  mulEquivOfOrderOfEq_apply_gen _ _ _

/-- The original quotient map, followed by its oriented cyclic chart. -/
def characterHom : C.source →* TernaryCyclic :=
  C.cyclicEquiv.symm.toMonoidHom.comp
    (C.cyclicQuotientEquiv.symm.toMonoidHom.comp C.quotientMap)

def character : PrimeCharacters 3 C.source :=
  AddMonoidHom.toMultiplicativeRight.symm C.characterHom

theorem character_generator : C.character (Additive.ofMul C.sourceGenerator) = 1 := by
  have hg : C.quotientMap C.sourceGenerator =
      C.cyclicQuotientEquiv ⟨C.generator,Subgroup.mem_zpowers _⟩ := rfl
  change (C.cyclicEquiv.symm (C.cyclicQuotientEquiv.symm
    (C.quotientMap C.sourceGenerator))).toAdd = 1
  rw [hg,C.cyclicQuotientEquiv.symm_apply_apply,← C.cyclicEquiv_generator,
    C.cyclicEquiv.symm_apply_apply]
  rfl

theorem character_kernel : C.characterHom.ker = C.kernel.subgroupOf C.source := by
  ext g
  change C.cyclicEquiv.symm (C.cyclicQuotientEquiv.symm (C.quotientMap g)) = 1 ↔ _
  rw [C.cyclicEquiv.symm.map_eq_one_iff, C.cyclicQuotientEquiv.symm.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff g

theorem character_split : TernarySplit C.character := by
  apply (ternarySplit_iff_witness _).mpr
  refine ⟨C.sourceGenerator,?_,C.character_generator⟩
  exact (Subgroup.orderOf_mk C.generator _).trans C.generator_order

end TernaryComplementChart
end SymmetricSubgroupAsymptotics
