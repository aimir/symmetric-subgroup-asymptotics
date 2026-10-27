import SymmetricSubgroupAsymptotics.CFSGMonsterRemoteTernaryTails
import SymmetricSubgroupAsymptotics.E6BraidSystemDerivedImage
import SymmetricSubgroupAsymptotics.TernaryIndependentPairEmbedding

/-! The SAME original Monster contains an actual perfect E6-derived
image and an independent commuting C3×C3. All maps are literal subgroup
inclusions or original-generator word maps. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6RemoteTernaryEmbedding
open CFSG.Models.MonsterConstruction CFSGMonsterRemoteTernaryTails

abbrev system := CFSGMonsterE6ActualNormalizerIndex.system
abbrev E6Derived := E6BraidSystemDerivedImage.DerivedImage system
abbrev e6Embedding : E6Derived →* CFSG.Models.Monster :=
  E6BraidSystemDerivedImage.embedding system

theorem e6Embedding_injective : Function.Injective e6Embedding :=
  E6BraidSystemDerivedImage.embedding_injective system

theorem e6Derived_perfect : commutator E6Derived=⊤ :=
  E6BraidSystemDerivedImage.derived_perfect system

theorem anchor_ne_one (hn : ¬IsMulCommutative CFSG.Models.Monster) :
    E6BraidSystemDerivedWords.a (E6BraidSystemDerivedImage.imageSystem system)≠1 := by
  intro he
  have hh := congrArg e6Embedding he
  rw [E6BraidSystemDerivedImage.anchor_binding,
    CFSGMonsterE6ActualNormalizerIndex.selected_cube_binding,map_one] at hh
  exact CFSGMonsterSelectedDerivedCube.selected_ne_one hn hh

abbrev ternaryEmbedding :
    TernaryIndependentPairEmbedding.P×TernaryIndependentPairEmbedding.P →* CFSG.Models.Monster :=
  TernaryIndependentPairEmbedding.embedding firstTail secondTail first_cube second_cube tails_commute

theorem ternaryEmbedding_injective (hn : ¬IsMulCommutative CFSG.Models.Monster) :
    Function.Injective ternaryEmbedding :=
  TernaryIndependentPairEmbedding.embedding_injective firstTail secondTail first_cube second_cube
    tails_commute (first_ne_one hn) (second_ne_one hn)
    firstInverter firstInverter_first firstInverter_second

private theorem first_commutes_e6 (g : E6Derived) : Commute firstTail (e6Embedding g) := by
  have hle : E6BraidSystemDerivedImage.ReflectionGroup system≤
      Subgroup.centralizer {firstTail.val} := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (first_commutes_reflection i).eq.symm
  have hh := Subgroup.mem_centralizer_singleton_iff.mp (hle g.val.property)
  apply Subtype.ext
  exact hh.symm

private theorem second_commutes_e6 (g : E6Derived) : Commute secondTail (e6Embedding g) := by
  have hle : E6BraidSystemDerivedImage.ReflectionGroup system≤
      Subgroup.centralizer {secondTail.val} := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (second_commutes_reflection i).eq.symm
  have hh := Subgroup.mem_centralizer_singleton_iff.mp (hle g.val.property)
  apply Subtype.ext
  exact hh.symm

theorem embeddings_commute (p : TernaryIndependentPairEmbedding.P×TernaryIndependentPairEmbedding.P)
    (g : E6Derived) : Commute (ternaryEmbedding p) (e6Embedding g) := by
  change Commute (TernaryCubePowerHom.powerHom firstTail first_cube p.1*
    TernaryCubePowerHom.powerHom secondTail second_cube p.2) (e6Embedding g)
  change Commute (TernaryCubePowerHom.powerHom firstTail first_cube
    (Multiplicative.ofAdd p.1.toAdd)*TernaryCubePowerHom.powerHom secondTail second_cube
      (Multiplicative.ofAdd p.2.toAdd)) (e6Embedding g)
  rw [TernaryCubePowerHom.powerHom_val,TernaryCubePowerHom.powerHom_val]
  exact ((first_commutes_e6 g).pow_left _).mul_left ((second_commutes_e6 g).pow_left _)

theorem card_ge_twentySeven_of_nontrivial_action
    [Finite CFSG.Models.Monster] {X : Type*} [Finite X] [MulAction E6Derived X]
    (hmove : ∃ g : E6Derived, ∃ x : X, g • x≠x) : 27≤Nat.card X :=
  E6BraidSystemDerivedImage.card_ge_twentySeven_of_nontrivial_action system hmove

end SymmetricSubgroupAsymptotics.CFSGMonsterE6RemoteTernaryEmbedding
