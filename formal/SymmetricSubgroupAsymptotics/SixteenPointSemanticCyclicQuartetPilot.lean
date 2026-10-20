import SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932ActualImportedRow

/-! The literal16T1932 action instantiates the shared family constructor.
All physical membership and generator bindings are the previously checked
ones; the new path retains the actual representative and its original axes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetPilot
open BinaryPlaneWreathIrreducible BinaryPlaneWreathNormalGenerators
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles

abbrev K := Subgroup.closure (Set.range lifted)

theorem localSingers (i : Fin 4) : localEmbedding i singer ∈ actualImage K := by
  let C := actualImage K
  have hgen (j : Fin 2) : (lifted j).right ∈ C := ⟨closureGenerators lifted j,rfl⟩
  have hz : singerSeed ∈ C := C.pow_mem (C.mul_mem (hgen 0) (hgen 1)) 2
  rw [← singerWords_eq i]
  exact C.mul_mem
    (C.mul_mem (C.pow_mem (hgen 0) i.val) (C.pow_mem hz (exponents i)))
    (C.inv_mem (C.pow_mem (hgen 0) i.val))

def beta : actualImage K →* Blocks := PermutationalWreathProduct.rightHom.comp
  (actualImage K).subtype

theorem beta_surjective : Function.Surjective beta := by
  have hr : PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation ∈ beta.range :=
    ⟨⟨(lifted 0).right,⟨closureGenerators lifted 0,rfl⟩⟩,rfl⟩
  intro r
  obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
  have he : PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation^z = r := Subtype.ext hz
  rw [← he]
  exact beta.range.zpow_mem hr z

theorem transitiveImage (i j : Fin 4) :
    ∃ q : actualImage K, (q : Lin).right • i = j := by
  obtain ⟨r,hr⟩ := blocks_transitive i j
  obtain ⟨q,hq⟩ := beta_surjective r
  exact ⟨q,by change beta q • i = j; rw [hq,hr]⟩

def originalMap : K →* Original :=
  GeneratedLiteralImage.toTop (action.comp K.subtype) (closureGenerators lifted)
    generators (Equiv.refl _) (closureGenerators_full lifted) bindings

theorem originalMap_surjective : Function.Surjective originalMap :=
  GeneratedLiteralImage.toTop_surjective (action.comp K.subtype)
    (closureGenerators lifted) generators (Equiv.refl _)
    (closureGenerators_full lifted) bindings

open PrimitiveAffineDegreeTwoNonbinary16T1932ActualImportedRow (index originalEquiv)

def actualMap : K →* preE7NonPairAction 16 index :=
  originalEquiv.toMonoidHom.comp originalMap

theorem actualMap_surjective : Function.Surjective actualMap :=
  originalEquiv.surjective.comp originalMap_surjective

def source (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 index :=
  SixteenPointSemanticCyclicQuartetSource.source K localSingers transitiveImage
    beta_surjective PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation blocks_cycle blocks_coprime index actualMap
    actualMap_surjective hMN hZmud

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetPilot
end
