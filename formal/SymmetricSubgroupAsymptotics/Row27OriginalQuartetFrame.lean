import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row27OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
 def points : Fin 3 × Fin 4 ≃ Fin 12 where
  toFun x := (#[0,3,6,9,2,8,11,5,1,4,10,7] : Array (Fin 12))[4*x.1.val+x.2.val]!
  invFun x := (#[(0,0),(2,0),(1,0),(0,1),(2,1),(1,3),
    (0,2),(2,3),(1,1),(0,3),(2,2),(1,2)] : Array (Fin 3 × Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
 def tops : Fin 4 → Equiv.Perm (Fin 3) := ![1,finRotate 3,(finRotate 3)⁻¹,Equiv.swap 1 2]
private theorem preserves : ∀ (i : Fin 4) (x : Fin 3 × Fin 4),
    (points.symm (row27Generators i (points x))).1=tops i x.1 := by decide +kernel
 def frame : ProductBlockFrame Row27Top (Fin 3) (Fin 4) :=
  ProductBlockFrame.ofGenerators points row27Generators tops preserves
 def original : Fin 4 → Row27Top := closureGenerators row27Generators
 theorem generator_top (i : Fin 4) : frame.top (original i)=tops i :=
  ProductBlockFrame.ofGenerators_top_generator points row27Generators tops preserves i
private def words : Fin 6 → FiniteGeneratorWord (Fin 4) :=
  ![.one,.generator 1,.mul (.generator 1) (.generator 1),.generator 3,
    .mul (.generator 3) (.generator 1),
    .mul (.generator 3) (.mul (.generator 1) (.generator 1))]
 theorem top_surjective : Function.Surjective frame.top := by
  have hw : ∀ p : Equiv.Perm (Fin 3),∃ i : Fin 6,(words i).eval tops=p := by decide +kernel
  intro p
  obtain ⟨i,hi⟩ := hw p
  refine ⟨(words i).eval original,?_⟩
  rw [FiniteGeneratorWord.map_eval]
  have he : (fun j => frame.top (original j))=tops := funext generator_top
  rw [he]
  exact hi
end SymmetricSubgroupAsymptotics.Row27OriginalQuartetFrame
