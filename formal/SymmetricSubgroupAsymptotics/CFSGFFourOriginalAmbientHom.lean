import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWords
import SymmetricSubgroupAsymptotics.CFSGFFourE6AmbientPositiveSylow

/-! The whole original F4 Model embeds in the same literal E6 elementary
group in characteristic two. Its positive subgroup is defined as the
full ambient positive preimage, without a simple-generator assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalAmbientHom
open CFSG.Models.Chevalley CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalFoldedEquivalence CFSGFFourE6AmbientPositiveSylow
open CFSGFFourE6RootSubgroups
variable (K : Type) [Field K] [Finite K] [CharP K 2]

def modelAmbientHom : Model CartanMatrix.F₄ K→*AmbientGroup K :=
  (rawHom K).codRestrict (AmbientGroup K) (fun g=>by
    apply foldedModel_le_ambient K
    exact (modelEquivFolded K g).property)

theorem modelAmbientHom_val (g : Model CartanMatrix.F₄ K) :
    (modelAmbientHom K g).val=rawHom K g := rfl

theorem modelAmbientHom_injective : Function.Injective (modelAmbientHom K) := by
  intro x y he
  exact rawHom_injective K (congrArg (fun z : AmbientGroup K=>z.val) he)

def modelPositive : Subgroup (Model CartanMatrix.F₄ K) :=
  (AmbientPositive K).comap (modelAmbientHom K)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalAmbientHom
