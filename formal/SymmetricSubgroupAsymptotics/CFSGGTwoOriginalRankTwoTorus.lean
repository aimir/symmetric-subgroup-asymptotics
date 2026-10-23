import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords

/-! The faithful original rank-two torus, with its literal root words
retained. The native equivalence used here is unconditional. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRankTwoTorus
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGGTwoSerreMatrices
open CFSGGTwoOriginalNaturalEquivalence
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

def weylParameter (i : Fin 2) (t : Kˣ) : Model A K :=
  modelRoot A K false i (t : K) * modelRoot A K true i (-(t⁻¹ : Kˣ) : K) *
    modelRoot A K false i (t : K)

def torusNode (i : Fin 2) (t : Kˣ) : Model A K :=
  weylParameter K i t * weylParameter K i (-1)

theorem shortNode_native (t : Kˣ) :
    modelEquivNatural K (torusNode K 0 t) = CFSGGTwoNaturalRankTwoTorus.shortTorus K t := by
  simp only [torusNode, weylParameter, map_mul, modelEquivNatural_root,
    CFSGGTwoNaturalRankTwoTorus.shortTorus, CFSGGTwoNaturalRankTwoTorus.shortWeylParameter]

theorem longNode_native (t : Kˣ) :
    modelEquivNatural K (torusNode K 1 t) = CFSGGTwoLongTorusAction.longTorus t := by
  simp only [torusNode, weylParameter, map_mul, modelEquivNatural_root,
    CFSGGTwoLongTorusAction.longTorus, CFSGGTwoLongTorusAction.longWeylParameter]

def torusPair (t : Kˣ × Kˣ) : Model A K :=
  torusNode K 0 t.1 * torusNode K 1 t.2

theorem torusPair_native (t : Kˣ × Kˣ) :
    modelEquivNatural K (torusPair K t) = CFSGGTwoNaturalRankTwoTorus.torusPair K t := by
  simp only [torusPair, map_mul, shortNode_native, longNode_native,
    CFSGGTwoNaturalRankTwoTorus.torusPair]

theorem torusPair_injective : Function.Injective (torusPair K) := by
  intro t u he
  apply CFSGGTwoNaturalRankTwoTorus.torusPair_injective K
  rw [← torusPair_native, ← torusPair_native]
  exact congrArg (modelEquivNatural K) he

def torusHom : (Kˣ × Kˣ) →* Model A K :=
  (modelEquivNatural K).symm.toMonoidHom.comp (CFSGGTwoNaturalRankTwoTorus.torusHom K)

theorem torusHom_apply (t : Kˣ × Kˣ) : torusHom K t = torusPair K t := by
  apply (modelEquivNatural K).injective
  change modelEquivNatural K ((modelEquivNatural K).symm
    (CFSGGTwoNaturalRankTwoTorus.torusPair K t)) = _
  rw [(modelEquivNatural K).apply_symm_apply, torusPair_native]

theorem torusHom_injective : Function.Injective (torusHom K) := by
  intro t u he
  apply torusPair_injective K
  simpa only [torusHom_apply] using he

theorem nodes_commute (a b : Kˣ) : Commute (torusNode K 0 a) (torusNode K 1 b) := by
  change torusNode K 0 a * torusNode K 1 b = torusNode K 1 b * torusNode K 0 a
  apply (modelEquivNatural K).injective
  simp only [map_mul, shortNode_native, longNode_native]
  exact (CFSGGTwoNaturalRankTwoTorus.short_long_commute K a b).eq

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRankTwoTorus
