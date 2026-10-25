import SymmetricSubgroupAsymptotics.CFSGFFourBinaryNativeCentralAction
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviWeylRoots
import SymmetricSubgroupAsymptotics.CFSGSymplecticSimpleWeyl

/-! Actual native short Weyl words swap both paired-coordinate blocks.
Their point lift fixes the central coordinate because the literal dot
product is unchanged. This matches the displayed F4 Weyl axis formulas. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativeWeylCoordinates
open CFSGFFourBinaryNativeCentralAction CFSGFFourBinaryShortLeviWeylRoots
open CFSGFFourBinaryRadicalCentralLayers CFSGSymplecticSerreMatrices
open CFSGSymplecticBinaryPointTailAction CFSGSymplecticHeisenbergVectorAction
variable (K : Type) [Field K] [CharP K 2]

theorem native_weyl_vector (n : Fin 2) (v : (Fin 3 → K) × (Fin 3 → K)) :
    vectorLinearHom K 3 (simpleWeyl K 3 n.castSucc) v =
      (v.1 ∘ swapIndex n,v.2 ∘ swapIndex n) := by
  rw [vectorLinearHom_apply,simpleWeyl_chain_val,←Matrix.mulVec_mulVec]
  apply Prod.ext <;> funext i
  all_goals
    fin_cases n <;> fin_cases i <;>
      simp [CFSGMatrixPairRotation.rotation,vectorEquiv,swapIndex,Function.comp_def,
        Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec,
        CharTwo.sub_eq_add,CharTwo.neg_eq,CharTwo.add_self_eq_zero,Equiv.swap_apply_def]

omit [CharP K 2] in
private theorem swap_dot (n : Fin 2) (u v : Fin 3 → K) :
    dotProduct (u ∘ swapIndex n) (v ∘ swapIndex n)=dotProduct u v := by
  simp only [dotProduct,Fin.sum_univ_three]
  fin_cases n <;> simp [swapIndex,Equiv.swap_apply_def] <;> ring

theorem nativeCentralAction_weyl [Finite K] (hK : Nat.card K=2)
    (n : Fin 2) (x : CentralCoordinates K) :
    nativeCentralAction K hK (simpleWeyl K 3 n.castSucc) x =
      Multiplicative.ofAdd (x.toAdd.1,(x.toAdd.2.1 ∘ swapIndex n,x.toAdd.2.2 ∘ swapIndex n)) := by
  rw [nativeCentralAction_apply,pointLinearHom_apply,native_weyl_vector]
  apply Multiplicative.toAdd.injective
  change (x.toAdd.1+dotProduct x.toAdd.2.1 x.toAdd.2.2+
      dotProduct (x.toAdd.2.1 ∘ swapIndex n) (x.toAdd.2.2 ∘ swapIndex n),
      (x.toAdd.2.1 ∘ swapIndex n,x.toAdd.2.2 ∘ swapIndex n)) =
    (x.toAdd.1,(x.toAdd.2.1 ∘ swapIndex n,x.toAdd.2.2 ∘ swapIndex n))
  rw [swap_dot,add_assoc,CharTwo.add_self_eq_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativeWeylCoordinates
