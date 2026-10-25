import SymmetricSubgroupAsymptotics.SquareScalarOrderTwentyFivePermutationDegree
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCharacteristicIndex

/-! Proper index at least15 for the actual SL2 and full-centre PSL2
quotients over a field of order25. The original upper-root additive
action and original determinant-one torus supply the generic fixed-count
obstruction. Neither simplicity nor subgroup recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoTwentyFiveIndex
open CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots CFSGPSLTwoRootCoordinates

/-- The actual coset action, including its original upper-root action,
pays the15-point floor before passage to the full centre quotient. -/
theorem slTwo_proper_index_ge_fifteen {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K=25) (H : Subgroup (SL2 (F:=K))) (hH : H≠⊤) :
    15≤H.index := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (SL2 (F:=K) ⧸ H) := Fintype.ofFinite _
  letI : MulAction (Multiplicative K) (SL2 (F:=K) ⧸ H) :=
    MulAction.compHom _ (upperHom (F:=K))
  change 15≤Nat.card (SL2 (F:=K) ⧸ H)
  apply SquareScalarOrderTwentyFivePermutationDegree.fifteen_le_card_of_square_fixedBy
    (F:=K) hK
  · intro a c
    have he := Nat.card_congr
      (CFSGConjugateSubgroupDegree.fixedByConjugateEquiv (X:=SL2 (F:=K) ⧸ H)
        (upper (a:K)) (torus (by decide : (0:Fin 2)≠1) c))
    have hact : torus (by decide : (0:Fin 2)≠1) c*upper (a:K)*
        (torus (by decide : (0:Fin 2)≠1) c)⁻¹=upper ((c:K)^2*(a:K)) :=
      torus_conjugation (by decide : (0:Fin 2)≠1) c (a:K)
    rw [hact] at he
    simpa only [MulAction.fixedBy,MulAction.compHom_smul_def,upperHom,mul_comm]
      using he.symm
  · intro a
    exact CFSGSLTwoProperIndexLower.exists_moved_coset H hH a a.ne_zero

/-- The same index bound for the pinned original PSL2 model, retaining
the actual full-centre projection and original proper subgroup. -/
theorem proper_index_ge_fifteen (q : CFSG.PrimePower) (hq : q.order=25)
    (H : Subgroup (CFSG.Models.A 1 q)) (hH : H≠⊤) : 15≤H.index := by
  have hpre : H.comap (projection (F:=q.Field))≠⊤ := by
    intro ht
    apply hH
    apply top_unique
    intro x _
    obtain ⟨g,rfl⟩ := projection_surjective (F:=q.Field) x
    have hg : g∈H.comap (projection (F:=q.Field)) := by rw [ht]; trivial
    exact hg
  have hh := slTwo_proper_index_ge_fifteen (K:=q.Field)
    (by rw [q.card_field,hq])
    (H.comap (CFSGPSLTwoRootCoordinates.projection (F:=q.Field))) hpre
  rw [H.index_comap_of_surjective (CFSGPSLTwoRootCoordinates.projection_surjective
    (F:=q.Field))] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGPSLTwoTwentyFiveIndex
