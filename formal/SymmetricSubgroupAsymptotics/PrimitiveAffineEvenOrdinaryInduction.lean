import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PermutationAutomorphismPuncturedAction
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions

/-! The primitive affine ordinary-generator induction in every even
degree at least eight. The same point stabilizer acts faithfully on the
original nonidentity translations, a strictly smaller set of degree n−1.
No bound at degree n, and no finite affine catalogue, is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEvenOrdinaryInduction
open PermutationAutomorphismPuncturedAction PermutationOrdinarySmallerActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem two_mul_genRank_le_degree (hprimitive : MulAction.IsPreprimitive G X)
    (heven : Even (Nat.card X)) (hn : 8≤Nat.card X)
    (hbelow : SmallerActionBound (Nat.card X)) : 2*MarkedC4.genRank G≤Nat.card X := by
  let x : X := Classical.arbitrary X
  let H := P.complement x
  let φ : H→*MulAut P.V := P.complementAction x
  have hφ : Function.Injective φ := P.complementAction_injective x
  letI : MulAction H (Punctured P.V) := MulAction.compHom _ (puncturedHom φ)
  letI : FaithfulSMul H (Punctured P.V) := by
    constructor
    intro h k hh
    apply puncturedHom_injective φ hφ
    apply Equiv.ext
    intro v
    exact hh v
  have hcard : Nat.card (Punctured P.V)=Nat.card X-1 := by
    rw [punctured_card,P.card_eq x]
  have hH : 2*MarkedC4.genRank H≤Nat.card X-1 := by
    have hh := hbelow H (Punctured P.V) (by omega) (by omega)
    simpa only [hcard] using hh
  have hG := P.genRank_le_complement_add_one hprimitive x
  change MarkedC4.genRank G≤MarkedC4.genRank H+1 at hG
  rcases heven with ⟨k,hk⟩
  omega

include P in
theorem exists_half_degree_generators (hprimitive : MulAction.IsPreprimitive G X)
    (heven : Even (Nat.card X)) (hn : 8≤Nat.card X)
    (hbelow : SmallerActionBound (Nat.card X)) :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤Nat.card X := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  rw [hS]
  exact two_mul_genRank_le_degree P hprimitive heven hn hbelow

end SymmetricSubgroupAsymptotics.PrimitiveAffineEvenOrdinaryInduction
