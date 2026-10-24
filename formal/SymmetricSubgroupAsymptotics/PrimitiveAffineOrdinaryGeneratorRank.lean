import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder
import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget

/-! Ordinary generators for the literal ambient group of a primitive
affine profile. Primitivity supplies irreducibility; faithfulness bounds
the actual point stabilizer by linear maps on the translation space.
No published permutation-generator theorem is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] (P : PrimitiveAffineProfile G X)

theorem complementAction_ordinary_irreducible
    (hprimitive : MulAction.IsPreprimitive G X) (x : X) :
    letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
    IrreducibleAbelianSemidirect.Irreducible (P.complementAction x) := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  intro S hS
  let K : Subgroup G := S.map P.V.subtype
  have hKnormal : K.Normal := by
    constructor
    intro y hy g
    obtain ⟨v,hv,rfl⟩ := hy
    obtain ⟨⟨u,h⟩,hgh⟩ := (P.isComplement'_complement x).2 g
    let w : P.V := P.complementAction x h v
    have hc : (u:G)*(w:G)=(w:G)*(u:G) := congrArg Subtype.val (mul_comm u w)
    refine ⟨w,hS h v hv,?_⟩
    change (h:G)*(v:G)*(h:G)⁻¹=g*(v:G)*g⁻¹
    rw [←hgh]
    calc
      (h:G)*(v:G)*(h:G)⁻¹=(u:G)*((h:G)*(v:G)*(h:G)⁻¹)*(u:G)⁻¹ := by
        change (w:G)=(u:G)*(w:G)*(u:G)⁻¹
        rw [hc]
        group
      _=((u:G)*(h:G))*(v:G)*((u:G)*(h:G))⁻¹ := by group
  rcases P.minimal hprimitive K hKnormal (Subgroup.map_subtype_le S) with hbot|htop
  · exact Or.inl ((S.map_eq_bot_iff_of_injective P.V.subtype_injective).mp hbot)
  · right
    apply Subgroup.map_injective P.V.subtype_injective
    simpa only [K,←MonoidHom.range_eq_map,Subgroup.range_subtype] using htop

theorem genRank_le_complement_add_one
    (hprimitive : MulAction.IsPreprimitive G X) (x : X) :
    MarkedC4.genRank G≤MarkedC4.genRank (P.complement x)+1 := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  letI : Nontrivial P.V := (P.pointEquiv x).symm.injective.nontrivial
  letI : Finite (P.V ⋊[(P.V.normalizerMonoidHom).comp
      (Subgroup.inclusion (P.V.normalizer_eq_top ▸ le_top))] P.complement x) :=
    Finite.of_equiv G (P.semidirectEquiv x).symm.toEquiv
  rw [←CoprimeNilpotentProductGenerators.genRank_mulEquiv (P.semidirectEquiv x)]
  exact IrreducibleAbelianSemidirectOrdinaryGenerators.genRank_le_complement_add_one
    (P.complementAction x) (P.complementAction_ordinary_irreducible hprimitive x)

section Faithful
variable [FaithfulSMul G X]

/-- The exact complement bound is `p^(d²)` for the actual elementary
chart, rather than a guessed matrix-group realization. -/
theorem complement_card_le_prime_pow_dimension_sq
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) (x : X) :
    Nat.card (P.complement x)≤P.p^(C.d^2) := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v:C.V=>C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hcard := P.complement_card_le_degree_pow_finrank C.equiv x
  have hdegree : Nat.card X=P.p^C.d := by
    simpa only [ElementaryChart.d] using P.degree_eq_prime_pow_finrank C.equiv x
  change Nat.card (P.complement x)≤Nat.card X^C.d at hcard
  simpa only [hdegree,←pow_mul,pow_two] using hcard

theorem genRank_le_binary_dimension_sq_add_one
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (x : X) (b : ℕ) (hp : P.p≤2^b) :
    MarkedC4.genRank G≤b*C.d^2+1 := by
  have hcomp := FiniteGroupBinaryOrderGenerators.genRank_le_mul_of_card_le_pow
    (P.complement x) P.p b (C.d^2) hp
    (P.complement_card_le_prime_pow_dimension_sq hprimitive C x)
  exact (P.genRank_le_complement_add_one hprimitive x).trans (Nat.add_le_add_right hcomp 1)

theorem genRank_le_pred_dimension_sq_add_one
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) (x : X) :
    MarkedC4.genRank G≤(P.p-1)*C.d^2+1 := by
  have hcomp := FiniteGroupBinaryOrderGenerators.genRank_le_pred_mul_of_card_le_pow
    (P.complement x) P.p (C.d^2) P.p_prime.pos
    (P.complement_card_le_prime_pow_dimension_sq hprimitive C x)
  exact (P.genRank_le_complement_add_one hprimitive x).trans (Nat.add_le_add_right hcomp 1)

end Faithful
end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
