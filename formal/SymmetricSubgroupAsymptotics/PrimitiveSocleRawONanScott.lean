import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import SymmetricSubgroupAsymptotics.OuterWreathPermutationCompression
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly
import SymmetricSubgroupAsymptotics.PrimitiveSocleDegreeFormNumerics

/-!
Bare structural O'Nan--Scott data, separated from the outer logarithmic
profile. Source: Liebeck--Praeger--Saxl, J. Austral. Math. Soc. A 44 (1988),
389--396, classification in section 1 and theorem on p392. The socle below
is the FULL socle, including both minimal normals in HS/HC. Product-action
factors use an actual proper subgroup index. Diagonal/product-diagonal
cases have k=m*l and exponent (m-1)*l; regular cases have exponent k.
Consequently their second degree form has k <= 2*a. The quotient embedding
is the ordinary outer-automorphism/factor-permutation structure; no
permutation compression or numerical outer estimate is imported here.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

open Non2UnipotentPrefixFiniteMenu

/-- Structural data on the original action and its actual full socle. -/
structure NonaffineData (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] where
  Simple : Type
  [group : Group Simple]
  [finite : Finite Simple]
  [simple : IsSimpleGroup Simple]
  noncommutative : ¬ IsMulCommutative Simple
  factorCount : ℕ
  factorCount_pos : 0 < factorCount
  socleEquiv : finiteGroupSocle G ≃* (Fin factorCount → Simple)
  quotientEmbedding : (G ⧸ finiteGroupSocle G) →*
    OuterWreathPermutationCompression.Wreath (Outer Simple) factorCount
  quotientEmbedding_injective : Function.Injective quotientEmbedding
  socle_transitive : MulAction.IsPretransitive (finiteGroupSocle G) X
  indexForm :
    (∃ H : Subgroup Simple, H ≠ ⊤ ∧ Nat.card X = H.index ^ factorCount) ∨
    (∃ a : ℕ, factorCount ≤ 2*a ∧ Nat.card X = (Nat.card Simple)^a)

attribute [instance] NonaffineData.group NonaffineData.finite NonaffineData.simple

/-- Raw finite primitive classification. The affine alternative only states
existence of a regular normal prime-power subgroup; the nonaffine alternative
contains no index lower bound or outer-order inequality. -/
def PublishedONanScottStructure : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X],
    Nonempty (NonaffineData G X ⊕ PrimitiveAffineProfile G X)

/-- Minimality of the actual proper-subgroup index supplies the first
numerical degree form. This is a deduction, not part of the classification. -/
theorem NonaffineData.degreeForm {G X : Type} [Group G] [Finite G]
    [Finite X] [MulAction G X] (D : NonaffineData G X)
    {ell : ℕ} (hell : LeastProperIndex D.Simple ell) :
    PrimitiveSocleDegreeForm ell (Nat.card D.Simple) D.factorCount (Nat.card X) := by
  rcases D.indexForm with ⟨H,hH,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact Or.inl ⟨H.index,hell.2 H hH,hdegree⟩
  · exact Or.inr ⟨a,hka,hdegree⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
