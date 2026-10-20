import SymmetricSubgroupAsymptotics.PrimitiveSocleDegreeFormsProof
import SymmetricSubgroupAsymptotics.NormalSubgroupOuterEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott

/-! Unconditional raw O'Nan--Scott structure in precisely the original
interface: the FULL socle, original primitive action, literal outer-wreath
quotient embedding, and actual proper-subgroup/diagonal degree forms. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open PrimitiveSocleONanScottHelpers

/-- The required raw finite primitive structure follows from minimal
normal subgroup theory and the proved Scott subdirect-product theorem. -/
theorem publishedONanScottStructure : PublishedONanScottStructure := by
  intro G X _ _ _ _ _ _ _
  obtain ⟨D⟩ := fullSocle_or_affine_nonempty G X
  cases D with
  | inr A => exact ⟨Sum.inr A⟩
  | inl D =>
    letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
    have hT : IsCenterless D.Simple := isCenterless_of_simple_perfect D.Simple
    have hS : IsCenterless (finiteGroupSocle G) := by
      intro s hs
      apply D.equiv.injective
      rw [map_one]
      funext i
      apply hT (D.equiv s i)
      intro t
      have h := congrArg D.equiv (hs (D.equiv.symm (Pi.mulSingle i t)))
      have hi := congrFun h i
      simpa only [map_mul,MulEquiv.apply_symm_apply,Pi.mul_apply,
        Pi.mulSingle_eq_same] using hi
    have hC : Subgroup.centralizer (finiteGroupSocle G : Set G)=⊥ :=
      FullSocleSelfCentralizing.centralizer_eq_bot hS
    exact ⟨Sum.inl {
      Simple := D.Simple
      noncommutative := D.noncommutative
      factorCount := D.factorCount
      factorCount_pos := D.factorCount_pos
      socleEquiv := D.equiv
      quotientEmbedding := NormalSubgroupOuterEmbedding.quotientEmbedding
        (finiteGroupSocle G) hT D.equiv
      quotientEmbedding_injective := NormalSubgroupOuterEmbedding.quotientEmbedding_injective
        (finiteGroupSocle G) hT D.equiv hC
      socle_transitive := D.transitive
      indexForm := D.indexForm }⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
