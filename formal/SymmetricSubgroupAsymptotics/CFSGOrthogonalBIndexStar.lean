import SymmetricSubgroupAsymptotics.CFSGSLProjectivePointRootStar
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! The actual B SL chain consumes the reusable projective point-root
star. Its existing literal double embedding is faithful by its first
matrix block, giving q^(rank-1) proper index for its actual central
quotient. No odd/even original-model recognition is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexStar
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
open CFSGTypeAIndexReindex
variable (K : Type) [Field K]

theorem doubleIntoElementary_injective (r : ℕ) :
    Function.Injective (doubleIntoElementary K r) := by
  intro A B he
  have hm := congrArg (fun u : elementaryRootGroup K r =>
    Matrix.toBlocks₁₁ (Matrix.toBlocks₁₁ (u.val : Mat K r))) he
  change A.val=B.val at hm
  exact Subtype.ext hm

def starEmbedding (s : ℕ) : CFSGSLProjectivePointRootStar.SL K s →*
    elementaryRootGroup K (s+3) :=
  (doubleIntoElementary K (s+3)).comp
    (slReindex (F:=K) (splitCoordinates (s+2))).toMonoidHom

theorem starEmbedding_injective (s : ℕ) : Function.Injective (starEmbedding K s) :=
  (doubleIntoElementary_injective K (s+3)).comp
    (slReindex (F:=K) (splitCoordinates (s+2))).injective

theorem projective_field_power_le_proper_index [Finite K] (s : ℕ)
    [IsSimpleGroup (elementaryProjective K (s+3))]
    (H : Subgroup (elementaryProjective K (s+3))) (hH : H≠⊤) :
    Nat.card K^(s+2) ≤ H.index := by
  letI : IsSimpleGroup ((elementaryRootGroup K (s+3))⧸
      Subgroup.center (elementaryRootGroup K (s+3))) :=
    inferInstanceAs (IsSimpleGroup (elementaryProjective K (s+3)))
  let f := starEmbedding K s
  let U := CFSGSLProjectivePointRootStar.starRoot K s f
  have hcard : Nat.card U=Nat.card K^(s+2) :=
    CFSGSLProjectivePointRootStar.starRoot_card K s f (starEmbedding_injective K s)
  letI : Finite (elementaryProjective K (s+3)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s+3))))
      (QuotientGroup.mk'_surjective _)
  letI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) (Finite.one_lt_card (α:=K)))
  have hh := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate U
    (CFSGSLProjectivePointRootStar.star_nonidentity_conjugate K s f) H hH
  simpa only [hcard] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexStar
