import SymmetricSubgroupAsymptotics.TwoTripleAffineSubgroupNonbinarySocles
import SymmetricSubgroupAsymptotics.TwoTripleLiteralAffineSubgroupChart
import SymmetricSubgroupAsymptotics.TwoTripleProductFrameRecognition
import SymmetricSubgroupAsymptotics.PermutationConjugateTopChart
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! The complete TWO TRIPLES geometric branch: every actual nonbinary
normal quotient of the original six-point top has socle bound one.
Both point conjugacy and the original denominator are retained explicitly. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.SixPointTwoTripleNonbinaryQuotientSocles

variable (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)]

/-- Literal upper-wreath inclusion; no subgroup catalogue is consumed. -/
theorem of_literal
    (hle : P≤SixPairLocalWreathSocles.literalAction.range)
    (N : Subgroup P) [N.Normal] (hQ : ¬IsPGroup 2 (P ⧸ N)) :
    SocleNormalGeneratorBound (P ⧸ N) 1 := by
  let K := TwoTripleLiteralAffineSubgroupChart.affineSubgroup P
  let e : P ≃* K := TwoTripleLiteralAffineSubgroupChart.groupChart P hle
  let M := N.map e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let qe : P ⧸ N ≃* K ⧸ M := QuotientGroup.congr N M e rfl
  have hM : ¬IsPGroup 2 (K ⧸ M) := fun h => hQ (h.of_equiv qe.symm)
  have hs := TwoTripleAffineSubgroupNonbinarySocles.quotient_socle_one K
    (TwoTripleLiteralAffineSubgroupChart.upper_swap P hle) M hM
  exact CyclicSocleQuotientTools.socleBound_equiv qe.symm hs

/-- Actual geometric source, preserving every original normal axis. -/
theorem quotient (F : ProductBlockFrame P (Fin 2) (ZMod 3))
    (N : Subgroup P) [N.Normal] (hQ : ¬IsPGroup 2 (P ⧸ N)) :
    SocleNormalGeneratorBound (P ⧸ N) 1 := by
  let c := TwoTripleProductFrameRecognition.conjugator F
  let D : Subgroup (Equiv.Perm (Fin 6)) := MulAut.conj c • P
  let e : P ≃* D := PermutationConjugateTopChart.groupChart P D c rfl
  letI : MulAction.IsPretransitive D (Fin 6) := by
    constructor
    intro x y
    obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P (c.symm x) (c.symm y)
    refine ⟨e p,?_⟩
    change c (p.val (c.symm x))=y
    change p.val (c.symm x)=c.symm y at hp
    rw [hp,c.apply_symm_apply]
  let M := N.map e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let qe : P ⧸ N ≃* D ⧸ M := QuotientGroup.congr N M e rfl
  have hM : ¬IsPGroup 2 (D ⧸ M) := fun h => hQ (h.of_equiv qe.symm)
  have hs := of_literal D (TwoTripleProductFrameRecognition.conjugate_le F) M hM
  exact CyclicSocleQuotientTools.socleBound_equiv qe.symm hs

end SymmetricSubgroupAsymptotics.SixPointTwoTripleNonbinaryQuotientSocles
