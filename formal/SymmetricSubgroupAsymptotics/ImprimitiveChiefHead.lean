import SymmetricSubgroupAsymptotics.ActualLocalChiefHead
import SymmetricSubgroupAsymptotics.ImprimitiveChiefCoordinates
import SymmetricSubgroupAsymptotics.RelativeSecondIsomorphism

/-! Original imprimitive actions install the actual local-chief head
bound. The local component is the literal stabilizer image on the base
fibre; the subgroup is the original intersection with the block kernel.
All original conjugation, restrictions, and the single top section survive. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A Ω X:Type} [Group A] [Finite A] [MulAction A Ω] [MulAction A X]
variable [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]
variable (b:Ω→X) (hb:∀ (a:A) (ω:Ω),b (a•ω)=a•b ω) (x₀:X)

/-- The complete original subgroup in the block kernel, for any actual
chief series of the original local component. -/
theorem originalBlockChiefHead_bound
    (N:Subgroup A) [N.Normal] (hN:N≤(MulAction.toPermHom A X).ker)
    (s:ActualChiefSeries (originalBlockComponent b hb x₀)) :
    (Module.finrank (ZMod 3) (primeRelativeCharacters 3 N):ℝ)≤
      (actualChiefSeriesTernaryWeight s:ℝ)*(ternaryIndexWidth (Nat.card X):ℝ) := by
  letI : Finite (originalBlockComponent b hb x₀) :=
    Finite.of_surjective (originalBlockProjection b hb x₀)
      (originalBlockFibreAction b hb x₀).rangeRestrict_surjective
  have h := actualLocalChiefHead_bound N (MulAction.stabilizer A x₀)
    (originalBlockEvaluation b hb x₀ N hN) (originalBlockProjection b hb x₀)
    (originalBlockEvaluation_conjugation b hb x₀ N hN)
    (originalBlockFibreAction b hb x₀).rangeRestrict_surjective
    (originalBlockEvaluation_conjugates_separate b hb x₀ N hN) s
  rwa [MulAction.index_stabilizer_of_transitive A x₀] at h

/-- An arbitrary original normal subgroup, with its block-kernel
intersection treated once and its original top quotient retained once. -/
theorem originalImprimitiveChiefHead_bound
    (N:Subgroup A) [N.Normal]
    (s:ActualChiefSeries (originalBlockComponent b hb x₀)) :
    (Module.finrank (ZMod 3) (primeRelativeCharacters 3 N):ℝ)≤
      (actualChiefSeriesTernaryWeight s:ℝ)*(ternaryIndexWidth (Nat.card X):ℝ)+
        (Module.finrank (ZMod 3) (primeRelativeCharacters 3
          (normalChainQuotient (MulAction.toPermHom A X).ker N)):ℝ) := by
  let U := N⊓(MulAction.toPermHom A X).ker
  have hu := originalBlockChiefHead_bound b hb x₀ U inf_le_right s
  have h := primeRelativeHead_chain_le U N 3 inf_le_left
  have h' : (Module.finrank (ZMod 3) (primeRelativeCharacters 3 N):ℝ)≤
      (Module.finrank (ZMod 3) (primeRelativeCharacters 3 U):ℝ)+
        (Module.finrank (ZMod 3) (primeRelativeCharacters 3 (normalChainQuotient U N)):ℝ) := by
    exact_mod_cast h
  have hfinal := h'.trans (add_le_add hu le_rfl)
  simpa only [U,primeRelativeHead_second_isomorphism] using hfinal

end SymmetricSubgroupAsymptotics
