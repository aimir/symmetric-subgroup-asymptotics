import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLiftedWeylWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! The literal matrix/root grading detects the integral Weyl action even
in bad characteristic. This follows from nonzero diagonal entries of the
identity matrix, not from separation of field eigenvalues. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylDegreeFaithful
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWordLatticeSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckLiftedWeylWords
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem wordLinear_eq_one_of_wordUnit_eq_one (K : Type) [Field K]
    (w : List (Fin r)) (hw : wordUnit A hs hp b₀ s₀ K w=1) :
    wordLinear A hs hp b₀ s₀ w=1 := by
  have hdegree := word_lattice_support A hs hp b₀ s₀ K w
  rw [hw] at hdegree
  have hfix : ∀i : Fin r,wordLinear A hs hp b₀ s₀ w (Pi.single i 1)=Pi.single i 1 := by
    intro i
    by_contra he
    have hne : latticeWeight A hs hp b₀ (.inr (s₀ i:Roots A))≠
        wordLinear A hs hp b₀ s₀ w (latticeWeight A hs hp b₀ (.inr (s₀ i:Roots A))) :=
      Ne.symm he
    have hz := hdegree (.inr (s₀ i:Roots A)) (.inr (s₀ i:Roots A)) hne
    exact (one_ne_zero : (1:K)≠0) (by simpa using hz)
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℤ (Fin r)).ext
  intro i
  simp only [Pi.basisFun_apply]
  exact hfix i

theorem lifted_matrixProjection_injective (K : Type) [Field K] :
    Function.Injective ((MonoidHom.fst _ _).comp
      (liftedWeyl A hs hp b₀ s₀ K).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  obtain ⟨w,hw⟩ := x.property
  have hx₁ : x.val.1=1 := hx
  have hw₁ : wordUnit A hs hp b₀ s₀ K w=1 := (congrArg Prod.fst hw).trans hx₁
  have hw₂ := wordLinear_eq_one_of_wordUnit_eq_one A hd hs hp ho K w hw₁
  apply Prod.ext
  · exact hx₁
  · exact (congrArg Prod.snd hw).symm.trans hw₂

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylDegreeFaithful
