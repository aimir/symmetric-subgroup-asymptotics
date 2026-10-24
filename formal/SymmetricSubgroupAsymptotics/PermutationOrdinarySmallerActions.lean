import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Finite.Perm

/-! Strictly smaller-action induction for ordinary generators. The
three-point full symmetric exception is retained in the sharp induction
hypothesis and paid internally in the rounded consequence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions

/-- Only strictly smaller original point sets are covered, and degree
three is excluded from this sharp action-level interface. -/
def SmallerActionBound (n : ℕ) : Prop :=
  ∀(H Y : Type) [Group H] [Finite H] [Finite Y] [MulAction H Y] [FaithfulSMul H Y],
    Nat.card Y<n→Nat.card Y≠3→2*MarkedC4.genRank H≤Nat.card Y

/-- The interface follows from the literal sharp subgroup statement at
strictly smaller degrees; no bound at the current degree is assumed. -/
theorem smallerActionBound_of_subgroup_generators (n : ℕ)
    (hbelow : ∀(k : ℕ),k<n→∀J:Subgroup (Equiv.Perm (Fin k)),
      (k=3→J≠⊤)→∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤k) :
    SmallerActionBound n := by
  intro H Y _ _ _ _ _ hlt hthree
  let f : H→*Equiv.Perm (Fin (Nat.card Y)) :=
    (Finite.equivFin Y).permCongrHom.toMonoidHom.comp (MulAction.toPermHom H Y)
  have hf : Function.Injective f :=
    (Finite.equivFin Y).permCongrHom.injective.comp MulAction.toPerm_injective
  let e : H≃*f.range := MonoidHom.ofInjective (f:=f) hf
  obtain ⟨S,hgen,hcard⟩ := hbelow (Nat.card Y) hlt f.range
    (fun h=>(hthree h).elim)
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
  exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard

private theorem faithful_card_le_factorial (H Y : Type) [Group H] [Finite H] [Finite Y]
    [MulAction H Y] [FaithfulSMul H Y] : Nat.card H≤(Nat.card Y).factorial := by
  have h := Nat.card_le_card_of_injective (MulAction.toPermHom H Y)
    MulAction.toPerm_injective
  simpa only [Nat.card_perm] using h

/-- Rounded smaller-action generation includes the full S3. Its actual
order six forces at most two ordinary generators. -/
theorem rounded_rank_of_smaller (n : ℕ) (hbelow : SmallerActionBound n)
    (H Y : Type) [Group H] [Finite H] [Finite Y] [MulAction H Y] [FaithfulSMul H Y]
    (hlt : Nat.card Y<n) : 2*MarkedC4.genRank H≤Nat.card Y+1 := by
  by_cases hthree:Nat.card Y=3
  · have hcard : Nat.card H≤6 := by
      simpa only [hthree] using faithful_card_le_factorial H Y
    have hrank : MarkedC4.genRank H≤2 := by
      by_contra h
      have hh : 3≤MarkedC4.genRank H := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0<2) hh).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card H).trans hcard)
      norm_num at hp
    omega
  · exact (hbelow H Y hlt hthree).trans (Nat.le_succ _)

end SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions
