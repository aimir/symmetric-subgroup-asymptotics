import SymmetricSubgroupAsymptotics.NonabelianSimpleOrderAtLeastSixty
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding

/-! The actual full socle is perfect and embeds in A_n. For2≤n≤7,
its order is at most2520, whereas two simple factors would have order
at least3600. No global simple-index packet is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSevenPointSingleFactorWithoutIndexInput
open PrimitiveSocleRawStructure

theorem factorCount_eq_one {G : Type} [Group G] [Finite G] {n : ℕ}
    [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]
    (D : NonaffineData G (Fin n)) (hn : 2≤n) (hsmall : n≤7) : D.factorCount=1 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
  let coordinate (i : Fin D.factorCount) : finiteGroupSocle G →* D.Simple :=
    (Pi.evalMonoidHom (fun _ : Fin D.factorCount => D.Simple) i).comp D.socleEquiv.toMonoidHom
  have hcoordinate (i : Fin D.factorCount) : Function.Surjective (coordinate i) := by
    intro t
    refine ⟨D.socleEquiv.symm (fun _ => t),?_⟩
    change D.socleEquiv (D.socleEquiv.symm (fun _ => t)) i=t
    rw [D.socleEquiv.apply_symm_apply]
  letI : Group.IsPerfect (finiteGroupSocle G) :=
    perfect_of_subdirect (fun _ : Fin D.factorCount => D.Simple) (finiteGroupSocle G)
      coordinate hcoordinate (by
        intro x y h
        exact D.socleEquiv.injective h)
  let j := perfectPermutationToAlternating (MulAction.toPermHom (finiteGroupSocle G) (Fin n))
  have hj : Function.Injective j := perfectPermutationToAlternating_injective _
    (show Function.Injective (MulAction.toPermHom (finiteGroupSocle G) (Fin n)) from MulAction.toPerm_injective)
  have hAlt : Nat.card (alternatingGroup (Fin n))≤2520 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    exact (Nat.div_le_div_right (Nat.factorial_le hsmall)).trans (by decide)
  have hS : Nat.card D.Simple ^ D.factorCount≤2520 := by
    have hc : Nat.card (finiteGroupSocle G)=Nat.card D.Simple ^ D.factorCount := by
      rw [Nat.card_congr D.socleEquiv.toEquiv,Nat.card_fun,Nat.card_fin]
    rw [←hc]
    exact (Nat.card_le_card_of_injective j hj).trans hAlt
  have hT := NonabelianSimpleOrderAtLeastSixty.sixty_le_card D.Simple D.noncommutative
  have hpos := D.factorCount_pos
  by_contra hh
  have hk : 2≤D.factorCount := by omega
  have hl : 3600≤Nat.card D.Simple ^ D.factorCount := calc
    3600=60^2 := by decide
    _ ≤ Nat.card D.Simple ^ 2 := Nat.pow_le_pow_left hT 2
    _ ≤ Nat.card D.Simple ^ D.factorCount := pow_le_pow_right₀ (by omega) hk
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleSevenPointSingleFactorWithoutIndexInput
