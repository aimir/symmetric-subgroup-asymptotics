import SymmetricSubgroupAsymptotics.SixPairBinaryQuotientKernelBound
import SymmetricSubgroupAsymptotics.TransitiveSixBinaryQuotientCard
import SymmetricSubgroupAsymptotics.BinaryPairZeroCutExtension
import SymmetricSubgroupAsymptotics.BinaryPairSectionCocycleBound
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! Every binary ORIGINAL quotient of a transitive six-pair action has
order at most32: its exact surviving kernel has at most4 elements and
its exact top quotient has at most8. No catalogue or classification is
used, and every literal normal denominator is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 6))
    [MulAction U (Fin 6)] [MulAction.IsPretransitive U (Fin 6)]
    (hact : ∀ (u : U) (i : Fin 6), u • i = F.top u i)
    (N : Subgroup U) [N.Normal]

include hact in
/-- This bound concerns U/N itself, not its abelianization or image in
a separately chosen model. -/
theorem binary_quotient_card_le_thirtyTwo
    (hQ : IsPGroup 2 (U ⧸ N)) : Nat.card (U ⧸ N) ≤ 32 := by
  let T := F.top.range
  let D := U ⧸ (F.top.ker ⊔ N)
  let f := F.zeroCutBase N
  have hf : Function.Surjective f := F.zeroCutBase_surjective N
  have hD : IsPGroup 2 D := hQ.of_surjective f hf
  letI : MulAction.IsPretransitive T (Fin 6) := ⟨by
    intro i j
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq U i j
    refine ⟨F.top.rangeRestrict u,?_⟩
    change F.top u i = j
    rw [← hact]
    exact hu⟩
  have hd : Nat.card D ≤ 8 :=
    transitiveSix_binary_epimorphism_card_le_eight
      (F.sectionTopQuotient N) (F.sectionTopQuotient_surjective N) hD
  have hk : Nat.card f.ker ≤ 4 := by
    have he : Nat.card f.ker = Nat.card (F.kernelSpace ⧸ F.normalSpace N) := by
      calc
        Nat.card f.ker = Nat.card (Multiplicative (F.zeroCutModule N)) :=
          Nat.card_congr (F.zeroCutKernelEquiv N).symm.toEquiv
        _ = Nat.card (F.zeroCutModule N) := Nat.card_congr Multiplicative.toAdd
        _ = Nat.card (F.kernelSpace ⧸ F.normalSpace N) :=
          Nat.card_congr (F.zeroCutSectionEquiv N).toLinearEquiv.toEquiv
    rw [he]
    exact F.binary_quotient_kernel_section_card_le_four hact N hQ
  have hp := f.ker.card_mul_index
  rw [Subgroup.index_ker,f.range_eq_top_of_surjective hf,Subgroup.card_top] at hp
  have hm := Nat.mul_le_mul hk hd
  change Nat.card f.ker * Nat.card D ≤ 4*8 at hm
  have hcard : Nat.card f.ker * Nat.card D = Nat.card (U ⧸ N) := hp
  calc
    Nat.card (U ⧸ N) = Nat.card f.ker * Nat.card D := hcard.symm
    _ ≤ 4*8 := hm
    _ = 32 := rfl

include hact in
/-- Every binary target cell is automatic for an actual six-pair action. -/
def binary_quotient_B6_certificate (hQ : IsPGroup 2 (U ⧸ N)) :
    PreE7B6QuotientCertificate (U ⧸ N) :=
  .binary hQ (F.binary_quotient_card_le_thirtyTwo hact N hQ)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
end
