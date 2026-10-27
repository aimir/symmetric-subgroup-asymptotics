import SymmetricSubgroupAsymptotics.ActualFullWreathSimpleKernelFibreCount
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Literal local-quotient specialization. N can be the actual local socle
(or a chosen actual homogeneous minimal normal subgroup). Its genuine
product chart is retained; no abstract model is substituted for N. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathSemisimpleQuotientFibreCount

variable {R Q I J T : Type} [Group R] [Group Q] [MulAction Q I]
    [Group T] [Finite T] [IsSimpleGroup T] [Fintype J]
    (N : Subgroup R) [N.Normal] (eN : N ≃* (J → T))

def quotientKernelChart : (QuotientGroup.mk' N).ker ≃* (J → T) :=
  (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N)).trans eN

include eN in
theorem card_fibre_le [Finite R] [Finite Q] [Finite I] (hZ : IsCenterless T)
    (H : ActualFullWreathFamily.Family (R ⧸ N) Q I) {d : ℕ}
    (f : Fin d → H.val) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (ActualFullWreathSimpleKernelFibreCount.Fibre (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) H)≤
      (2^(Nat.card I * Nat.card J) *
        (2*(1+(Nat.card I * Nat.card J)*Nat.card (T ≃* T)))^(Nat.card I * Nat.card J))*
        Nat.card T ^ ((Nat.card I * Nat.card J)*d) :=
  ActualFullWreathSimpleKernelFibreCount.card_fibre_le (QuotientGroup.mk' N)
    (quotientKernelChart N eN) hZ (QuotientGroup.mk'_surjective N) H f hf

end SymmetricSubgroupAsymptotics.ActualFullWreathSemisimpleQuotientFibreCount
