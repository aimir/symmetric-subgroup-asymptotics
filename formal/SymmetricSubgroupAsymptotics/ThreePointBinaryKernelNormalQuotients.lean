import SymmetricSubgroupAsymptotics.SixPairThreePointNormalTop
import SymmetricSubgroupAsymptotics.OriginalKernelSmallTopQuotientCard

/-! Every nonbinary quotient of a binary extension of an actual transitive
three-point group retains the original coarse kernel. The denominator may
be any original normal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ThreePointBinaryKernelNormalQuotients
open OriginalKernelModuleChart

 theorem nonbinary_le_kernel {G : Type} [Group G] [Finite G]
    (B : Subgroup (Equiv.Perm (Fin 3))) [MulAction.IsPretransitive B (Fin 3)]
    (pi : G →* B) (hpi : Function.Surjective pi) (hK : IsPGroup 2 pi.ker)
    (N : Subgroup G) [N.Normal] (hQ : ¬IsPGroup 2 (G ⧸ N)) : N≤pi.ker := by
  by_contra hn
  have hm : N.map pi≠⊥ := fun hm => hn ((Subgroup.map_eq_bot_iff (H := N)).mp hm)
  letI : (N.map pi).Normal := (inferInstance : N.Normal).map pi hpi
  have hs := SixPairThreePointNormalTop.quotient_card_le_two B (N.map pi) hm
  let R := G ⧸ (pi.ker ⊔ N)
  let f : (G ⧸ N) →* R := base pi N
  have hc : Nat.card R≤2 := (residualTop_card_eq pi hpi N).le.trans hs
  have hr : IsPGroup 2 R := by
    have hp : 0<Nat.card R := Nat.card_pos
    by_cases h1 : Nat.card R=1
    · exact IsPGroup.of_card (n := 0) (by simpa using h1)
    · have h2 : Nat.card R=2 := by omega
      exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using h2)
  have hk : IsPGroup 2 f.ker :=
    hK.of_surjective (quotientKernelMap pi N) (quotientKernelMap_surjective pi N)
  have hh := (hr.to_subgroup (⊤ : Subgroup R)).comap_of_ker_isPGroup f hk
  have ht : IsPGroup 2 (⊤ : Subgroup (G ⧸ N)) := by
    simpa only [Subgroup.comap_top] using hh
  exact hQ (ht.of_equiv Subgroup.topEquiv)

end SymmetricSubgroupAsymptotics.ThreePointBinaryKernelNormalQuotients
