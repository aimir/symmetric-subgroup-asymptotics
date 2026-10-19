import SymmetricSubgroupAsymptotics.BinaryBySymmetricThreeSocleOne
import SymmetricSubgroupAsymptotics.TransitiveThreeBinaryNaturalUniform
import SymmetricSubgroupAsymptotics.BinaryPairUniformQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocleBounds

/-! Every retained original denominator in the full symmetric coarse-top
branch has a normally cyclic socle. Binary and odd socle parts share one
position; no splitting of the original pair extension is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPointThreePairSymmetricRetainedSocles

variable {T : Subgroup (Equiv.Perm (Fin 6))} (E : BinaryPairFrame T (Fin 3))

include E in
 theorem quotient [MulAction.IsPretransitive T (Fin 6)]
    (honto : Function.Surjective E.top) (N : Subgroup T) [N.Normal]
    (hN : N≤E.top.ker) : SocleNormalGeneratorBound (T ⧸ N) 1 := by
  let q := QuotientGroup.mk' N
  let beta : (T ⧸ N) →* Equiv.Perm (Fin 3) := QuotientGroup.lift N E.top hN
  have hb (g : T) : beta (q g)=E.top g := rfl
  have hbeta : Function.Surjective beta := by
    intro x
    obtain ⟨g,rfl⟩ := honto x
    exact ⟨q g,hb g⟩
  have hker : beta.ker=E.top.ker.map q := by
    apply le_antisymm
    · intro y hy
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N y
      exact ⟨g,hy,rfl⟩
    · rintro y ⟨g,hg,rfl⟩
      exact hg
  have hbinary : IsPGroup 2 beta.ker := by
    rw [hker]
    exact E.kernel_isPGroup.map q
  letI : MulAction.IsPretransitive E.top.range (Fin 3) := E.top_pretransitive
  have hu := E.elementaryKernelChart_uniform 1
    (transitiveThree_binary_natural_uniform_one E.top.range)
  have hg (H : Subgroup T) (hH : H.Normal) (hHE : H≤E.top.ker) :
      MarkedC4.normalGen H≤1 := by
    letI := hH
    exact ElementaryUniformNormalGenerators.kernel_normalGen_le E.top.ker
      E.elementaryKernelChart 1 hu H hHE
  have hgen (H : Subgroup (T ⧸ N)) (hH : H.Normal) (hle : H≤beta.ker) :
      MarkedC4.normalGen H≤1 := by
    letI := hH
    apply CoprimeCyclicQuotientSocleBounds.image_normalGen_le q
      (QuotientGroup.mk'_surjective N) E.top.ker 1 hg H
    exact hle.trans_eq hker
  obtain ⟨a,ha⟩ := hbinary.exists_card_eq
  have hquot : Nat.card ((T ⧸ N) ⧸ beta.ker)=6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective beta hbeta).toEquiv]
    norm_num [Fintype.card_perm,Fintype.card_fin]
  have hcard : Nat.card (T ⧸ N)∣2^(a+1)*3 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup beta.ker
    rw [hquot,ha] at hc
    have heq : Nat.card (T ⧸ N)=2^(a+1)*3 := by
      rw [hc,pow_succ]
      ring
    exact heq ▸ dvd_rfl
  exact BinaryBySymmetricThreeSocleOne.socle_one beta hbeta hbinary hcard hgen

end SymmetricSubgroupAsymptotics.SixPointThreePairSymmetricRetainedSocles
