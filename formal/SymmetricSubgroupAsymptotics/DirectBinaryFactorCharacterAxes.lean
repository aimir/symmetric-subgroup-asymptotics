import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFiniteNormalImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCharacterOnlySource
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Every original quotient of H × C2 has one general character, or one
binary linear character and one general character, whenever every original
quotient of H has a one-generator socle. Denominators meeting C2 are handled
by an actual surjection from H, not by falsely retaining a split factor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.DirectBinaryFactorCharacterAxes
open Non2UnipotentPrefixFiniteMenu
abbrev Bit := Multiplicative (ZMod 2)
private theorem nonone_equal : ∀ a b : Bit,a ≠ 1 → b ≠ 1 → a=b := by decide +kernel
variable {H : Type} [Group H] [Finite H]

/-- This consumes actual all-normal socle bounds on H, rather than a final
source or a per-epimorphism counting premise. -/
def axis
    (hH : ∀ (M : Subgroup H) [M.Normal], SocleNormalGeneratorBound (H ⧸ M) 1)
    (N : Subgroup (H × Bit)) [N.Normal] :
    PreE7B6CharacterAxisData ((H × Bit) ⧸ N) := by
  apply Classical.choice
  let fst : H × Bit →* H := MonoidHom.fst H Bit
  let snd : H × Bit →* Bit := MonoidHom.snd H Bit
  let q := QuotientGroup.mk' N
  by_cases hN : N ≤ snd.ker
  · let M := N.map fst
    letI : M.Normal := (inferInstance : N.Normal).map fst Prod.fst_surjective
    let psi : H × Bit →* H ⧸ M := (QuotientGroup.mk' M).comp fst
    have hpsi : N ≤ psi.ker := by
      intro g hg
      exact (QuotientGroup.eq_one_iff g.1).mpr ⟨g,hg,rfl⟩
    let f : ((H × Bit) ⧸ N) →* H ⧸ M := QuotientGroup.lift N psi hpsi
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective M x
      exact ⟨q (h,1),rfl⟩
    let bit : ((H × Bit) ⧸ N) →* Bit := QuotientGroup.lift N snd hN
    let chi := binaryComplexUnitSign.comp bit
    have hgeneral : SocleNormalGeneratorBound (((H × Bit) ⧸ N) ⧸ f.ker) 1 :=
      CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (hH M)
    have hcommon : chi.ker ⊓ f.ker=⊥ := by
      apply le_bot_iff.mp
      intro x hx
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
      have hs : g.2=1 := by
        have hh := hx.1
        change binaryComplexUnitSign g.2=1 at hh
        exact (binaryComplexUnitSign_eq_one g.2).mp hh
      have hm : g.1∈M := by
        have hh := hx.2
        change QuotientGroup.mk' M g.1=1 at hh
        exact (QuotientGroup.eq_one_iff g.1).mp hh
      obtain ⟨n,hn,he⟩ := hm
      have hn2 : n.2=1 := hN hn
      have hgn : g=n := Prod.ext he.symm (hs.trans hn2.symm)
      exact (QuotientGroup.eq_one_iff g).mpr (hgn.symm ▸ hn)
    let D : LinearZmudCharacterPairData ((H × Bit) ⧸ N) :=
      { linear := chi
        generalKernel := f.ker
        generalSocleGenerator := hgeneral
        kernel_inf := hcommon }
    exact ⟨.linearGeneral D⟩
  · obtain ⟨n,hn,hnbit⟩ := SetLike.not_le_iff_exists.mp hN
    have hn2 : n.2 ≠ 1 := hnbit
    let f : H →* (H × Bit) ⧸ N := q.comp (MonoidHom.inl H Bit)
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
      by_cases hg : g.2=1
      · refine ⟨g.1,?_⟩
        change q (g.1,1)=q g
        exact congrArg q (Prod.ext rfl hg.symm)
      · refine ⟨g.1*n.1⁻¹,?_⟩
        have hs : g.2=n.2 := nonone_equal g.2 n.2 hg hn2
        have he : g=(g.1*n.1⁻¹,1)*n := by
          apply Prod.ext
          · change g.1=(g.1*n.1⁻¹)*n.1
            group
          · simpa using hs
        have hqn : q n=1 := (QuotientGroup.eq_one_iff n).mpr hn
        change q (g.1*n.1⁻¹,1)=q g
        calc
          q (g.1*n.1⁻¹,1) = q (g.1*n.1⁻¹,1)*q n := by rw [hqn,mul_one]
          _ = q ((g.1*n.1⁻¹,1)*n) := (q.map_mul _ _).symm
          _ = q g := congrArg q he.symm
    have hgeneral : SocleNormalGeneratorBound ((H × Bit) ⧸ N) 1 :=
      CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf) (hH f.ker)
    exact ⟨.oneGeneral hgeneral⟩

end SymmetricSubgroupAsymptotics.DirectBinaryFactorCharacterAxes
