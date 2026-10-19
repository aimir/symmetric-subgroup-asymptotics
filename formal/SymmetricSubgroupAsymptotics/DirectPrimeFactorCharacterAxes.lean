import SymmetricSubgroupAsymptotics.BinaryPrimaryLinearCharacter
import SymmetricSubgroupAsymptotics.CharacterAxisEquivTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCharacterOnlySource
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Every original quotient of H × C_p has one general character, or one
linear character and one general character, whenever every original
quotient of H has a one-generator socle. Denominators meeting C_p are handled
by an actual surjection from H, not by falsely retaining a split factor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.DirectPrimeFactorCharacterAxes
open Non2UnipotentPrefixFiniteMenu
variable (C : Type) [CommGroup C] [Finite C] [Fact (Nat.card C).Prime]

private theorem exists_faithful_linear : ∃ chi : C →* ℂˣ,Function.Injective chi := by
  letI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp
    (Fact.out : (Nat.card C).Prime).one_lt
  obtain ⟨c,hc⟩ := exists_ne (1 : C)
  letI : NeZero ((Monoid.exponent C : ℕ) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := C))⟩
  obtain ⟨chi,hchi⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity C ℂ hc
  have ht : chi.ker ≠ ⊤ := by
    intro h
    have hm : c∈chi.ker := by rw [h]; trivial
    exact hchi hm
  have hb : chi.ker=⊥ := (chi.ker.eq_bot_or_eq_top_of_prime_card).resolve_right ht
  exact ⟨chi,(MonoidHom.ker_eq_bot_iff chi).mp hb⟩

private def linear : C →* ℂˣ := Classical.choose (exists_faithful_linear C)
private theorem linear_injective : Function.Injective (linear C) :=
  Classical.choose_spec (exists_faithful_linear C)

variable {H : Type} [Group H] [Finite H]

/-- This consumes actual all-normal socle bounds on H, rather than a final
source or a per-epimorphism counting premise. -/
def axis
    (hH : ∀ (M : Subgroup H) [M.Normal], SocleNormalGeneratorBound (H ⧸ M) 1)
    (N : Subgroup (H × C)) [N.Normal] :
    PreE7B6CharacterAxisData ((H × C) ⧸ N) := by
  apply Classical.choice
  let fst : H × C →* H := MonoidHom.fst H C
  let snd : H × C →* C := MonoidHom.snd H C
  let q := QuotientGroup.mk' N
  by_cases hN : N ≤ snd.ker
  · let M := N.map fst
    letI : M.Normal := (inferInstance : N.Normal).map fst Prod.fst_surjective
    let psi : H × C →* H ⧸ M := (QuotientGroup.mk' M).comp fst
    have hpsi : N ≤ psi.ker := by
      intro g hg
      exact (QuotientGroup.eq_one_iff g.1).mpr ⟨g,hg,rfl⟩
    let f : ((H × C) ⧸ N) →* H ⧸ M := QuotientGroup.lift N psi hpsi
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective M x
      exact ⟨q (h,1),rfl⟩
    let bit : ((H × C) ⧸ N) →* C := QuotientGroup.lift N snd hN
    let chi := (linear C).comp bit
    have hgeneral : SocleNormalGeneratorBound (((H × C) ⧸ N) ⧸ f.ker) 1 :=
      CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (hH M)
    have hcommon : chi.ker ⊓ f.ker=⊥ := by
      apply le_bot_iff.mp
      intro x hx
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
      have hs : g.2=1 := by
        have hh := hx.1
        change linear C g.2=1 at hh
        exact linear_injective C (hh.trans (map_one (linear C)).symm)
      have hm : g.1∈M := by
        have hh := hx.2
        change QuotientGroup.mk' M g.1=1 at hh
        exact (QuotientGroup.eq_one_iff g.1).mp hh
      obtain ⟨n,hn,he⟩ := hm
      have hn2 : n.2=1 := hN hn
      have hgn : g=n := Prod.ext he.symm (hs.trans hn2.symm)
      exact (QuotientGroup.eq_one_iff g).mpr (hgn.symm ▸ hn)
    let D : LinearZmudCharacterPairData ((H × C) ⧸ N) :=
      { linear := chi
        generalKernel := f.ker
        generalSocleGenerator := hgeneral
        kernel_inf := hcommon }
    exact ⟨.linearGeneral D⟩
  · have hnmap : N.map snd ≠ ⊥ := by
      intro hm
      exact hN ((Subgroup.map_eq_bot_iff (H := N)).mp hm)
    have hfull : N.map snd=⊤ :=
      ((N.map snd).eq_bot_or_eq_top_of_prime_card).resolve_left hnmap
    let f : H →* (H × C) ⧸ N := q.comp (MonoidHom.inl H C)
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
      have hm : g.2∈N.map snd := by rw [hfull]; trivial
      obtain ⟨n,hn,hs⟩ := hm
      refine ⟨g.1*n.1⁻¹,?_⟩
      have he : g=(g.1*n.1⁻¹,1)*n := by
        apply Prod.ext
        · change g.1=(g.1*n.1⁻¹)*n.1
          group
        · change g.2=1*n.2
          simpa only [one_mul] using hs.symm
      have hqn : q n=1 := (QuotientGroup.eq_one_iff n).mpr hn
      change q (g.1*n.1⁻¹,1)=q g
      calc
        q (g.1*n.1⁻¹,1) = q (g.1*n.1⁻¹,1)*q n := by rw [hqn,mul_one]
        _ = q ((g.1*n.1⁻¹,1)*n) := (q.map_mul _ _).symm
        _ = q g := congrArg q he.symm
    have hgeneral : SocleNormalGeneratorBound ((H × C) ⧸ N) 1 :=
      CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf) (hH f.ker)
    exact ⟨.oneGeneral hgeneral⟩

/-- Every original normal quotient of an actual image retains its exact
kernel through the first isomorphism theorem. -/
def axis_of_surjective
    (hH : ∀ (M : Subgroup H) [M.Normal], SocleNormalGeneratorBound (H ⧸ M) 1)
    {Q : Type} [Group Q] (rho : H × C →* Q) (hrho : Function.Surjective rho)
    (N : Subgroup Q) [N.Normal] : PreE7B6CharacterAxisData (Q ⧸ N) :=
  let phi := (QuotientGroup.mk' N).comp rho
  (axis C hH phi.ker).mapEquiv
    (QuotientGroup.quotientKerEquivOfSurjective phi
      ((QuotientGroup.mk'_surjective N).comp hrho))

end SymmetricSubgroupAsymptotics.DirectPrimeFactorCharacterAxes
