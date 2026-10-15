import SymmetricSubgroupAsymptotics.TwoMinimalNormalQuotientSocles
import SymmetricSubgroupAsymptotics.TernaryCentralComplementSocles
import SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSocles

/-! The scalar-diagonal quotients needed by the full four-block modules.
For A4 times D3 the two literal minimal cores are separated by the first
factor. Every nontrivial normal kills one of those cores, reducing to the
checked quotients C3 times D3 and A4 times C2. S4 times D3 uses the uniform
two-position bound from its two actual normal chains. -/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.TernaryScalarComplementSocles

open Non2UnipotentPrefixFiniteMenu.CentralBinaryProductModels
open TernaryCentralComplementSocles

abbrev A4 := NaturalA4ScalarFourHead.G
abbrev Model := A4 × D3

def firstQuotient : Model →* C3 × D3 :=
  NaturalA4ScalarFourHead.top.prodMap (MonoidHom.id D3)

def secondQuotient : Model →* A4 × C2 :=
  (MonoidHom.id A4).prodMap (DihedralNormalGenerators.parity 3)

theorem firstQuotient_surjective : Function.Surjective firstQuotient := by
  intro x
  obtain ⟨a,ha⟩ := NaturalA4ScalarFourHead.top_surjective x.1
  exact ⟨(a,x.2),Prod.ext ha rfl⟩

theorem parity_surjective : Function.Surjective (DihedralNormalGenerators.parity 3) := by
  intro z
  have hz : z = 1 ∨ z = Multiplicative.ofAdd 1 :=
    (show ∀ z : C2, z = 1 ∨ z = Multiplicative.ofAdd 1 by decide +kernel) z
  rcases hz with hz | hz
  · exact ⟨DihedralGroup.r 0,hz.symm⟩
  · exact ⟨DihedralGroup.sr 0,hz.symm⟩

theorem secondQuotient_surjective : Function.Surjective secondQuotient := by
  intro x
  obtain ⟨d,hd⟩ := parity_surjective x.2
  exact ⟨(x.1,d),Prod.ext rfl hd⟩

theorem firstQuotient_ker : firstQuotient.ker = a4Core.productCore D3 := by
  ext x
  change (NaturalA4ScalarFourHead.top x.1,x.2) = 1 ↔ x.1 ∈ a4Core.V ∧ x.2 = 1
  rw [a4Core_eq_topKernel,MonoidHom.mem_ker]
  exact Prod.ext_iff

theorem mem_secondQuotient_ker (x : Model) :
    x ∈ secondQuotient.ker ↔ x.1 = 1 ∧ x.2 ∈ rotationCore.V := by
  change (x.1,DihedralNormalGenerators.parity 3 x.2) = 1 ↔
    x.1 = 1 ∧ DihedralNormalGenerators.parity 3 x.2 = 1
  exact Prod.ext_iff

private theorem productCore_minimal
    {L C : Type} [Group L] [Group C]
    (D : CentralBinaryProductCore L) (hD : D.V ≠ ⊥) :
    IsMinimalNormalSubgroup (D.productCore C) := by
  have hne : D.productCore C ≠ ⊥ := by
    obtain ⟨v,hv,hvne⟩ := D.V.bot_or_exists_ne_one.resolve_left hD
    intro h
    have hm : (v,(1 : C)) ∈ D.productCore C := (D.mem_productCore C _).mpr ⟨hv,rfl⟩
    rw [h] at hm
    exact hvne (congrArg Prod.fst (Subgroup.mem_bot.mp hm))
  exact ⟨inferInstance,hne,fun W hW hWne hWD =>
    (D.productCore_minimal C W hW hWD).resolve_left hWne⟩

theorem first_kernel_minimal : IsMinimalNormalSubgroup firstQuotient.ker := by
  rw [firstQuotient_ker]
  apply productCore_minimal a4Core
  rw [a4Core_eq_topKernel,NaturalA4ScalarFourHead.top_ker]
  intro h
  have hcard := alternatingGroup.kleinFour_card_of_card_eq_four
    (α := Fin 4) (by simp)
  rw [h] at hcard
  norm_num at hcard

theorem second_kernel_minimal : IsMinimalNormalSubgroup secondQuotient.ker := by
  let e : D3 × A4 ≃* Model := MulEquiv.prodComm
  have he : e.mapSubgroup (rotationCore.productCore A4) = secondQuotient.ker := by
    ext x
    change x ∈ (rotationCore.productCore A4).map e.toMonoidHom ↔ x ∈ secondQuotient.ker
    rw [mem_secondQuotient_ker]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨((rotationCore.mem_productCore A4 y).mp hy).2,
        ((rotationCore.mem_productCore A4 y).mp hy).1⟩
    · rintro ⟨hfirst,hsecond⟩
      exact ⟨(x.2,x.1),(rotationCore.mem_productCore A4 _).mpr ⟨hsecond,hfirst⟩,rfl⟩
  rw [← he]
  exact CyclicSocleQuotientTools.minimal_map_equiv e _
    (productCore_minimal rotationCore rotationCore_ne_bot)

theorem two_kernel_cover (N : Subgroup Model) (hN : N.Normal) (hNb : N ≠ ⊥) :
    firstQuotient.ker ≤ N ∨ secondQuotient.ker ≤ N := by
  rcases a4Core.normal_contains_productCore_or_le_productCentral D3 N hN with ha | hb
  · exact Or.inl (by rw [firstQuotient_ker]; exact ha)
  · right
    let pi : Model →* D3 := MonoidHom.snd A4 D3
    have hM : (N.map pi).Normal := hN.map pi Prod.snd_surjective
    have hMb : N.map pi ≠ ⊥ := by
      intro h
      apply hNb
      apply le_antisymm _ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Prod.ext
      · exact (a4Core.mem_productCentral D3 x).mp (hb hx)
      · have hm : x.2 ∈ N.map pi := ⟨x,hx,rfl⟩
        rw [h] at hm
        exact Subgroup.mem_bot.mp hm
    obtain ⟨d,hd,hdne⟩ := (N.map pi).bot_or_exists_ne_one.resolve_left hMb
    have hrot : rotationCore.V ≤ N.map pi := by
      change (DihedralNormalGenerators.parity 3).ker ≤ N.map pi
      rw [DihedralNormalGenerators.parity_ker]
      exact Subgroup.zpowers_le.mpr
        (OddPrimeDihedralNormalChain.rotation_mem_of_ne_one (by decide) _ hM d hd hdne)
    intro x hx
    obtain ⟨hx1,hx2⟩ := (mem_secondQuotient_ker x).mp hx
    obtain ⟨n,hn,he⟩ := hrot hx2
    have hn1 : n.1 = 1 := (a4Core.mem_productCentral D3 n).mp (hb hn)
    have hnx : n = x := Prod.ext (hn1.trans hx1.symm) he
    rwa [← hnx]

def firstAxis : Subgroup Model := (⊤ : Subgroup A4).prod ⊥

instance firstAxis_normal : firstAxis.Normal := by
  dsimp [firstAxis]
  infer_instance

theorem first_kernel_commutator : ⁅firstAxis,firstQuotient.ker⁆ = firstQuotient.ker := by
  apply first_kernel_minimal.2.2 _ inferInstance _ (Subgroup.commutator_le_right _ _)
  intro hzero
  apply first_kernel_minimal.2.1
  apply le_antisymm _ bot_le
  intro v hv
  have hvcore : v ∈ a4Core.productCore D3 := by rwa [← firstQuotient_ker]
  obtain ⟨hv1,hv2⟩ := (a4Core.mem_productCore D3 v).mp hvcore
  have hvzero : v.1 = 1 := by
    apply a4Core.noFixed v.1 hv1
    intro x
    have hx : (x,(1 : D3)) ∈ firstAxis := ⟨Subgroup.mem_top _,Subgroup.mem_bot.mpr rfl⟩
    have hm := Subgroup.commutator_mem_commutator hx hv
    rw [hzero] at hm
    have he := congrArg Prod.fst (Subgroup.mem_bot.mp hm)
    change x*v.1*x⁻¹*v.1⁻¹ = 1 at he
    calc
      x*v.1 = (x*v.1*x⁻¹*v.1⁻¹)*(v.1*x) := by group
      _ = v.1*x := by rw [he,one_mul]
  exact Subgroup.mem_bot.mpr (Prod.ext hvzero hv2)

theorem kernels_separated : NoCommonNormalQuotient firstQuotient.ker secondQuotient.ker := by
  apply noCommonNormalQuotient_of_commutator_full_central firstAxis
    _ _ first_kernel_commutator
  intro z hz
  have hz1 := ((mem_secondQuotient_ker z).mp hz).1
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hx2 : x.2 = 1 := Subgroup.mem_bot.mp hx.2
  apply Prod.ext
  · change x.1*z.1 = z.1*x.1
    simp only [hz1,mul_one,one_mul]
  · change x.2*z.2 = z.2*x.2
    simp only [hx2,mul_one,one_mul]

theorem ternary_dihedral_socle_of_surjective {X : Type} [Group X]
    (rho : C3 × D3 →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X 1 := by
  let e : D3 × C3 ≃* C3 × D3 := MulEquiv.prodComm
  let f := rho.comp e.toMonoidHom
  have hf : Function.Surjective f := hrho.comp e.surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
    (quotientSocleNormalGeneratorBound_of_normal_generating_tuples
      dihedral_product_normal_singletons f.ker)

theorem alternating_dihedral_socle_of_surjective {X : Type} [Group X]
    (rho : Model →* X) (hrho : Function.Surjective rho) : SocleNormalGeneratorBound X 1 := by
  apply TwoMinimalNormalQuotientSocles.socle_of_surjective
    firstQuotient firstQuotient_surjective secondQuotient secondQuotient_surjective
    first_kernel_minimal second_kernel_minimal two_kernel_cover kernels_separated
    (by decide) _ _ rho hrho
  · intro N hN
    letI := hN
    exact ternary_dihedral_socle_of_surjective
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  · intro N hN
    letI := hN
    exact AlternatingFourCentralTwoSocles.socle_of_surjective
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem symmetric_dihedral_socle_of_surjective {X : Type} [Group X]
    (rho : Equiv.Perm (Fin 4) × D3 →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X 2 :=
  CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective rho hrho)
    (quotientSocle_of_product_normal_generators
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.symmetric_normal_total)
      (OddPrimeDihedralNormalChain.normal_generating_singletons (by decide)) rho.ker)

end SymmetricSubgroupAsymptotics.TernaryScalarComplementSocles

end
