import SymmetricSubgroupAsymptotics.OriginalKernelSocleActionKernel
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.NonPrimarySocleCoprimeQuotient
import SymmetricSubgroupAsymptotics.NormalGeneratorDisjointKernelImage
import SymmetricSubgroupAsymptotics.NormalGeneratorForcedKernelLift

/-! A cubic elementary kernel and its actual action kernel control the
WHOLE socle by coprime MAX sharing at ONE generator. The residual binary group itself need
not have a small socle: only its actual action kernel has order at most two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CubicKernelSocleFromOrderTwoActionKernel

private theorem normalGen_le_one_of_card_le_two
    {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hcard : Nat.card N≤2) : MarkedC4.normalGen N≤1 := by
  obtain ⟨S,hS,hsize⟩ := MarkedC4.exists_generating_finset_card_le N
  have htwo : S.card≤1 := by
    have hp : 2^S.card≤2^1 := hsize.trans hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hp
  let T := S.image N.subtype
  have hTN : (T : Set G)⊆N := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hcl : Subgroup.closure (T : Set G)=N := by
    have h := N.subtype.map_closure (S : Set N)
    have htop : (⊤ : Subgroup N).map N.subtype=N := by
      ext x
      constructor
      · rintro ⟨y,_,rfl⟩; exact y.property
      · intro hx; exact ⟨⟨x,hx⟩,Subgroup.mem_top _,rfl⟩
    rw [hS,htop] at h
    simpa only [T,Finset.coe_image] using h.symm
  have hncl : Subgroup.normalClosure (T : Set G)=N :=
    le_antisymm (Subgroup.normalClosure_le_normal hTN)
      (hcl ▸ Subgroup.closure_le_normalClosure)
  exact (MarkedC4.normalGen_le hTN hncl).trans (Finset.card_image_le.trans htwo)

/-- The hypotheses are actual module/action facts. In the monomial
application, cyclicity gives hu and the checked kernel injection gives hsmall.
No bound on arbitrary binary quotients is assumed. -/
theorem socle_one {G B : Type} [Group G] [Group B] [Finite G] [Finite B]
    (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 3) B) [FiniteDimensional (ZMod 3) A]
    (E : OriginalKernelModuleChart pi A)
    (hu : UniformSubrepresentationGeneratorBound A.ρ 1)
    (hcop : Nat.Coprime 3 (Nat.card B))
    (hsmall : Nat.card A.ρ.asGroupHom.ker≤2) : SocleNormalGeneratorBound G 1 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hker : IsPGroup 3 pi.ker :=
    (ZModModule.isPGroup_multiplicative (n := 3) (G := A)).of_surjective
      E.equiv.toMonoidHom E.equiv.surjective
  have hcop' : Nat.Coprime 3 (Nat.card (G ⧸ pi.ker)) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective pi hpi).toEquiv]
    exact hcop
  have hp := E.kernel_normalGen_le pi A hpi 1 hu
    (minimalNormalSoclePart G (fun M => IsPGroup 3 M))
    (CoprimeCyclicQuotientSocles.primarySocle_le 3 pi.ker hcop')
  let H := minimalNormalSoclePart G (fun M => ¬ IsPGroup 3 M)
  have hinf : H ⊓ pi.ker=⊥ :=
    NonPrimarySocleCoprimeQuotient.nonprimarySocle_inf_kernel_eq_bot 3 pi.ker hker hcop'
  have hle : H.map pi≤A.ρ.asGroupHom.ker :=
    (Subgroup.map_mono (minimalNormalSoclePart_le_finiteGroupSocle _ _)).trans
      (E.socle_map_le_actionKernel pi A)
  letI : (H.map pi).Normal := Subgroup.Normal.map inferInstance pi hpi
  have hc : Nat.card (H.map pi)≤2 := (Subgroup.card_le_of_le hle).trans hsmall
  have hother : MarkedC4.normalGen H≤1 :=
    (normalGen_le_image_of_disjoint_kernel pi hpi H hinf).trans
      (normalGen_le_one_of_card_le_two _ hc)
  apply (socleNormalGeneratorBound_iff_normalGen_le G 1).mpr
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 3 G).trans
    (max_le hp hother)

end SymmetricSubgroupAsymptotics.CubicKernelSocleFromOrderTwoActionKernel
