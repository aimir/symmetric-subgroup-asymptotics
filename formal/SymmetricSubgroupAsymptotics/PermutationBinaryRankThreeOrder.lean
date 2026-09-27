import SymmetricSubgroupAsymptotics.BinaryCoverage
import SymmetricSubgroupAsymptotics.CentralTwoPairFrame
import SymmetricSubgroupAsymptotics.BinaryPairRankThreeSection
import SymmetricSubgroupAsymptotics.BinaryPairFixedLiftKernel
import SymmetricSubgroupAsymptotics.PermutationBinaryFourImage

/-! The original eight-point rank-three residual has small original
source order whenever its actual section action is nonfaithful. All pair
coordinates are constructed from a central subgroup of its actual action
kernel. The original correlated subspaces and original quotient remain
unchanged throughout the argument. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {X : Type} {G : Subgroup (Equiv.Perm X)}
    (M L : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))

/-- The actual section, before any auxiliary pair frame is chosen. -/
def originalPermutationSection : Representation (ZMod 2) G
    (M.toSubmodule ⧸ L.toSubmodule.comap M.toSubmodule.subtype) :=
  M.toRepresentation.quotient (L.toSubmodule.comap M.toSubmodule.subtype)
    (fun g _ hv => L.apply_mem_toSubmodule g hv)

/-- The maximal four-dimensional section with three fixed directions
forces the SAME original eight-point group to have order at most eight
and its original correlated submodule to have dimension five. -/
theorem permutationBinary_rankThree_nonfaithful_order
    [Finite X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (x : X) (hX : Nat.card X=8)
    (hLM : L.toSubmodule≤M.toSubmodule)
    (hd : Module.finrank (ZMod 2)
      (M.toSubmodule ⧸ L.toSubmodule.comap M.toSubmodule.subtype)=4)
    (ht : Module.finrank (ZMod 2) (originalPermutationSection M L).invariants=3)
    (hne : ¬Function.Injective (originalPermutationSection M L)) :
    Nat.card G≤8 ∧ Module.finrank (ZMod 2) M.toSubmodule=5 := by
  let σ := originalPermutationSection M L
  have hker : σ.ker≠⊥ := by
    intro h
    exact hne ((MonoidHom.ker_eq_bot_iff σ).mp h)
  obtain ⟨z,hzker,hzcenter,hzorder⟩ := pGroup_normal_contains_central_prime hG σ.ker hker
  let C : Subgroup G := Subgroup.zpowers z
  have hCcenter : C≤Subgroup.center G := Subgroup.zpowers_le.mpr hzcenter
  have hCcard : Nat.card C=2 := (Nat.card_zpowers z).trans hzorder
  letI : C.Normal := ⟨fun a ha b => by
    simpa only [Subgroup.mem_center_iff.mp (hCcenter ha) b,mul_inv_cancel_right] using ha⟩
  have hz_ne : z≠1 := by
    intro h
    rw [h,orderOf_one] at hzorder
    omega
  let Y := CentralTwoPairFrame.Points G C x
  let F : BinaryPairFrame G Y := CentralTwoPairFrame.frame G C x hCcenter hCcard
  letI : MulAction.IsPretransitive G Y := ⟨by
    intro a b
    obtain ⟨u,hu⟩ := a.property
    obtain ⟨v,hv⟩ := b.property
    refine ⟨v*u⁻¹,Subtype.ext ?_⟩
    change u • MulAction.orbit C x=(a:Set X) at hu
    change v • MulAction.orbit C x=(b:Set X) at hv
    change (v*u⁻¹) • (a:Set X)=(b:Set X)
    rw [← hu,← hv,mul_smul,inv_smul_smul]⟩
  have hY : Nat.card Y=4 := CentralTwoPairFrame.points_card_four G C x hCcenter hCcard hX
  let i : Y := CentralTwoPairFrame.pointMap G C x x
  have hact : ∀ (u : G) (j : Y), u • j=F.top u j := fun _ _ => rfl
  let zC : C := ⟨z,Subgroup.mem_zpowers z⟩
  let zF : F.top.ker :=
    ⟨z,CentralTwoPairFrame.kernel_le G C x hCcenter hCcard zC.property⟩
  have hbits : ∀ j, F.bits zF j=1 := by
    intro j
    exact CentralTwoPairFrame.bits_one G C x hCcenter hCcard zC
      (fun h => hz_ne (congrArg Subtype.val h)) j
  have htrivial : ∀ f ∈ M.toSubmodule,
      permutationFunctionRepresentation (ZMod 2) G X (zF:G) f-f∈L.toSubmodule := by
    intro f hf
    let m : M.toSubmodule := ⟨f,hf⟩
    have h := LinearMap.congr_fun (show σ z=1 from hzker)
      ((L.toSubmodule.comap M.toSubmodule.subtype).mkQ m)
    change (L.toSubmodule.comap M.toSubmodule.subtype).mkQ (M.toRepresentation z m)=
      (L.toSubmodule.comap M.toSubmodule.subtype).mkQ m at h
    have hzq : (L.toSubmodule.comap M.toSubmodule.subtype).mkQ
        (M.toRepresentation z m-m)=0 := by
      rw [map_sub,h,sub_self]
    exact (Submodule.Quotient.mk_eq_zero
      (L.toSubmodule.comap M.toSubmodule.subtype)).mp hzq
  obtain ⟨hW,hLeq,hL,_⟩ := F.maximal_pair_section zF hbits M.toSubmodule L.toSubmodule
    hLM htrivial (by rw [hd,hY])
  have himage : M.toSubmodule.map F.pairDelta≤L.toSubmodule := hLeq.ge
  have hthree : 3≤Module.finrank (ZMod 2) (F.pairSectionRepresentation M L).invariants := by
    change 3≤Module.finrank (ZMod 2) (originalPermutationSection M L).invariants
    rw [ht]
  obtain ⟨hLdim,hS,hq⟩ := F.pair_rank_three_boundary hact M L hW hL himage hG i hY hthree
  have hconstant := F.pair_rank_three_denominator_eq_constants hact M L hW hL himage
    hG x i hY hthree
  obtain ⟨m,hm,hfixedL⟩ := F.pair_rank_three_exists_fixed_lift hact M L hW hL himage
    hG i hY hthree
  have hfixed : ∀ u : G, permutationFunctionRepresentation (ZMod 2) G X u m.1-m.1∈
      (permutationFunctionRepresentation (ZMod 2) G X).invariants := by
    intro u
    rw [← hconstant]
    exact hfixedL u
  have hqmax : Module.finrank (ZMod 2)
      (centralQuotientRepresentation (permutationFunctionRepresentation (ZMod 2) G Y)
        (permutationFunctionRepresentation (ZMod 2) G Y).invariants le_rfl).invariants=2 := by
    have htransport (S : Submodule (ZMod 2) (Y → ZMod 2))
        (hstable : ∀ g : G, S≤S.comap
          (permutationFunctionRepresentation (ZMod 2) G Y g))
        (he : S=(permutationFunctionRepresentation (ZMod 2) G Y).invariants) :
        Module.finrank (ZMod 2)
          ((permutationFunctionRepresentation (ZMod 2) G Y).quotient S hstable).invariants=
        Module.finrank (ZMod 2)
          (centralQuotientRepresentation (permutationFunctionRepresentation (ZMod 2) G Y)
            (permutationFunctionRepresentation (ZMod 2) G Y).invariants le_rfl).invariants := by
      subst S
      rfl
    have heq := htransport (F.pairImageSubrepresentation hact L).toSubmodule
      (fun g => (F.pairImageSubrepresentation hact L).apply_mem_toSubmodule g) hS
    exact heq.symm.trans hq
  have htop : Nat.card F.top.range=4 := by
    have h := PermutationBinaryFourRegular.image_card_eq_degree_of_maximal_fixed_quotient
      (G := G) i 2 (by simpa using hY) hqmax
    exact h
  refine ⟨F.card_le_eight_of_fixed_lift m.1 hm hfixed i htop,?_⟩
  have hdim := (L.toSubmodule.comap M.toSubmodule.subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hLM).finrank_eq,hd,hLdim] at hdim
  omega

end SymmetricSubgroupAsymptotics
