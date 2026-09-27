import SymmetricSubgroupAsymptotics.BinaryPairMaximalExactSequence
import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection
import SymmetricSubgroupAsymptotics.RepresentationFixedExact

/-! The rank-three boundary for an actual four-pair maximal section.
The original denominator becomes the original constant line, and a fixed
quotient vector lifting its nonzero displacement is constructed. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
    [MulAction U I] (hact : ∀ (u : U) (i : I), u • i=F.top u i)
    (M L : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : F.pairConstant.range≤M.toSubmodule)
    (hL : L.toSubmodule≤F.pairConstant.range)
    (himage : M.toSubmodule.map F.pairDelta≤L.toSubmodule)

/-- The image coordinates identify the actual original L, not just its
dimension. -/
def pairImageEquiv : (F.pairImageSubrepresentation hact L).toSubmodule ≃ₗ[ZMod 2]
    L.toSubmodule := by
  let f : (F.pairImageSubrepresentation hact L).toSubmodule →ₗ[ZMod 2] L.toSubmodule := {
    toFun a := ⟨F.pairConstant a.1,a.2⟩
    map_add' a b := Subtype.ext (map_add F.pairConstant a.1 b.1)
    map_smul' c a := Subtype.ext (map_smul F.pairConstant c a.1) }
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    exact F.pairConstant_injective (congrArg Subtype.val hab)
  · intro l
    obtain ⟨a,ha⟩ := hL l.2
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change F.pairConstant a∈L
    rw [ha]
    exact l.2

variable [Finite X] [Finite I] [MulAction.IsPretransitive U I]

include hact hW hL himage

theorem pair_rank_three_boundary (hU : IsPGroup 2 U) (i : I) (hI : Nat.card I=4)
    (ht : 3≤Module.finrank (ZMod 2) (F.pairSectionRepresentation M L).invariants) :
    Module.finrank (ZMod 2) L.toSubmodule=1 ∧
      (F.pairImageSubrepresentation hact L).toSubmodule=
        (permutationFunctionRepresentation (ZMod 2) U I).invariants ∧
      Module.finrank (ZMod 2) (F.pairImageQuotientRepresentation hact L).invariants=2 := by
  have hb := RepresentationFixedExact.finrank_invariants_le_of_range_eq_ker
    (F.pairLeftIntertwiner hact M L hW) (F.pairRightIntertwiner hact M L hL himage)
    (F.pairLeftIntertwiner_injective hact M L hW) (F.pair_exact hact M L hW hL himage)
  have hbound : 3≤
      Module.finrank (ZMod 2) (F.pairImageSubrepresentation hact L).toRepresentation.invariants+
      Module.finrank (ZMod 2)
        (PermutationBinaryFourSection.quotientRepresentation (F.pairImageSubrepresentation hact L)).invariants := by
    change 3≤
      Module.finrank (ZMod 2) (F.pairImageSubrepresentation hact L).toRepresentation.invariants+
      Module.finrank (ZMod 2) (F.pairImageQuotientRepresentation hact L).invariants
    omega
  obtain ⟨hd,he,hq⟩ := PermutationBinaryFourSection.boundary_forces_constant_line
    (F.pairImageSubrepresentation hact L) hU i hI hbound
  refine ⟨?_,he,hq⟩
  rw [← (F.pairImageEquiv hact L hL).finrank_eq]
  exact hd

/-- The same original group fixes the entire actual denominator. -/
theorem pair_rank_three_denominator_eq_constants [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U) (x : X) (i : I) (hI : Nat.card I=4)
    (ht : 3≤Module.finrank (ZMod 2) (F.pairSectionRepresentation M L).invariants) :
    L.toSubmodule=(permutationFunctionRepresentation (ZMod 2) U X).invariants := by
  obtain ⟨hd,he,_⟩ := F.pair_rank_three_boundary hact M L hW hL himage hU i hI ht
  have hle : L.toSubmodule≤(permutationFunctionRepresentation (ZMod 2) U X).invariants := by
    intro l hl u
    obtain ⟨a,ha⟩ := hL hl
    have hsa : a∈(F.pairImageSubrepresentation hact L).toSubmodule := by
      change F.pairConstant a∈L
      rw [ha]
      exact hl
    rw [he] at hsa
    rw [← ha,F.pairConstant_action]
    apply congrArg F.pairConstant
    have hu := hsa u
    change (fun j => a (u⁻¹ • j))=a at hu
    simpa only [hact,map_inv] using hu
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [PermutationBinaryFourSection.invariants_finrank x,hd]

/-- Dimension equality proves the invariant map is onto; this is not a
general assertion that invariants preserve quotient surjections. -/
theorem pair_rank_three_fixed_right_surjective (hU : IsPGroup 2 U)
    (i : I) (hI : Nat.card I=4)
    (ht : 3≤Module.finrank (ZMod 2) (F.pairSectionRepresentation M L).invariants) :
    Function.Surjective (RepresentationFixedExact.fixedMap
      (F.pairRightIntertwiner hact M L hL himage)) := by
  obtain ⟨hd,_,hq⟩ := F.pair_rank_three_boundary hact M L hW hL himage hU i hI ht
  let left := F.pairLeftIntertwiner hact M L hW
  let right := F.pairRightIntertwiner hact M L hL himage
  have hexact := RepresentationFixedExact.fixedMap_range_eq_ker left right
    (F.pairLeftIntertwiner_injective hact M L hW) (F.pair_exact hact M L hW hL himage)
  have hirange := LinearMap.finrank_range_of_inj
    (RepresentationFixedExact.fixedMap_injective left
      (F.pairLeftIntertwiner_injective hact M L hW))
  have hrank := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2)
    (V := (F.pairSectionRepresentation M L).invariants)
    (V₂ := (F.pairImageSubrepresentation hact L).toRepresentation.invariants)
    (RepresentationFixedExact.fixedMap right)
  rw [← hexact,hirange] at hrank
  change Module.finrank (ZMod 2) (RepresentationFixedExact.fixedMap right).range+
    Module.finrank (ZMod 2) (F.pairImageQuotientRepresentation hact L).invariants=
      Module.finrank (ZMod 2) (F.pairSectionRepresentation M L).invariants at hrank
  have hs : Module.finrank (ZMod 2)
      (F.pairImageSubrepresentation hact L).toRepresentation.invariants≤1 :=
    PermutationBinaryFourSection.subrepresentation_invariants_le_one i
      (F.pairImageSubrepresentation hact L)
  apply LinearMap.range_eq_top.mp
  change (RepresentationFixedExact.fixedMap right).range=⊤
  apply Submodule.eq_of_le_of_finrank_le (K := ZMod 2)
    (V := (F.pairImageSubrepresentation hact L).toRepresentation.invariants)
    (S₁ := (RepresentationFixedExact.fixedMap right).range) (S₂ := ⊤) le_top
  rw [finrank_top]
  omega

/-- A fixed vector of the ORIGINAL quotient has a representative whose
displacement is the nonzero constant vector on the original pairs. -/
theorem pair_rank_three_exists_fixed_lift (hU : IsPGroup 2 U)
    (i : I) (hI : Nat.card I=4)
    (ht : 3≤Module.finrank (ZMod 2) (F.pairSectionRepresentation M L).invariants) :
    ∃ m : M.toSubmodule, F.pairSum m.1=(fun _ => 1) ∧
      ∀ u : U, permutationFunctionRepresentation (ZMod 2) U X u m.1-m.1∈L := by
  obtain ⟨_,he,_⟩ := F.pair_rank_three_boundary hact M L hW hL himage hU i hI ht
  have hone : (fun _ : I => (1:ZMod 2))∈
      (F.pairImageSubrepresentation hact L).toSubmodule := by
    rw [he]
    intro _
    rfl
  let a : (F.pairImageSubrepresentation hact L).toSubmodule := ⟨fun _ => 1,hone⟩
  have hafixed : a∈(F.pairImageSubrepresentation hact L).toRepresentation.invariants := by
    intro _
    apply Subtype.ext
    rfl
  obtain ⟨v,hv⟩ := F.pair_rank_three_fixed_right_surjective hact M L hW hL himage
    hU i hI ht ⟨a,hafixed⟩
  obtain ⟨m,hm⟩ := (F.pairSectionDenominator M L).mkQ_surjective v.1
  refine ⟨m,?_,?_⟩
  · have hh := congrArg
      (fun z : (F.pairImageSubrepresentation hact L).toRepresentation.invariants =>
        (z.1 : I → ZMod 2)) hv
    change (F.pairRightIntertwiner hact M L hL himage v.1 : I → ZMod 2)=(fun _ => 1) at hh
    rw [← hm] at hh
    exact hh
  · intro u
    have hh := v.2 u
    rw [← hm] at hh
    change (F.pairSectionDenominator M L).mkQ (M.toRepresentation u m)=
      (F.pairSectionDenominator M L).mkQ m at hh
    have hz : (F.pairSectionDenominator M L).mkQ (M.toRepresentation u m-m)=0 := by
      rw [map_sub,hh,sub_self]
    exact (Submodule.Quotient.mk_eq_zero (F.pairSectionDenominator M L)).mp hz

end SymmetricSubgroupAsymptotics.BinaryPairFrame
