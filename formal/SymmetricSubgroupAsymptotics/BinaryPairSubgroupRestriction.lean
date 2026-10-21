import SymmetricSubgroupAsymptotics.BinaryPairFrames
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.RepresentationRestrictionSameVectors

/-! Restriction to an actual top subgroup preserves the physical pair
frame and its SAME full correlated kernel. No split lifts are assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

def restrictSource (V : Subgroup (Equiv.Perm X)) (hV : V ≤ U) : BinaryPairFrame V I where
  frame := F.frame
  top := F.top.comp (Subgroup.inclusion hV)
  intertwine v p := F.intertwine (Subgroup.inclusion hV v) p

theorem restrictSource_kernelSpace (V : Subgroup (Equiv.Perm X)) (hV : V ≤ U)
    (hkernel : (F.top.ker.map U.subtype) ≤ V) :
    (F.restrictSource V hV).kernelSpace = F.kernelSpace := by
  let R := F.restrictSource V hV
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    let k : F.top.ker := ⟨Subgroup.inclusion hV a.toMul.val, a.toMul.property⟩
    exact ⟨Additive.ofMul k, rfl⟩
  · rintro v ⟨a, rfl⟩
    have hv : ((a.toMul : F.top.ker) : U).val ∈ V :=
      hkernel ⟨a.toMul.val, a.toMul.property, rfl⟩
    let k : R.top.ker := ⟨⟨a.toMul.val.val, hv⟩, by
      change F.top (Subgroup.inclusion hV ⟨a.toMul.val.val, hv⟩) = 1
      exact a.toMul.property⟩
    exact ⟨Additive.ofMul k, rfl⟩

def topSubgroupPreimage (H : Subgroup (Equiv.Perm I)) : Subgroup (Equiv.Perm X) :=
  (H.comap F.top).map U.subtype

theorem topSubgroupPreimage_le (H : Subgroup (Equiv.Perm I)) :
    F.topSubgroupPreimage H ≤ U := by
  rintro p ⟨u, _, rfl⟩
  exact u.property

theorem kernel_le_topSubgroupPreimage (H : Subgroup (Equiv.Perm I)) :
    F.top.ker.map U.subtype ≤ F.topSubgroupPreimage H := by
  rintro p ⟨u, hu, rfl⟩
  refine ⟨u, ?_, rfl⟩
  change F.top u ∈ H
  rw [show F.top u = 1 from hu]
  exact H.one_mem

def restrictTopSubgroup (H : Subgroup (Equiv.Perm I)) :
    BinaryPairFrame (F.topSubgroupPreimage H) I :=
  F.restrictSource (F.topSubgroupPreimage H) (F.topSubgroupPreimage_le H)

theorem restrictTopSubgroup_kernelSpace (H : Subgroup (Equiv.Perm I)) :
    (F.restrictTopSubgroup H).kernelSpace = F.kernelSpace :=
  F.restrictSource_kernelSpace _ _ (F.kernel_le_topSubgroupPreimage H)

theorem restrictTopSubgroup_range (H : Subgroup (Equiv.Perm I)) (hH : H ≤ F.top.range) :
    (F.restrictTopSubgroup H).top.range = H := by
  apply le_antisymm
  · rintro p ⟨v, rfl⟩
    obtain ⟨u, hu, he⟩ := v.property
    have he' : Subgroup.inclusion (F.topSubgroupPreimage_le H) v = u :=
      Subtype.ext he.symm
    change F.top (Subgroup.inclusion (F.topSubgroupPreimage_le H) v) ∈ H
    rw [he']
    exact hu
  · intro p hp
    obtain ⟨u, hu⟩ := hH hp
    have hv : u.val ∈ F.topSubgroupPreimage H := ⟨u, by change F.top u ∈ H; rw [hu]; exact hp, rfl⟩
    refine ⟨⟨u.val, hv⟩, ?_⟩
    change F.top (Subgroup.inclusion (F.topSubgroupPreimage_le H) ⟨u.val, hv⟩) = p
    exact hu

variable [Finite X] {w : ℕ} (E : BinaryPairFrame U (Fin w))

theorem naturalModuleHead_le_of_subgroup_pair_layer_bound
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : H ≤ E.top.range)
    (K : Submodule (ZMod 2) (Fin w → ZMod 2)) (hK : E.kernelSpace = K)
    (cap : ℕ)
    (hbound : ∀ S L : Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype),
      binaryCoordinateProductSpan K S.toSubmodule ≤ L.toSubmodule →
      Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
        Module.finrank (ZMod 2) (L.toSubmodule ⧸
          ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
            Representation.Coinvariants.ker L.toRepresentation)) ≤ cap)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ cap := by
  let V := E.topSubgroupPreimage H
  let j : V →* U := Subgroup.inclusion (E.topSubgroupPreimage_le H)
  let rho := permutationFunctionRepresentation (ZMod 2) U X
  let tau := permutationFunctionRepresentation (ZMod 2) V X
  have he (v : V) (x : X → ZMod 2) : rho (j v) x = tau v x := rfl
  let M := restrictionSameVectors rho tau j he W
  have hh := restrictionSameVectors_head_le rho tau j he W
  have hb := (E.restrictTopSubgroup H).naturalModuleHead_le_of_literal_pair_layer_bound
    H (E.restrictTopSubgroup_range H hH) K ((E.restrictTopSubgroup_kernelSpace H).trans hK)
    cap hbound M
  exact hh.trans hb

end SymmetricSubgroupAsymptotics.BinaryPairFrame
