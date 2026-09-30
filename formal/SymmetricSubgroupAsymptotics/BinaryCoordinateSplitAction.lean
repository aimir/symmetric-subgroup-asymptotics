import SymmetricSubgroupAsymptotics.BinaryPairAffineCoboundary
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-!
# Coordinate form of a split binary pair action

Relabelling a physical split action by its own pair frame removes every
irrelevant choice of original point labels.  The resulting subgroup depends
only on the literal top permutation subgroup and the retained correlated flip
module.  This is the reusable comparison interface for the three surviving
degree-sixteen split actions.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The zero-cocycle affine permutation on literal pair coordinates. -/
def binaryCoordinateAffinePermutation {I : Type}
    (t : Equiv.Perm I) (a : I → ZMod 2) : Equiv.Perm (I × ZMod 2) where
  toFun p := (t p.1,p.2+a (t p.1))
  invFun p := (t⁻¹ p.1,p.2-a p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- Relabel a binary coordinate function along a bijection of pair labels. -/
def binaryFunctionRelabel {I J : Type} (e : I ≃ J) :
    (I → ZMod 2) ≃ₗ[ZMod 2] (J → ZMod 2) where
  toFun a j := a (e.symm j)
  invFun a i := a (e i)
  left_inv a := by funext i; simp
  right_inv a := by funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transport a correlated flip module through the same label bijection. -/
def binaryRelabelModule {I J : Type} (e : I ≃ J)
    (M : Submodule (ZMod 2) (I → ZMod 2)) :
    Submodule (ZMod 2) (J → ZMod 2) :=
  M.map (binaryFunctionRelabel e).toLinearMap

/-- Relabel pair coordinates without changing their binary bit. -/
def binaryCoordinateRelabel {I J : Type} (e : I ≃ J) :
    I × ZMod 2 ≃ J × ZMod 2 :=
  Equiv.prodCongr e (Equiv.refl (ZMod 2))

theorem binaryCoordinateRelabel_permCongr_affine {I J : Type}
    (e : I ≃ J) (t : Equiv.Perm I) (a : I → ZMod 2) :
    (binaryCoordinateRelabel e).permCongr
        (binaryCoordinateAffinePermutation t a)=
      binaryCoordinateAffinePermutation (e.permCongr t)
        (binaryFunctionRelabel e a) := by
  apply Equiv.ext
  rintro ⟨j,b⟩
  simp [binaryCoordinateRelabel,binaryCoordinateAffinePermutation,
    binaryFunctionRelabel,Equiv.permCongr_apply]

/-- The split coordinate action attached to an actual top and invariant
correlated flip module.  Closure keeps the definition independent of a
chosen finite generating tuple. -/
def binaryCoordinateSplitAction {I : Type}
    (T : Subgroup (Equiv.Perm I))
    (M : Submodule (ZMod 2) (I → ZMod 2)) :
    Subgroup (Equiv.Perm (I × ZMod 2)) :=
  Subgroup.closure {p | ∃ (t : T) (a : I → ZMod 2),
    a∈M ∧ p=binaryCoordinateAffinePermutation (t : Equiv.Perm I) a}

/-- The coordinate split construction is natural under a simultaneous
relabelling of the top action and the correlated module. -/
theorem relabelSubgroup_binaryCoordinateSplitAction {I J : Type}
    (e : I ≃ J) (T : Subgroup (Equiv.Perm I))
    (M : Submodule (ZMod 2) (I → ZMod 2)) :
    relabelSubgroup (binaryCoordinateRelabel e)
        (binaryCoordinateSplitAction T M)=
      binaryCoordinateSplitAction (relabelSubgroup e T)
        (binaryRelabelModule e M) := by
  unfold relabelSubgroup binaryCoordinateSplitAction
  change Subgroup.map (binaryCoordinateRelabel e).permCongrHom.toMonoidHom
      (Subgroup.closure {p | ∃ (t : T) (a : I → ZMod 2),
        a∈M ∧ p=binaryCoordinateAffinePermutation (t : Equiv.Perm I) a}) = _
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext p
  constructor
  · rintro ⟨q,⟨t,a,ha,rfl⟩,rfl⟩
    let t' : relabelSubgroup e T :=
      ⟨e.permCongr (t : Equiv.Perm I),⟨t,t.property,rfl⟩⟩
    let a' : J → ZMod 2 := binaryFunctionRelabel e a
    have ha' : a'∈binaryRelabelModule e M := ⟨a,ha,rfl⟩
    exact ⟨t',a',ha',binaryCoordinateRelabel_permCongr_affine e t a⟩
  · rintro ⟨t',a',ha',rfl⟩
    obtain ⟨t,ht,hte⟩ := t'.property
    obtain ⟨a,ha,hae⟩ := ha'
    refine ⟨binaryCoordinateAffinePermutation t a,⟨⟨t,ht⟩,a,ha,rfl⟩,?_⟩
    change (binaryCoordinateRelabel e).permCongr
      (binaryCoordinateAffinePermutation t a)=_
    rw [binaryCoordinateRelabel_permCongr_affine]
    have hte' : e.permCongr t=(t' : Equiv.Perm J) := hte
    have hae' : binaryFunctionRelabel e a=a' := hae
    rw [hte',hae']

namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I)

/-- The frame relabelling carries each physical affine permutation to its
literal coordinate formula. -/
theorem frame_permCongr_affinePermutation
    (t : Equiv.Perm I) (a : I → ZMod 2) :
    F.frame.symm.permCongr (F.affinePermutation t a)=
      binaryCoordinateAffinePermutation t a := by
  apply Equiv.ext
  rintro ⟨i,b⟩
  change F.frame.symm (F.affinePermutation t a (F.frame (i,b)))=(t i,b+a (t i))
  rw [F.affinePermutation_apply_frame,F.frame.symm_apply_apply]

/-- A physical split action becomes the canonical coordinate action under
the frame itself.  No group classification or finite catalogue enters. -/
theorem relabelSubgroup_frame_symm_splitAffineAction :
    relabelSubgroup F.frame.symm F.splitAffineAction=
      binaryCoordinateSplitAction F.top.range F.kernelSpace := by
  unfold relabelSubgroup splitAffineAction binaryCoordinateSplitAction
  change Subgroup.map F.frame.symm.permCongrHom.toMonoidHom
      (Subgroup.closure {p | ∃ (t : F.top.range) (a : I → ZMod 2),
        a∈F.kernelSpace ∧ p=F.affinePermutation (t : Equiv.Perm I) a}) = _
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext p
  constructor
  · rintro ⟨q,⟨t,a,ha,rfl⟩,rfl⟩
    exact ⟨t,a,ha,F.frame_permCongr_affinePermutation t a⟩
  · rintro ⟨t,a,ha,rfl⟩
    refine ⟨F.affinePermutation (t : Equiv.Perm I) a,⟨t,a,ha,rfl⟩,?_⟩
    exact F.frame_permCongr_affinePermutation t a

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
