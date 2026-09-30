import SymmetricSubgroupAsymptotics.BinaryCoordinateSplitAction
import SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

/-!
# Transport of two-orbit augmentation modules

The six-dimensional correlated flip module in the split frontier is defined
by its two actual kernel orbits.  This file proves that both the orbit classes
and their augmentation module commute with literal relabelling of the pair
points.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Relabel the actual orbit quotient together with the acting permutation
subgroup. -/
def relabelOrbitEquiv {I J : Type} (e : I ≃ J)
    (H : Subgroup (Equiv.Perm I)) :
    MulAction.orbitRel.Quotient H I ≃
      MulAction.orbitRel.Quotient (relabelSubgroup e H) J where
  toFun := Quotient.map' e (by
    intro x y hxy
    rw [MulAction.orbitRel_apply] at hxy ⊢
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hxy
    let h' : relabelSubgroup e H :=
      ⟨e.permCongr (h : Equiv.Perm I),⟨h,h.property,rfl⟩⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h',?_⟩
    change (h' : Equiv.Perm J) (e y)=e x
    dsimp [h']
    simpa only [e.symm_apply_apply] using congrArg e hh)
  invFun := Quotient.map' e.symm (by
    intro x y hxy
    rw [MulAction.orbitRel_apply] at hxy ⊢
    obtain ⟨h',hh'⟩ := MulAction.mem_orbit_iff.mp hxy
    obtain ⟨h,hh,heh⟩ := h'.property
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨h,hh⟩,?_⟩
    apply e.injective
    change e (h (e.symm y))=e (e.symm x)
    rw [e.apply_symm_apply]
    calc
      e (h (e.symm y)) = (e.permCongr h) y := by
        simp only [Equiv.permCongr_apply,Equiv.apply_symm_apply]
      _ = (h' : Equiv.Perm J) y := by
        have heh' : e.permCongr h=(h' : Equiv.Perm J) := heh
        rw [heh']
      _ = x := hh')
  left_inv := by
    intro o
    induction o using Quotient.inductionOn'
    simp only [Quotient.map'_mk'',Equiv.symm_apply_apply]
  right_inv := by
    intro o
    induction o using Quotient.inductionOn'
    simp only [Quotient.map'_mk'',Equiv.apply_symm_apply]

/-- The relabelling equivalence on the literal points inside one orbit. -/
def relabelOrbitPointEquiv {I J : Type} (e : I ≃ J)
    (H : Subgroup (Equiv.Perm I))
    (o : MulAction.orbitRel.Quotient H I) :
    o.orbit ≃ (relabelOrbitEquiv e H o).orbit where
  toFun x := ⟨e x,by
    apply MulAction.orbitRel.Quotient.mem_orbit.mpr
    have hx := MulAction.orbitRel.Quotient.mem_orbit.mp x.property
    calc
      Quotient.mk'' (e x.val) =
          relabelOrbitEquiv e H (Quotient.mk'' x.val) := rfl
      _ = relabelOrbitEquiv e H o := congrArg (relabelOrbitEquiv e H) hx⟩
  invFun y := ⟨e.symm y,by
    apply MulAction.orbitRel.Quotient.mem_orbit.mpr
    have hy := MulAction.orbitRel.Quotient.mem_orbit.mp y.property
    apply (relabelOrbitEquiv e H).injective
    calc
      relabelOrbitEquiv e H (Quotient.mk'' (e.symm y.val)) =
          Quotient.mk'' y.val := by
        change Quotient.mk'' (e (e.symm y.val))=Quotient.mk'' y.val
        rw [e.apply_symm_apply]
      _ = relabelOrbitEquiv e H o := hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)

/-- Orbit sums are unchanged by simultaneous relabelling of points and
functions. -/
theorem orbitSum_binaryFunctionRelabel {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J)
    (H : Subgroup (Equiv.Perm I))
    (o : MulAction.orbitRel.Quotient H I) (a : I → ZMod 2) :
    PermutationBinaryTwoOrbitSplit.orbitSum (relabelSubgroup e H)
        (relabelOrbitEquiv e H o) (binaryFunctionRelabel e a)=
      PermutationBinaryTwoOrbitSplit.orbitSum H o a := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype J := Fintype.ofFinite J
  have hsum := Equiv.sum_comp (relabelOrbitPointEquiv e H o)
    (fun y : (relabelOrbitEquiv e H o).orbit =>
      (binaryFunctionRelabel e a) y.val)
  change (∑ y : (relabelOrbitEquiv e H o).orbit,
      (binaryFunctionRelabel e a) y.val)=∑ x : o.orbit,a x.val
  have hright :
      (∑ x : o.orbit,
        (binaryFunctionRelabel e a) (relabelOrbitPointEquiv e H o x).val)=
          ∑ x : o.orbit,a x.val := by
    apply Finset.sum_congr rfl
    intro x _
    change a (e.symm (e x.val))=a x.val
    rw [e.symm_apply_apply]
  exact hsum.symm.trans hright

/-- The two-orbit augmentation module is fusion-natural under the same
pair-label relabelling as the top subgroup. -/
theorem binaryRelabelModule_twoOrbitAugmentation {I J : Type}
    [Fintype I] [Fintype J]
    (e : I ≃ J) (H : Subgroup (Equiv.Perm I))
    (o₁ o₂ : MulAction.orbitRel.Quotient H I) :
    binaryRelabelModule e
        (PermutationBinaryTwoOrbitSplit.twoOrbitAugmentation H o₁ o₂)=
      PermutationBinaryTwoOrbitSplit.twoOrbitAugmentation
        (relabelSubgroup e H) (relabelOrbitEquiv e H o₁)
          (relabelOrbitEquiv e H o₂) := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    change (_,_)=(0,0)
    change (_,_)=(0,0) at hb
    apply Prod.ext
    · exact (orbitSum_binaryFunctionRelabel e H o₁ b).trans
        (congrArg Prod.fst hb)
    · exact (orbitSum_binaryFunctionRelabel e H o₂ b).trans
        (congrArg Prod.snd hb)
  · intro ha
    let b : I → ZMod 2 := (binaryFunctionRelabel e).symm a
    refine ⟨b,?_,?_⟩
    · change (_,_)=(0,0)
      change (_,_)=(0,0) at ha
      have h₁ := orbitSum_binaryFunctionRelabel e H o₁ b
      have h₂ := orbitSum_binaryFunctionRelabel e H o₂ b
      rw [(binaryFunctionRelabel e).apply_symm_apply] at h₁ h₂
      apply Prod.ext
      · exact h₁.symm.trans (congrArg Prod.fst ha)
      · exact h₂.symm.trans (congrArg Prod.snd ha)
    · exact (binaryFunctionRelabel e).apply_symm_apply a

end SymmetricSubgroupAsymptotics
