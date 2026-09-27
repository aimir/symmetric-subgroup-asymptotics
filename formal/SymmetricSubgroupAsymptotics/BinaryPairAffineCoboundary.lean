import SymmetricSubgroupAsymptotics.BinaryPairAffineChart

/-! A vanishing affine cohomology class gives an actual point conjugation.

The conjugating flip is a permutation of the original point set, lifted
from the original ambient flip quotient. The conclusion identifies the
whole original subgroup with the full zero affine graph. It is not an
abstract module or extension isomorphism, and it makes no assertion that
an arbitrary original normal subgroup equals its kernel intersection.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- The affine permutation on the original points in the actual frame. -/
def affinePermutation (t : Equiv.Perm I) (a : I → ZMod 2) : Equiv.Perm X where
  toFun x := F.frame (t (F.frame.symm x).1,
    (F.frame.symm x).2+a (t (F.frame.symm x).1))
  invFun x := F.frame (t⁻¹ (F.frame.symm x).1,
    (F.frame.symm x).2-a (F.frame.symm x).1)
  left_inv x := by simp
  right_inv x := by simp

theorem affinePermutation_apply_frame (t : Equiv.Perm I) (a : I → ZMod 2)
    (i : I) (b : ZMod 2) :
    F.affinePermutation t a (F.frame (i,b))=F.frame (t i,b+a (t i)) := by
  simp only [affinePermutation,Equiv.coe_fn_mk,Equiv.symm_apply_apply]

/-- A literal original-point flip; it need not already belong to U. -/
def physicalFlip (a : I → ZMod 2) : Equiv.Perm X := F.affinePermutation 1 a

theorem physicalFlip_apply_frame (a : I → ZMod 2) (i : I) (b : ZMod 2) :
    F.physicalFlip a (F.frame (i,b))=F.frame (i,b+a i) :=
  F.affinePermutation_apply_frame 1 a i b

theorem physicalFlip_inv_apply_frame (a : I → ZMod 2) (i : I) (b : ZMod 2) :
    (F.physicalFlip a)⁻¹ (F.frame (i,b))=F.frame (i,b-a i) := by
  simp only [physicalFlip,affinePermutation,Equiv.Perm.inv_def,
    Equiv.coe_fn_symm_mk,Equiv.symm_apply_apply]
  rfl

theorem affinePermutation_original (u : U) :
    F.affinePermutation (F.top u) (F.affineTranslation u)=(u : Equiv.Perm X) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  rw [F.affinePermutation_apply_frame,F.affine_action_frame]

/-- The actual point conjugation changes the translation by the literal
coboundary. Its sign and permutation convention are fixed by this formula. -/
theorem physicalFlip_conjugate (a : I → ZMod 2) (u : U) :
    (F.physicalFlip a)*(u : Equiv.Perm X)*(F.physicalFlip a)⁻¹=
      F.affinePermutation (F.top u)
        (F.affineTranslation u+a-
          permutationFunctionRepresentation (ZMod 2) F.top.range I
            (F.top.rangeRestrict u) a) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  change F.physicalFlip a ((u : Equiv.Perm X)
    ((F.physicalFlip a)⁻¹ (F.frame (i,b))))=_
  rw [F.physicalFlip_inv_apply_frame,F.affine_action_frame,F.physicalFlip_apply_frame,
    F.affinePermutation_apply_frame]
  apply congrArg F.frame
  apply Prod.ext
  · rfl
  · change b-a i+F.affineTranslation u (F.top u i)+a (F.top u i)=
      b+(F.affineTranslation u (F.top u i)+a (F.top u i)-a ((F.top u)⁻¹ (F.top u i)))
    rw [Equiv.Perm.inv_def,Equiv.symm_apply_apply]
    abel

/-- The full zero affine action on the same original points and the same
actual top, retaining the full original correlated kernel. -/
def splitAffineAction : Subgroup (Equiv.Perm X) :=
  Subgroup.closure {p | ∃ (t : F.top.range) (a : I → ZMod 2),
    a∈F.kernelSpace ∧ p=F.affinePermutation (t : Equiv.Perm I) a}

/-- A literal lifted coboundary gives equality of original permutation
subgroups after conjugation, not just an abstract extension equivalence. -/
theorem physical_conjugate_eq_split_of_coboundary (a : I → ZMod 2)
    (hc : ∀ t : F.top.range,F.affineClass t=
      F.affineQuotientRepresentation t (F.kernelSpace.mkQ a)-F.kernelSpace.mkQ a) :
    U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom=F.splitAffineAction := by
  apply le_antisymm
  · rintro p ⟨u,hu,rfl⟩
    let v : U := ⟨u,hu⟩
    apply Subgroup.subset_closure
    refine ⟨F.top.rangeRestrict v,
      F.affineTranslation v+a-permutationFunctionRepresentation (ZMod 2) F.top.range I
        (F.top.rangeRestrict v) a,?_,?_⟩
    · apply (Submodule.Quotient.mk_eq_zero F.kernelSpace).mp
      change F.kernelSpace.mkQ
        (F.affineTranslation v+a-permutationFunctionRepresentation (ZMod 2) F.top.range I
          (F.top.rangeRestrict v) a)=0
      rw [map_sub,map_add,← F.affineClass_top]
      change F.affineClass (F.top.rangeRestrict v)+F.kernelSpace.mkQ a-
        F.affineQuotientRepresentation (F.top.rangeRestrict v) (F.kernelSpace.mkQ a)=0
      rw [hc]
      abel
    · exact F.physicalFlip_conjugate a v
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨t,m,hm,rfl⟩
    let b := m-a+permutationFunctionRepresentation (ZMod 2) F.top.range I t a
    have hm0 : F.kernelSpace.mkQ m=0 :=
      (Submodule.Quotient.mk_eq_zero F.kernelSpace).mpr hm
    have hb : F.kernelSpace.mkQ b=F.affineClass t := by
      change F.kernelSpace.mkQ m-F.kernelSpace.mkQ a+
        F.affineQuotientRepresentation t (F.kernelSpace.mkQ a)=F.affineClass t
      rw [hm0,hc]
      abel
    obtain ⟨v,ht,hs⟩ := (F.affine_graph_fibre t b).mpr hb
    refine ⟨(v : Equiv.Perm X),v.property,?_⟩
    change F.physicalFlip a*(v : Equiv.Perm X)*(F.physicalFlip a)⁻¹=
      F.affinePermutation (t : Equiv.Perm I) m
    rw [F.physicalFlip_conjugate,hs,ht]
    have ht' : F.top v=(t : Equiv.Perm I) := congrArg Subtype.val ht
    rw [ht']
    congr 1
    dsimp [b]
    abel

/-- A quotient coboundary is lifted to an actual original flip vector.
No source-membership premise is imposed on the conjugating permutation. -/
theorem exists_physical_conjugate_eq_split_of_coboundary
    (c : (I → ZMod 2) ⧸ F.kernelSpace)
    (hc : ∀ t : F.top.range,F.affineClass t=F.affineQuotientRepresentation t c-c) :
    ∃ a : I → ZMod 2,
      U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom=F.splitAffineAction := by
  obtain ⟨a,rfl⟩ := F.kernelSpace.mkQ_surjective c
  exact ⟨a,F.physical_conjugate_eq_split_of_coboundary a hc⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
