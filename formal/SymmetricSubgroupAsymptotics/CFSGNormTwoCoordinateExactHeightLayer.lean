import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerProduct

/-! Only roots of EXACT height h are needed in the image of the actual
h-tail modulo the (h+1)-tail. Higher roots vanish in that quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateHeightLayerProduct

abbrev ExactHeightRoot {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (h : ℤ) :=
  {k : PositiveRoot A // height k.val.val=h}

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem higher_root_quotient_eq_one (K : Type) [Field K] (h : ℤ)
    (k : Roots A) (hk : ∀i,0≤k.val i) (hhigh : h<height k.val) (a : Multiplicative K) :
    quotientRootHom A hd hs hp ho K h k hk a=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change selectedRootElement A hd hs hp ho K k a.toAdd∈heightTail A hd hs hp ho K (h+1)
  exact rootElement_mem_heightTail A hd hs hp ho K (h+1) k hk (by omega) a.toAdd

theorem quotient_heightTail_eq_exact_iSup_ranges (K : Type) [Field K] (h : ℤ) :
    (heightTailInPositive A hd hs hp ho K h).map
      (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1)))=
      ⨆k : ExactHeightRoot A h,
        (quotientRootHom A hd hs hp ho K h k.val.val k.val.property).range := by
  classical
  rw [quotient_heightTail_eq_iSup_ranges]
  apply le_antisymm
  · apply iSup_le
    intro k x hx
    obtain ⟨a,rfl⟩ := hx
    by_cases he : height k.val.val.val=h
    · exact (le_iSup (fun k : ExactHeightRoot A h=>
        (quotientRootHom A hd hs hp ho K h k.val.val k.val.property).range) ⟨k.val,he⟩)
        ⟨a,rfl⟩
    · have hh : h<height k.val.val.val := lt_of_le_of_ne k.property (Ne.symm he)
      rw [higher_root_quotient_eq_one A hd hs hp ho K h k.val.val k.val.property hh a]
      exact one_mem _
  · apply iSup_le
    intro k
    exact le_iSup (fun k : HeightRoot A h=>
      (quotientRootHom A hd hs hp ho K h k.val.val k.val.property).range)
      ⟨k.val,le_of_eq k.property.symm⟩

def exactHeightProductHom (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    (ExactHeightRoot A h→Multiplicative K)→*HeightQuotient A hd hs hp ho K h := by
  classical
  apply MonoidHom.noncommPiCoprod
    (fun k : ExactHeightRoot A h=>quotientRootHom A hd hs hp ho K h k.val.val k.val.property)
  intro i j hij a b
  exact quotient_root_images_commute A hd hs hp ho K h hh i.val.val j.val.val
    i.val.property j.val.property (le_of_eq i.property.symm) (le_of_eq j.property.symm) a b

theorem exactHeightProductHom_range (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    (exactHeightProductHom A hd hs hp ho K h hh).range=
      (heightTailInPositive A hd hs hp ho K h).map
        (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1))) := by
  classical
  rw [exactHeightProductHom,MonoidHom.noncommPiCoprod_range]
  exact (quotient_heightTail_eq_exact_iSup_ranges A hd hs hp ho K h).symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightLayer
