import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient
import Mathlib.GroupTheory.NoncommPiCoprod

/-! Each actual height-tail IMAGE in the successive quotient has a
finite one-coordinate-per-root product parametrization. The generated
subgroup equality and quotient commutativity are proved internally from
the literal root family, not supplied as a factorization hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerProduct
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateRootHeightQuotient

abbrev HeightRoot {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (h : ℤ) :=
  {k : PositiveRoot A // h≤height k.val.val}

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

instance heightLayerTailNormal (K : Type) [Field K] (h : ℤ) :
    (heightTailInPositive A hd hs hp ho K h).Normal :=
  heightTail_normal_in_positive A hd hs hp ho K h

theorem heightTail_eq_iSup_ranges (K : Type) [Field K] (h : ℤ) :
    heightTail A hd hs hp ho K h=
      ⨆k : HeightRoot A h,(selectedRootHom A hd hs hp ho K k.val.val).range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨k,hk,a,ha⟩
    exact (le_iSup (fun k : HeightRoot A h=>(selectedRootHom A hd hs hp ho K k.val.val).range)
      ⟨k,hk⟩) ⟨Multiplicative.ofAdd a,ha⟩
  · apply iSup_le
    intro k x hx
    obtain ⟨a,rfl⟩ := hx
    exact rootElement_mem_heightTail A hd hs hp ho K h k.val.val k.val.property k.property a.toAdd

theorem heightTailInPositive_eq_iSup_ranges (K : Type) [Field K] (h : ℤ) :
    heightTailInPositive A hd hs hp ho K h=
      ⨆k : HeightRoot A h,(positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property).range := by
  apply Subgroup.map_injective (PositiveGroup A hd hs hp ho K).subtype_injective
  change ((heightTail A hd hs hp ho K h).subgroupOf (PositiveGroup A hd hs hp ho K)).map
      (PositiveGroup A hd hs hp ho K).subtype=_
  rw [Subgroup.map_subgroupOf_eq_of_le (heightTail_le_positive A hd hs hp ho K h),Subgroup.map_iSup]
  have hmap (k : HeightRoot A h) :
      ((positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property).range).map
        (PositiveGroup A hd hs hp ho K).subtype=(selectedRootHom A hd hs hp ho K k.val.val).range := by
    rw [←MonoidHom.range_comp]
    rfl
  simp only [hmap]
  exact heightTail_eq_iSup_ranges A hd hs hp ho K h

theorem quotient_heightTail_eq_iSup_ranges (K : Type) [Field K] (h : ℤ) :
    (heightTailInPositive A hd hs hp ho K h).map
      (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1)))=
      ⨆k : HeightRoot A h,(quotientRootHom A hd hs hp ho K h k.val.val k.val.property).range := by
  calc
    _ = (⨆k : HeightRoot A h,
        (positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property).range).map
        (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1))) :=
      congrArg (fun P : Subgroup (PositiveGroup A hd hs hp ho K)=>
        P.map (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1))))
        (heightTailInPositive_eq_iSup_ranges A hd hs hp ho K h)
    _ = _ := by
      rw [Subgroup.map_iSup]
      apply iSup_congr
      intro k
      exact (MonoidHom.range_comp _ _).symm

def heightLayerProductHom (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    (HeightRoot A h→Multiplicative K)→*HeightQuotient A hd hs hp ho K h := by
  classical
  apply MonoidHom.noncommPiCoprod
    (fun k : HeightRoot A h=>quotientRootHom A hd hs hp ho K h k.val.val k.val.property)
  intro i j hij a b
  exact quotient_root_images_commute A hd hs hp ho K h hh i.val.val j.val.val
    i.val.property j.val.property i.property j.property a b

theorem heightLayerProductHom_range (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    (heightLayerProductHom A hd hs hp ho K h hh).range=
      (heightTailInPositive A hd hs hp ho K h).map
        (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1))) := by
  classical
  rw [heightLayerProductHom,MonoidHom.noncommPiCoprod_range]
  exact (quotient_heightTail_eq_iSup_ranges A hd hs hp ho K h).symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerProduct
