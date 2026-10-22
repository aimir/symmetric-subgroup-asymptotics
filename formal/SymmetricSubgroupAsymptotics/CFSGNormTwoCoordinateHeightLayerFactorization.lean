import SymmetricSubgroupAsymptotics.CFSGFiniteQuotientFamilyProduct
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightLayer

/-! Actual one-height collection in the Geck MATRIX image-U. Every
element of the h-tail is one fixed ordered product with one parameter
per exact height-h root, times a remainder in the (h+1)-tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerFactorization
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateHeightLayerProduct
open CFSGNormTwoCoordinateExactHeightLayer CFSGFiniteQuotientFamilyProduct

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

def exactHeightWord (K : Type) [Field K] (h : ℤ) (c : ExactHeightRoot A h→K) :
    PositiveGroup A hd hs hp ho K := by
  classical
  exact orderedFamilyProduct (fun k : ExactHeightRoot A h=>
    positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property (Multiplicative.ofAdd (c k)))

theorem heightTailInPositive_factor (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (x : PositiveGroup A hd hs hp ho K) (hx : x∈heightTailInPositive A hd hs hp ho K h) :
    ∃c : ExactHeightRoot A h→K,∃y : PositiveGroup A hd hs hp ho K,
      y∈heightTailInPositive A hd hs hp ho K (h+1) ∧
      x=exactHeightWord A hd hs hp ho K h c*y := by
  classical
  let q : PositiveGroup A hd hs hp ho K→*HeightQuotient A hd hs hp ho K h :=
    QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1))
  let f := fun k : ExactHeightRoot A h=>
    positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property
  have hc : Pairwise (fun i j : ExactHeightRoot A h=>
      ∀a b,Commute (q (f i a)) (q (f j b))) := by
    intro i j hij a b
    exact quotient_root_images_commute A hd hs hp ho K h hh i.val.val j.val.val
      i.val.property j.val.property (le_of_eq i.property.symm) (le_of_eq j.property.symm) a b
  have hxrange : q x∈(MonoidHom.noncommPiCoprod (fun i=>q.comp (f i)) hc).range := by
    change q x∈(exactHeightProductHom A hd hs hp ho K h hh).range
    rw [exactHeightProductHom_range]
    exact ⟨x,hx,rfl⟩
  obtain ⟨c,y,hy,he⟩ := exists_ordered_factor_and_kernel q f hc x hxrange
  refine ⟨(fun k=>(c k).toAdd),y,?_,?_⟩
  · exact (QuotientGroup.eq_one_iff y).mp hy
  · exact he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerFactorization
