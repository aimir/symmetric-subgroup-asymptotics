import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNoncentralMatrix
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageFourthCoefficient
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootFixed
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

/-! A noncentral fourth-root word in the SAME original Serre image group.
The witness is tested on the image of the original E generator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageWeylWitness
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightData CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (hsimple : ∀ j : b.support,rootSign A j= -1) (K : Type) [Field K]

abbrev group := canonicalElementaryGroup (realizationData A hs hp b s) K

def imageAction := canonicalImageAction (realizationData A hs hp b s) K
  (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero
    A hs hp b s hsimple K)

abbrev imageGroup := (imageAction A hs hp b s hsimple K).range

def weylElement (i : Fin r) : group A hs hp b s K :=
  canonicalElementaryRoot (realizationData A hs hp b s) K false i 1*
    canonicalElementaryRoot (realizationData A hs hp b s) K true i (-1)*
    canonicalElementaryRoot (realizationData A hs hp b s) K false i 1

def imageWeyl (i : Fin r) : imageGroup A hs hp b s hsimple K :=
  (imageAction A hs hp b s hsimple K).rangeRestrict (weylElement A hs hp b s K i)

theorem weylElement_four (i : Fin r) : (weylElement A hs hp b s K i)^4=1 := by
  apply Subtype.ext
  exact CFSGNormTwoGeckWeylUnits.weyl_four A hs hp b s K i

theorem imageWeyl_four (i : Fin r) : (imageWeyl A hs hp b s hsimple K i)^4=1 := by
  rw [imageWeyl,←map_pow,weylElement_four,map_one]

private theorem action_val (g : group A hs hp b s K)
    (y : (baseChange (realizationData A hs hp b s) K).range) :
    (imageAction A hs hp b s hsimple K g y).val=
      (g.val:Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*y.val*(↑(g.val⁻¹):Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := rfl

theorem imageWeyl_not_center (i : Fin r) :
    imageWeyl A hs hp b s hsimple K i∉Subgroup.center (imageGroup A hs hp b s hsimple K) := by
  intro hc
  let D := realizationData A hs hp b s
  let R := canonicalElementaryRoot D K false i 1
  let y : (baseChange D K).range := (baseChange D K).rangeRestrict
    (1⊗ₜ[ℤ]CFSGSerreDiagram.latticeGenerator (cartan b s) (CartanMatrix.Generators.E i))
  have hy : y.val=fieldRoot D K false i := by
    change baseChange D K
      (1⊗ₜ[ℤ]CFSGSerreDiagram.latticeGenerator (cartan b s) (CartanMatrix.Generators.E i))=_
    rw [baseChange_generator]
    rfl
  have hRfix : imageAction A hs hp b s hsimple K R y=y := by
    apply Subtype.ext
    rw [action_val,hy]
    exact canonicalRoot_fixes_root D K false i 1
  have hWy : (imageAction A hs hp b s hsimple K (weylElement A hs hp b s K i) y).val=
      (canonicalWeyl D K i:Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*fieldRoot D K false i*
        (↑((canonicalWeyl D K i)⁻¹):Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
    rw [action_val,hy]
    rfl
  have hcomm := (Subgroup.mem_center_iff.mp hc)
    ((imageAction A hs hp b s hsimple K).rangeRestrict R)
  have hh := congrArg Subtype.val hcomm
  change imageAction A hs hp b s hsimple K R*
      imageAction A hs hp b s hsimple K (weylElement A hs hp b s K i)=
    imageAction A hs hp b s hsimple K (weylElement A hs hp b s K i)*
      imageAction A hs hp b s hsimple K R at hh
  have he := DFunLike.congr_fun hh y
  change imageAction A hs hp b s hsimple K R
      (imageAction A hs hp b s hsimple K (weylElement A hs hp b s K i) y)=
    imageAction A hs hp b s hsimple K (weylElement A hs hp b s K i)
      (imageAction A hs hp b s hsimple K R y) at he
  rw [hRfix] at he
  have hv := congrArg Subtype.val he
  rw [action_val,hWy] at hv
  exact CFSGNormTwoGeckNoncentralMatrix.root_does_not_fix_weyl_root A hs hp b s K i hv

theorem imageProjective_even_card (i : Fin r) :
    Even (Nat.card (imageGroup A hs hp b s hsimple K⧸
      Subgroup.center (imageGroup A hs hp b s hsimple K))) := by
  let q := QuotientGroup.mk' (Subgroup.center (imageGroup A hs hp b s hsimple K))
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root
    (q (imageWeyl A hs hp b s hsimple K i))
  · intro h
    exact imageWeyl_not_center A hs hp b s hsimple K i ((QuotientGroup.eq_one_iff _).mp h)
  · have hw : (imageWeyl A hs hp b s hsimple K i)^4=1 :=
      imageWeyl_four A hs hp b s hsimple K i
    exact (map_pow q (imageWeyl A hs hp b s hsimple K i) 4).symm.trans
      ((congrArg q hw).trans (map_one q))

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageWeylWitness
