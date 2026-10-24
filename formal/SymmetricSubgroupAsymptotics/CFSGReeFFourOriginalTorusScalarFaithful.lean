import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalFieldAction

/-! The original projection preserves both scalar characters faithfully.
Equality of projected torus words is tested on actual original root
coordinates; injectivity is concluded, rather than assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalTorusScalarFaithful
open CFSGReeFFourOriginalDiagonalFieldAction CFSGReeFFourTorusScalarCoordinates
open CFSGReeFFourFieldParameters CFSGReeFFourPerfectProjection CFSGReeFFourFixedTorus
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalOuterSemilinear
open CFSGReeFFourOriginalMiddleSemilinear

theorem scalarPair_eq_of_original_torus_eq (m : ℕ) (hm : 0<m)
    (a b c d : (Field m)ˣ)
    (he : fixedToOriginal m hm (fixedTorus m a b)=fixedToOriginal m hm (fixedTorus m c d)) :
    scalarPair m (a,b)=scalarPair m (c,d) := by
  have houter (x : Field m) : outerAction m hm 1 x=x := by
    exact congrArg (fun A : AddAut (Field m)=>A x) (map_one (outerRestriction m hm))
  have hmiddle (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      CFSGSuzukiUnipotent.firstParameter m (middleAction m hm 1 x)=
        CFSGSuzukiUnipotent.firstParameter m x := by
    exact congrArg (fun A : MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m)=>
      CFSGSuzukiUnipotent.firstParameter m (A x)) (map_one (middleRestriction m hm))
  have himage : (1 : pairStabilizer m hm).val (fixedToOriginal m hm (fixedTorus m a b))=
      fixedToOriginal m hm (fixedTorus m c d) := he
  apply Prod.ext
  · apply Units.ext
    exact (congrArg Units.val (outer_character_of_torus_image m hm 1
      (RingEquiv.refl (Field m)) houter a b c d himage)).symm
  · apply Units.ext
    exact (congrArg Units.val (middle_character_of_torus_image m hm 1
      (RingEquiv.refl (Field m)) hmiddle a b c d himage)).symm

theorem original_torus_parameters_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (fun p : (Field m)ˣ×(Field m)ˣ=>
      fixedToOriginal m hm (fixedTorus m p.1 p.2)) := by
  intro p q he
  exact scalarPair_injective m (scalarPair_eq_of_original_torus_eq m hm p.1 p.2 q.1 q.2 he)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalTorusScalarFaithful
