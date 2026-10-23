import SymmetricSubgroupAsymptotics.CFSGGTwoSimpleHigherCollecting
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveCollecting

/-! Actual source-model higher/simple collecting, with all signs retained.
The only two noncommuting pairs are supplied by checked native sparse actions
and transported through the unconditional whole original Model equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherCollecting
open CFSG.Models.Chevalley CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalPositiveCollecting
open CFSGGTwoSimpleHigherCollecting

variable (K : Type) [Field K] [CharP K 3]

theorem pair_commute (i : Fin 6) (a b : K) :
    Commute (positiveModel K (commutingPair i).1 a)
      (positiveModel K (commutingPair i).2 b) := by
  change _ * _ = _ * _
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,Subgroup.coe_mul,positiveModel_native] using
    (positive_pair_commute K i a b).eq

theorem two_short (a c : K) :
    positiveModel K 2 c * positiveModel K 0 a =
      positiveModel K 0 a * positiveModel K 2 c * positiveModel K 3 (-a*c) := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,Subgroup.coe_mul,positiveModel_native] using
    positive_two_short K a c

theorem four_long (b c : K) :
    positiveModel K 4 c * positiveModel K 1 b =
      positiveModel K 1 b * positiveModel K 4 c * positiveModel K 5 (b*c) := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,Subgroup.coe_mul,positiveModel_native] using
    positive_four_long K b c

private theorem shift_first {G : Type*} [Group G] (a u v w z delta : G)
    (h : u*a=a*u*delta) (hv : Commute v a) (hw : Commute w a)
    (hz : Commute z a) :
    u*v*w*z*a=a*u*(delta*v)*w*z := by
  calc
    _ = u*((v*w*z)*a) := by simp only [mul_assoc]
    _ = u*(a*(v*w*z)) := by rw [((hv.mul_left hw).mul_left hz).eq]
    _ = (u*a)*(v*w*z) := by simp only [mul_assoc]
    _ = (a*u*delta)*(v*w*z) := by rw [h]
    _ = _ := by simp only [mul_assoc]

private theorem shift_third {G : Type*} [Group G] (a u v w z delta : G)
    (h : w*a=a*w*delta) (hu : Commute u a) (hv : Commute v a)
    (hz : Commute z a) :
    u*v*w*z*a=a*u*v*w*(delta*z) := by
  calc
    _ = (u*v*w)*(z*a) := by simp only [mul_assoc]
    _ = (u*v*w)*(a*z) := by rw [hz.eq]
    _ = (u*v)*(w*a)*z := by simp only [mul_assoc]
    _ = (u*v)*(a*w*delta)*z := by rw [h]
    _ = ((u*v)*a)*w*delta*z := by simp only [mul_assoc]
    _ = (a*(u*v))*w*delta*z := by rw [(hu.mul_left hv).eq]
    _ = _ := by simp only [mul_assoc]

private theorem higherWord_four (a b c d : K) :
    higherWord K ![a,b,c,d]=positiveModel K 2 a*positiveModel K 3 b*
      positiveModel K 4 c*positiveModel K 5 d := rfl

theorem higherWord_short (x : Fin 4 → K) (a : K) :
    higherWord K x * positiveModel K 0 a =
      positiveModel K 0 a * higherWord K ![x 0,x 1-a*x 0,x 2,x 3] := by
  have h := shift_first (positiveModel K 0 a) (positiveModel K 2 (x 0))
    (positiveModel K 3 (x 1)) (positiveModel K 4 (x 2)) (positiveModel K 5 (x 3))
    (positiveModel K 3 (-a*x 0)) (two_short K a (x 0))
    (pair_commute K 1 (x 1) a) (pair_commute K 3 (x 2) a) (pair_commute K 4 (x 3) a)
  change higherWord K x * positiveModel K 0 a =
    positiveModel K 0 a * positiveModel K 2 (x 0) *
      (positiveModel K 3 (-a*x 0) * positiveModel K 3 (x 1)) *
        positiveModel K 4 (x 2) * positiveModel K 5 (x 3) at h
  rw [h,positiveModel_add,show -a*x 0+x 1=x 1-a*x 0 by ring]
  simp only [higherWord_four,mul_assoc]

theorem higherWord_long (x : Fin 4 → K) (b : K) :
    higherWord K x * positiveModel K 1 b =
      positiveModel K 1 b * higherWord K ![x 0,x 1,x 2,x 3+b*x 2] := by
  have h := shift_third (positiveModel K 1 b) (positiveModel K 2 (x 0))
    (positiveModel K 3 (x 1)) (positiveModel K 4 (x 2)) (positiveModel K 5 (x 3))
    (positiveModel K 5 (b*x 2)) (four_long K b (x 2))
    (pair_commute K 0 (x 0) b) (pair_commute K 2 (x 1) b) (pair_commute K 5 (x 3) b)
  change higherWord K x * positiveModel K 1 b =
    positiveModel K 1 b * positiveModel K 2 (x 0) * positiveModel K 3 (x 1) *
      positiveModel K 4 (x 2) * (positiveModel K 5 (b*x 2) * positiveModel K 5 (x 3)) at h
  rw [h,positiveModel_add,show b*x 2+x 3=x 3+b*x 2 by ring]
  simp only [higherWord_four,mul_assoc]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherCollecting
