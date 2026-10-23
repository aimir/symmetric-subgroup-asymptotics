import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveCollecting
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalHigherRootCovariance
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedCoordinateArithmetic

/-! The actual ORIGINAL Ree automorphism has the checked signed polynomial
coordinate map on the injective six-root word chart. This is a source group
identity, not a claim that arbitrary fixed quotient coordinates lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoSixWordTwist
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoPositiveSixWord CFSGGTwoOriginalPositiveCollecting
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalAutomorphism
open CFSGReeGTwoOriginalHigherRootCovariance CFSGReeGTwoFixedCoordinateArithmetic

private theorem collect_exchanged_group {K G : Type*} [Ring K] [Group G]
    (x : Fin 6 → K → G) (H : (Fin 4 → K) → G)
    (hH : ∀ z, H z=x 2 (z 0)*x 3 (z 1)*x 4 (z 2)*x 5 (z 3))
    (hadd : ∀ z w, H z*H w=H (z+w))
    (hrotate : ∀ c d e f, x 4 c*x 5 d*x 2 e*x 3 f=H ![e,f,c,d])
    (hcollect : ∀ a b, x 1 b*x 0 a=
      x 0 a*x 1 b*x 2 (-a*b)*x 3 (-a^2*b)*x 4 (-a^3*b)*x 5 (a^3*b^2))
    (a b c d e f : K) :
    x 1 b*x 0 a*x 4 c*x 5 d*x 2 e*x 3 f=
      x 0 a*x 1 b*x 2 (-a*b+e)*x 3 (-a^2*b+f)*x 4 (-a^3*b+c)*x 5 (a^3*b^2+d) := by
  have hH4 (r s t u : K) : H ![r,s,t,u]=x 2 r*x 3 s*x 4 t*x 5 u := hH _
  have hsum : (![-a*b,-a^2*b,-a^3*b,a^3*b^2]+![e,f,c,d]) =
      ![-a*b+e,-a^2*b+f,-a^3*b+c,a^3*b^2+d] := by
    funext i
    fin_cases i <;> rfl
  calc
    _ = (x 1 b*x 0 a)*(x 4 c*x 5 d*x 2 e*x 3 f) := by simp only [mul_assoc]
    _ = (x 0 a*x 1 b*H ![-a*b,-a^2*b,-a^3*b,a^3*b^2])*H ![e,f,c,d] := by
      rw [hcollect,hrotate]
      simp only [hH4,mul_assoc]
    _ = x 0 a*x 1 b*H (![-a*b,-a^2*b,-a^3*b,a^3*b^2]+![e,f,c,d]) := by
      simp only [mul_assoc,hadd]
    _ = _ := by rw [hsum,hH4]; simp only [mul_assoc]

private theorem collect_exchanged_word (K : Type) [Field K] [CharP K 3]
    (a b c d e f : K) :
    positiveModel K 1 b * positiveModel K 0 a *
      positiveModel K 4 c * positiveModel K 5 d *
      positiveModel K 2 e * positiveModel K 3 f =
        modelWord K ![a,b,-a*b+e,-a^2*b+f,-a^3*b+c,a^3*b^2+d] :=
  collect_exchanged_group (positiveModel K) (higherWord K) (fun _ => rfl)
    (higherWord_add K) (higherWord_rotate K) (simple_collecting K) a b c d e f

theorem ree_modelWord (m : ℕ) (x : Fin 6 → Field m) :
    reeAutomorphism m (modelWord (Field m) x) =
      modelWord (Field m) (twist (alphaEquiv m) x) := by
  simp only [modelWord, map_mul, ree_positiveModel_0, ree_positiveModel_1,
    ree_positiveModel_2, ree_positiveModel_3, ree_positiveModel_4, ree_positiveModel_5]
  rw [collect_exchanged_word]
  change modelWord (Field m)
      ![beta m (x 1),alpha m (x 0),
        -beta m (x 1)*alpha m (x 0)+(-beta m (x 4)),
        -(beta m (x 1))^2*alpha m (x 0)+beta m (x 5),
        -(beta m (x 1))^3*alpha m (x 0)+(-alpha m (x 2)),
        (beta m (x 1))^3*(alpha m (x 0))^2+alpha m (x 3)] = _
  simp only [twist, sub_eq_add_neg]
  rfl

theorem modelWord_fixed_iff (m : ℕ) (x : Fin 6 → Field m) :
    reeAutomorphism m (modelWord (Field m) x) = modelWord (Field m) x ↔
      twist (alphaEquiv m) x = x := by
  rw [ree_modelWord]
  exact (modelWord_injective (Field m)).eq_iff

theorem normalForm_modelWord_fixed (m : ℕ) (a c d : Field m) :
    reeAutomorphism m
      (modelWord (Field m) (normalForm (alphaEquiv m) a c d)) =
      modelWord (Field m) (normalForm (alphaEquiv m) a c d) := by
  rw [ree_modelWord, twist_normalForm _ (alpha_twice m)]

end SymmetricSubgroupAsymptotics.CFSGReeGTwoSixWordTwist
