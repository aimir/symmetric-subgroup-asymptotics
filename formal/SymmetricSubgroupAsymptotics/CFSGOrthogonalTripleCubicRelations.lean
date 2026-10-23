import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Tactic.NoncommRing

/-! Integral multiplication identities for the cubic coefficients of
three commuting quadratic factors. Mixed first/second products vanish
as literal ring products; no Lie-image or characteristic assumption is
hidden in this algebraic helper. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalTripleCubicRelations
variable {B : Type*} [Ring B]

 theorem triple_relations (T Q : Fin 3→B)
    (hcomm : ∀i j,Commute (T i) (T j))
    (hsquare : ∀i,T i*T i=Q i+Q i)
    (hTQ : ∀i j,T i*Q j=0) (hQT : ∀i j,Q i*T j=0) :
    let e := T 0+T 1+T 2
    let d := Q 0+Q 1+Q 2+T 0*T 1+T 0*T 2+T 1*T 2
    let c := T 0*T 1*T 2
    e*e=d+d ∧ e*d=c+c+c ∧ d*e=c+c+c ∧ e*c=0 ∧ c*e=0 := by
  dsimp only
  have h10 := (hcomm 1 0).eq
  have h20 := (hcomm 2 0).eq
  have h21 := (hcomm 2 1).eq
  have h10L (y : B) : T 1*(T 0*y)=T 0*(T 1*y) := by rw [←mul_assoc,h10,mul_assoc]
  have h20L (y : B) : T 2*(T 0*y)=T 0*(T 2*y) := by rw [←mul_assoc,h20,mul_assoc]
  have h21L (y : B) : T 2*(T 1*y)=T 1*(T 2*y) := by rw [←mul_assoc,h21,mul_assoc]
  have hsqL (i : Fin 3) (y : B) : T i*(T i*y)=(Q i+Q i)*y := by
    rw [←mul_assoc,hsquare]
  have hTQL (i j : Fin 3) (y : B) : T i*(Q j*y)=0 := by rw [←mul_assoc,hTQ,zero_mul]
  have hQTL (i j : Fin 3) (y : B) : Q i*(T j*y)=0 := by rw [←mul_assoc,hQT,zero_mul]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals noncomm_ring [h10,h20,h21,h10L,h20L,h21L,hsquare,hsqL,hTQ,hQT,hTQL,hQTL]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalTripleCubicRelations
