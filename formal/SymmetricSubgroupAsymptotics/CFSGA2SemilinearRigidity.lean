import SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRigidity
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Ring.Aut
import Mathlib.Tactic.Ring

/-! Literal A2 incidence propagates positive semilinearity to the third
root, then determines every opposite-simple parameter with reciprocal
scalar. The actual-model consumers discharge both commutator identities. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGA2SemilinearRigidity
variable {K G : Type*} [Field K] [Group G]

theorem third_parameter_semilinear (u v w : K→G)
    (hcomm : ∀ a b, ⁅u a,v b⁆=w (a*b))
    (f : G→*G) (tau : RingAut K) (c d : K)
    (hfu : ∀ a, f (u a)=u (c*tau a))
    (hfv : ∀ a, f (v a)=v (d*tau a)) (a : K) :
    f (w a)=w ((c*d)*tau a) := by
  have ha : ⁅u a,v 1⁆=w a := by simpa only [mul_one] using hcomm a 1
  calc
    _=f ⁅u a,v 1⁆ := congrArg f ha.symm
    _=⁅u (c*tau a),v (d*tau 1)⁆ := by rw [map_commutatorElement,hfu,hfv]
    _=w ((c*tau a)*(d*tau 1)) := hcomm _ _
    _=_ := by rw [map_one]; congr 1; ring

theorem opposite_parameter_semilinear (u n w : K→G)
    (hu : Function.Injective u) (hcomm : ∀ a b, ⁅n a,w b⁆=u (a*b))
    (f : G→*G) (tau : RingAut K) (c d : K) (hc : c≠0) (hd : d≠0)
    (hfu : ∀ a, f (u a)=u (d*tau a))
    (hfw : ∀ a, f (w a)=w ((c*d)*tau a))
    (hfn : ∀ a, ∃ b, f (n a)=n b) (a : K) :
    f (n a)=n (c⁻¹*tau a) := by
  obtain ⟨b,hb⟩ := hfn a
  have he := congrArg f (hcomm a 1)
  rw [map_commutatorElement,hb,hfw,hfu,hcomm,map_one,mul_one] at he
  simp only [mul_one] at he
  have hp : b*(c*d)=d*tau a := hu he
  have hbc : b*c=tau a := by
    apply mul_right_cancel₀ hd
    simpa only [mul_assoc,mul_comm d (tau a)] using hp
  have hz : b=c⁻¹*tau a := by
    calc
      b=(b*c)*c⁻¹ := by rw [mul_assoc,mul_inv_cancel₀ hc,mul_one]
      _=tau a*c⁻¹ := by rw [hbc]
      _=c⁻¹*tau a := mul_comm _ _
  simpa only [hz] using hb

end SymmetricSubgroupAsymptotics.CFSGA2SemilinearRigidity
