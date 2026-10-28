import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group

/-! A literal commuting-swap certificate; no Coxeter classification is used. -/
namespace SymmetricSubgroupAsymptotics.ThreeArmCoxeterWordConjugacy
variable {G : Type*} [Group G]

theorem shuffle (a b c d R : G)
    (hac : Commute a c) (had : Commute a d) (hbd : Commute b d)
    (hRb : Commute R b) (hRc : Commute R c) (hRd : Commute R d) :
    (d*c*b*a*R)*(d*c*d*b*c*d) =
      (d*c*d*b*c*d)*(a*b*c*d*R) := by
  have hRC : Commute R (d*c*d*b*c*d) :=
    (((((hRd.mul_right hRc).mul_right hRd).mul_right hRb).mul_right hRc).mul_right hRd)
  have hs : b*a*d*c*d*b*c*d = d*b*c*d*a*b*c*d := by
    simp only [mul_assoc]
    rw [had.left_comm, hbd.left_comm, hac.left_comm, had.left_comm]
  calc
    (d*c*b*a*R)*(d*c*d*b*c*d) =
        (d*c*b*a)*(R*(d*c*d*b*c*d)) := mul_assoc _ _ _
    _ = (d*c*b*a)*((d*c*d*b*c*d)*R) := congrArg ((d*c*b*a)*·) hRC.eq
    _ = (d*c*d*b*c*d)*(a*b*c*d*R) := by
      simpa only [mul_assoc] using congrArg (fun x => d*c*x*R) hs

theorem conjugacy (a b c d R : G)
    (hac : Commute a c) (had : Commute a d) (hbd : Commute b d)
    (hRb : Commute R b) (hRc : Commute R c) (hRd : Commute R d) :
    (d*c*d*b*c*d)⁻¹*(d*c*b*a*R)*(d*c*d*b*c*d) = a*b*c*d*R := by
  rw [mul_assoc, shuffle a b c d R hac had hbd hRb hRc hRd]
  group
end SymmetricSubgroupAsymptotics.ThreeArmCoxeterWordConjugacy
