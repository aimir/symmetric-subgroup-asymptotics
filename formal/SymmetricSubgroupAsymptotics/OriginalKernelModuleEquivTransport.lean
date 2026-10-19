import SymmetricSubgroupAsymptotics.Non2LiftBound

/-! Change only the coordinates of the retained original elementary
kernel. Source, quotient map, and every original normal subgroup remain
literal; the change is an actual intertwining equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G Q : Type} [Group G] [Group Q]
    {pi : G →* Q} {A B : Rep.{0} (ZMod 2) Q}
    (E : OriginalKernelModuleChart pi A) (e : B.ρ.Equiv A.ρ)

def ofModuleEquiv : OriginalKernelModuleChart pi B where
  equiv := e.toLinearEquiv.toAddEquiv.toMultiplicative.trans E.equiv
  conjugate g v := by
    change E.equiv (Multiplicative.ofAdd (e (B.ρ (pi g) v)))=
      g*E.equiv (Multiplicative.ofAdd (e v))*g⁻¹
    have h := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (pi g) v
    have h' : e (B.ρ (pi g) v) = A.ρ (pi g) (e v) := h
    exact (congrArg (fun w : A => (E.equiv (Multiplicative.ofAdd w) : G)) h').trans
      (E.conjugate g (e v))
end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
