import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativeVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralAction
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralAction

/-! Native positive C3 point lifts match the SAME F4 central-coordinate
shears, including the genuine long quadratic correction. This is a
coordinate identity, without any assertion that the whole native C3
has an actual F4 lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativePointCoordinates
open CFSGFFourBinaryLeviNativeVectorCoordinates CFSGFFourBinaryShortLeviCentralAction
open CFSGFFourBinaryLongLeviCentralAction CFSGSymplecticBinaryPointTailAction
variable (K : Type) [Field K] [CharP K 2]
private abbrev Raw := K × ((Fin 3 → K) × (Fin 3 → K))
private theorem short_dot (n : Fin 2) (a : K) (u v : Fin 3 → K) :
    dotProduct (u+Pi.single n.succ (a*u n.castSucc))
      (v+Pi.single n.castSucc (a*v n.succ)) = dotProduct u v := by
  have hne : n.succ ≠ n.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    change n.val+1=n.val at hv
    omega
  calc
    _=dotProduct u v+(a*u n.castSucc*v n.succ+a*u n.castSucc*v n.succ) := by
      simp only [add_dotProduct,dotProduct_add,dotProduct_single,single_dotProduct,
        Pi.add_apply]
      rw [Pi.single_eq_of_ne (Ne.symm hne)]
      ring
    _=dotProduct u v := by rw [CharTwo.add_self_eq_zero,add_zero]
omit [CharP K 2] in
private theorem long_dot (a : K) (u v : Fin 3 → K) :
    dotProduct u (v+Pi.single 2 (a*u 2))=dotProduct u v+a*(u 2)^2 := by
  rw [dotProduct_add,dotProduct_single]
  ring

theorem native_short_point [Finite K] (hK : Nat.card K=2)
    (n : Fin 2) (a : K) (x : Raw K) :
    let y := pointLinearHom K hK 3 (nativePositive K n.castSucc a) (x.2,x.1)
    (y.2,y.1) = (shortShear K n a (Multiplicative.ofAdd x)).toAdd := by
  have hy : pointLinearHom K hK 3 (nativePositive K n.castSucc a) (x.2,x.1) =
      ((x.2.1+Pi.single n.succ (a*x.2.1 n.castSucc),
        x.2.2+Pi.single n.castSucc (a*x.2.2 n.succ)),x.1) := by
    rw [pointLinearHom_apply,native_short_vector]
    apply Prod.ext
    · rfl
    · change x.1+dotProduct x.2.1 x.2.2+
          dotProduct (x.2.1+Pi.single n.succ (a*x.2.1 n.castSucc))
            (x.2.2+Pi.single n.castSucc (a*x.2.2 n.succ))=x.1
      rw [short_dot,add_assoc,CharTwo.add_self_eq_zero,add_zero]
  dsimp only
  rw [hy]
  rfl

theorem native_long_point [Finite K] (hK : Nat.card K=2) (a : K) (x : Raw K) :
    let y := pointLinearHom K hK 3 (nativePositive K 2 a) (x.2,x.1)
    (y.2,y.1) = (longShear K a (Multiplicative.ofAdd x)).toAdd := by
  have hy : pointLinearHom K hK 3 (nativePositive K 2 a) (x.2,x.1) =
      ((x.2.1,x.2.2+Pi.single 2 (a*x.2.1 2)),x.1+a*(x.2.1 2)^2) := by
    rw [pointLinearHom_apply,native_long_vector]
    apply Prod.ext
    · rfl
    · change x.1+dotProduct x.2.1 x.2.2+
          dotProduct x.2.1 (x.2.2+Pi.single 2 (a*x.2.1 2))=x.1+a*(x.2.1 2)^2
      rw [long_dot]
      calc
        _=x.1+a*(x.2.1 2)^2+(dotProduct x.2.1 x.2.2+dotProduct x.2.1 x.2.2) := by ring
        _=_ := by rw [CharTwo.add_self_eq_zero,add_zero]
  dsimp only
  rw [hy]
  rfl

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativePointCoordinates
