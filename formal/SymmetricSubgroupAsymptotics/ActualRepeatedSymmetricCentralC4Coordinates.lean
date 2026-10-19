import SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
import SymmetricSubgroupAsymptotics.BinaryPlaneScalarFourKernel

/-! Recognize an actual central cover of synchronized S4 coordinates.
The original central kernel is retained exactly; no splitting is inferred. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualRepeatedSymmetricCentralC4Coordinates
open BinaryPlanePermutationAffineEquiv BinaryPlaneScalarFourKernel
variable {Q : Type} [Group Q] {c d : ℕ}
  (u : Q →* (Fin d → Equiv.Perm Plane)) (j₀ : Fin d)
  (hcommon : ∀ g j, linearPart (u g j)=
    linearPart (u g j₀))

def top : Q →* Linear where
  toFun g := linearPart (u g j₀)
  map_one' := by rw [map_one]; exact map_one _
  map_mul' g h := by rw [map_mul]; exact map_mul _ _ _

private def localKernel (j : Fin d) : (top u j₀).ker →* linearPart.ker where
  toFun p := ⟨u (p : Q) j,(hcommon (p : Q) j).trans p.property⟩
  map_one' := by apply Subtype.ext; exact congrFun u.map_one j
  map_mul' p q := by apply Subtype.ext; exact congrFun (u.map_mul p q) j

def active : (top u j₀).ker →* (Fin d → ScalarFour) where
  toFun p j := coord (localKernel u j₀ hcommon j p)
  map_one' := by funext j; rw [map_one,map_one]; rfl
  map_mul' p q := by funext j; rw [map_mul,map_mul]; rfl

private theorem active_eq_one_iff (p : (top u j₀).ker) :
    active u j₀ hcommon p=1 ↔ u (p : Q)=1 := by
  constructor
  · intro hp
    funext j
    have he := congrFun hp j
    have hl : localKernel u j₀ hcommon j p=1 := coord_injective (by
      simpa only [map_one] using he)
    exact congrArg Subtype.val hl
  · intro hp
    funext j
    have hl : localKernel u j₀ hcommon j p=1 :=
      Subtype.ext (congrFun hp j)
    change coord (localKernel u j₀ hcommon j p)=1
    rw [hl,map_one]

/-- Both kernels consist of the same original target elements. -/
def centralKernelEquiv : (active u j₀ hcommon).ker ≃* u.ker where
  toFun z := ⟨((z : (top u j₀).ker) : Q),
    (active_eq_one_iff u j₀ hcommon z).mp z.property⟩
  invFun z :=
    ⟨⟨(z : Q),by
      change linearPart (u (z : Q) j₀)=1
      rw [z.property]
      exact map_one _⟩,
      (active_eq_one_iff u j₀ hcommon _).mpr z.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl
  map_mul' x y := by apply Subtype.ext; rfl

/-- A generator-level synchronized-coordinate witness yields the counting
structure, including nonsplit central extensions of repeated S4 models. -/
def coordinates
    (htop : Function.Surjective (top u j₀))
    (hcentral : ∀ z : u.ker, ∀ g : Q, (z : Q)*g=g*(z : Q))
    (z : u.ker →* (Fin c → Multiplicative (ZMod 4))) (hz : Function.Injective z) :
    ScalarFourCentralC4TopCoordinates Q Linear c d where
  top := top u j₀
  top_surjective := htop
  cubic := BinaryPlaneScalarFourKernel.cubic
  active := active u j₀ hcommon
  central v g := hcentral (centralKernelEquiv u j₀ hcommon v) g
  centralCoordinates := z.comp (centralKernelEquiv u j₀ hcommon).toMonoidHom
  centralCoordinates_injective := hz.comp (centralKernelEquiv u j₀ hcommon).injective
  cubic_action := by
    intro v hv p j
    have he : localKernel u j₀ hcommon j (MulAut.conjNormal v p)=
        MulAut.conjNormal (u v j) (localKernel u j₀ hcommon j p) := by
      apply Subtype.ext
      change u (v*(p : Q)*v⁻¹) j=(u v j)*(u (p : Q) j)*(u v j)⁻¹
      rw [map_mul,map_mul,map_inv]
      rfl
    change coord (localKernel u j₀ hcommon j (MulAut.conjNormal v p))=_
    rw [he]
    have ht : linearPart (u v j)=BinaryPlaneScalarFourKernel.cubic :=
      (hcommon v j).trans hv
    exact coord_conjugate (u v j) ht (localKernel u j₀ hcommon j p)
end SymmetricSubgroupAsymptotics.ActualRepeatedSymmetricCentralC4Coordinates
