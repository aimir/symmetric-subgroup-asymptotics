import SymmetricSubgroupAsymptotics.CFSGSuzukiOriginalTorusAction
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentCharacteristicLayers

/-! The original torus acts on the actual unipotent subgroup. The two
coordinate weights are recorded on the actual subtype, for intrinsic
automorphism reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters CFSGSuzukiTorus

def torusAction (m : ℕ) (c : (Field m)ˣ) : unipotentSubgroup m→*unipotentSubgroup m where
  toFun g := ⟨torusElement m c*g.val*(torusElement m c)⁻¹,by
    obtain ⟨a,b,hg⟩ := g.property
    rw [hg,original_torus_conjugation]
    exact ⟨_,_,rfl⟩⟩
  map_one' := Subtype.ext (map_one (MulAut.conj (torusElement m c)))
  map_mul' g h := Subtype.ext (map_mul (MulAut.conj (torusElement m c)) g.val h.val)

theorem torusAction_coordinateElement (m : ℕ) (c : (Field m)ˣ) (a b : Field m) :
    torusAction m c (coordinateElement m a b)=
      coordinateElement m ((c : Field m)⁻¹*a)
        (((c : Field m)*theta m (c : Field m))⁻¹*b) :=
  Subtype.ext (original_torus_conjugation m c a b)

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
