import SymmetricSubgroupAsymptotics.FourPairY1ActualFrame
import SymmetricSubgroupAsymptotics.FiniteCayleyMaps
import SymmetricSubgroupAsymptotics.ScalarFourRepeatedHeadModel

/-! The selected Y1 central-quotient map uses the existing96source rows
and only original-generator transitions. The target is the existing actual
A4 fiber product; no second graph/group closure or normal census is built. -/
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY1RepeatedHeadMap
open PrimitiveAffineEightFrameRow21TopCertificate NaturalS4
private abbrev A := NaturalA4ScalarFourHead.G
private def pairValues : Fin 5 → Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) :=
  ![(c2,c1),(c3,c2),(c2,c1),
    (Equiv.swap 0 1 * Equiv.swap 1 3,Equiv.swap 0 1 * Equiv.swap 1 3),(c1,1)]
private theorem even_left_checked : ∀ j : Fin 5,
    (pairValues j).1 ∈ alternatingGroup (Fin 4) := by
  intro j
  change Equiv.Perm.sign (pairValues j).1=1
  revert j
  decide +kernel
private theorem even_right_checked : ∀ j : Fin 5,
    (pairValues j).2 ∈ alternatingGroup (Fin 4) := by
  intro j
  change Equiv.Perm.sign (pairValues j).2=1
  revert j
  decide +kernel
private def leftValue (j : Fin 5) : A := ⟨(pairValues j).1,even_left_checked j⟩
private def rightValue (j : Fin 5) : A := ⟨(pairValues j).2,even_right_checked j⟩
private theorem equal_top_checked : ∀ j : Fin 5,
    NaturalA4ScalarFourHead.top (leftValue j) = NaturalA4ScalarFourHead.top (rightValue j) := by
  decide +kernel

def images (j : Fin 5) : ScalarFourRepeatedHeadModel.G :=
  ⟨(leftValue j,rightValue j),equal_top_checked j⟩

private def values (i : Fin 96) : ScalarFourRepeatedHeadModel.G :=
  ((certificate.words i).map images).prod
private def leftPoint (g : ScalarFourRepeatedHeadModel.G) (x : Fin 4) : Fin 4 :=
  ((g : A × A).1 : Equiv.Perm (Fin 4)) x
private def rightPoint (g : ScalarFourRepeatedHeadModel.G) (x : Fin 4) : Fin 4 :=
  ((g : A × A).2 : Equiv.Perm (Fin 4)) x

private theorem next_left_checked : ∀ (i : Fin 96) (j : Fin 5) (x : Fin 4),
    leftPoint (values (certificate.next i j)) x = leftPoint (values i * images j) x := by
  decide +kernel
private theorem next_right_checked : ∀ (i : Fin 96) (j : Fin 5) (x : Fin 4),
    rightPoint (values (certificate.next i j)) x = rightPoint (values i * images j) x := by
  decide +kernel
private theorem identity_left_checked : ∀ x : Fin 4,
    leftPoint (values certificate.identity) x = x := by decide +kernel
private theorem identity_right_checked : ∀ x : Fin 4,
    rightPoint (values certificate.identity) x = x := by decide +kernel

private theorem next_equation (i : Fin 96) (j : Fin 5) :
    values (certificate.next i j) = values i * images j := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Equiv.ext (next_left_checked i j)
  · apply Subtype.ext
    exact Equiv.ext (next_right_checked i j)
private theorem identity_equation : values certificate.identity = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Equiv.ext identity_left_checked
  · apply Subtype.ext
    exact Equiv.ext identity_right_checked

local instance sourceGroup : Group Source := group

/-- A genuine homomorphism on the already checked original96-state group. -/
def sourceMap : Source →* ScalarFourRepeatedHeadModel.G :=
  certificate.checkedHom values images next_equation rows_injective
    previousRow previous_checked identity_equation

/-- The same homomorphism installed on the original eight-point subgroup. -/
def originalMap : FourPairY1ActualFrame.Original →* ScalarFourRepeatedHeadModel.G :=
  sourceMap.comp originalEquiv.symm.toMonoidHom

end SymmetricSubgroupAsymptotics.FourPairY1RepeatedHeadMap
end
