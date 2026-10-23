import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleOrbitFlags
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalRootSupport

/-! The positive E6 roots of zero orbit-excluded degree are EXACTLY
the one or two simple roots in that orbit. Positivity kills outside
coordinates; orthogonality and norm two identify the surviving root.
This is not a root census and has no coefficient-field hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitZeroRoots
open CFSGE6GeckSimpleOrbitFlags CFSGTwistedE6RelativeWeylOrbits
open CFSGNormTwoCoordinateOrthogonalRootSupport CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
local notation "A" => CartanMatrix.E₆

theorem orbit_nodes_orthogonal (a : Fin 4) :
    ∀i∈orbitWord a,∀j∈orbitWord a,i≠j→A j i=0 := by
  fin_cases a <;> decide

theorem orbitHeight_nonneg (a : Fin 4) (x : Fin 6→ℤ) (hx : ∀i,0≤x i) :
    0≤orbitHeight a x := by
  have h0:=hx 0;have h1:=hx 1;have h2:=hx 2
  have h3:=hx 3;have h4:=hx 4;have h5:=hx 5
  fin_cases a
  · change 0≤x 1+x 2+x 3+x 4
    omega
  · change 0≤x 0+x 1+x 3+x 5
    omega
  · change 0≤x 0+x 1+x 2+x 4+x 5
    omega
  · change 0≤x 0+x 2+x 3+x 4+x 5
    omega

theorem orbitHeight_zero_support (a : Fin 4) (x : Fin 6→ℤ)
    (hx : ∀i,0≤x i) (hz : orbitHeight a x=0) :
    ∀i,i∉orbitWord a→x i=0 := by
  have h0:=hx 0;have h1:=hx 1;have h2:=hx 2
  have h3:=hx 3;have h4:=hx 4;have h5:=hx 5
  fin_cases a
  · change x 1+x 2+x 3+x 4=0 at hz
    intro i hi
    fin_cases i
    · exact False.elim (hi (by decide))
    · change x 1=0;omega
    · change x 2=0;omega
    · change x 3=0;omega
    · change x 4=0;omega
    · exact False.elim (hi (by decide))
  · change x 0+x 1+x 3+x 5=0 at hz
    intro i hi
    fin_cases i
    · change x 0=0;omega
    · change x 1=0;omega
    · exact False.elim (hi (by decide))
    · change x 3=0;omega
    · exact False.elim (hi (by decide))
    · change x 5=0;omega
  · change x 0+x 1+x 2+x 4+x 5=0 at hz
    intro i hi
    fin_cases i
    · change x 0=0;omega
    · change x 1=0;omega
    · change x 2=0;omega
    · exact False.elim (hi (by decide))
    · change x 4=0;omega
    · change x 5=0;omega
  · change x 0+x 2+x 3+x 4+x 5=0 at hz
    intro i hi
    fin_cases i
    · change x 0=0;omega
    · exact False.elim (hi (by decide))
    · change x 2=0;omega
    · change x 3=0;omega
    · change x 4=0;omega
    · change x 5=0;omega

theorem zero_orbit_positive_root_simple (a : Fin 4) (k : Roots A)
    (hk : ∀i,0≤k.val i) (hz : orbitHeight a k.val=0) :
    ∃i∈orbitWord a,k=(E6Index i : Roots A) := by
  obtain ⟨i,hi,he⟩ := positive_root_supported_on_orthogonal_simples A CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite {i | i∈orbitWord a}
    (orbit_nodes_orthogonal a) k hk (orbitHeight_zero_support a k.val hk hz)
  exact ⟨i,hi,he⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitZeroRoots
