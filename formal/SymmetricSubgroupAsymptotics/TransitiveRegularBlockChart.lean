import SymmetricSubgroupAsymptotics.PermutationalWreathTransport
import Mathlib.Data.Fintype.EquivFin

/-! A transitive block image whose order equals the block count has its
actual regular chart. Any group isomorphism then transports it to the
regular canonical top, without searching for a permutation conjugator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TransitiveRegularBlockChart
variable {Q R I : Type} [Group Q] [Group R] [MulAction Q I]
  [Fintype Q] [Fintype I]
variable (i₀ : I) (htrans : ∀ i : I, ∃ q : Q, q • i₀=i)
  (hcard : Fintype.card Q=Fintype.card I)

def orbit : Q ≃ I := Equiv.ofBijective (fun q : Q => q • i₀)
  ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨htrans,hcard⟩)

include htrans hcard in
theorem orbit_symm_smul (q : Q) (i : I) :
    (orbit i₀ htrans hcard).symm (q • i) =
      q * (orbit i₀ htrans hcard).symm i := by
  apply (orbit i₀ htrans hcard).injective
  rw [(orbit i₀ htrans hcard).apply_symm_apply]
  change q • i = (q * (orbit i₀ htrans hcard).symm i) • i₀
  rw [mul_smul]
  exact congrArg (fun j : I => q • j) ((orbit i₀ htrans hcard).apply_symm_apply i).symm

/-- The block chart is tied to the actual orbit map and chosen group chart. -/
def chart (e : Q ≃* R) : I ≃ R := (orbit i₀ htrans hcard).symm.trans e.toEquiv

theorem chart_equivariant (e : Q ≃* R) (q : Q) (i : I) :
    chart i₀ htrans hcard e (q • i) = e q * chart i₀ htrans hcard e i := by
  change e ((orbit i₀ htrans hcard).symm (q • i)) =
    e q * e ((orbit i₀ htrans hcard).symm i)
  rw [orbit_symm_smul, e.map_mul]
end SymmetricSubgroupAsymptotics.TransitiveRegularBlockChart
