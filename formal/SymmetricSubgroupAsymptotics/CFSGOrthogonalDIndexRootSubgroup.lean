import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus

/-! A literal one-parameter chain-root subgroup of the actual D
projective elementary group. Its field parameter survives the centre
quotient, as seen on the original off-diagonal matrix entry. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootSubgroup
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble CFSGTypeAElementaryMatrices
variable (K : Type) [Field K]

def first (s : ℕ) : Fin (s + 4) := 0
def second (s : ℕ) : Fin (s + 4) := ⟨1, by omega⟩
def third (s : ℕ) : Fin (s + 4) := ⟨2, by omega⟩

theorem first_ne_second (s : ℕ) : first s ≠ second s := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = 1 at hv
  omega

theorem first_ne_third (s : ℕ) : first s ≠ third s := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = 2 at hv
  omega

theorem second_ne_third (s : ℕ) : second s ≠ third s := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = 2 at hv
  omega

def firstSLHom (s : ℕ) : Multiplicative K →* Matrix.SpecialLinearGroup (Fin (s + 4)) K where
  toFun a := elementary (first_ne_second s) a.toAdd
  map_one' := elementary_zero (first_ne_second s)
  map_mul' a b := elementary_add (first_ne_second s) a.toAdd b.toAdd

def firstHom (s : ℕ) : Multiplicative K →* elementaryRootGroup K (s + 4) :=
  (doubleIntoElementary K (s + 4)).comp (firstSLHom K s)

theorem firstHom_val (s : ℕ) (a : Multiplicative K) :
    ((firstHom K s a).val : Mat K (s + 4)) =
      1 + a.toAdd • chainMatrix K (s + 4) (first s) (second s) :=
  doubleHom_elementary_val K (s + 4) (first s) (second s) (first_ne_second s) a.toAdd

def projectiveFirstHom (s : ℕ) : Multiplicative K →* elementaryProjective K (s + 4) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))).comp (firstHom K s)

theorem first_parameter_zero_of_central (s : ℕ) (a : Multiplicative K)
    (ha : firstHom K s a ∈ Subgroup.center (elementaryRootGroup K (s + 4))) : a.toAdd = 0 := by
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) (firstHom K s a)).mp ha
  have he := congrArg (fun A : Mat K (s + 4) => A (Sum.inl (first s)) (Sum.inl (second s))) hc
  rw [firstHom_val] at he
  simpa [chainMatrix, Matrix.one_apply, Matrix.single_apply, first_ne_second,
    Matrix.smul_apply, smul_eq_mul] using he

theorem projectiveFirstHom_injective (s : ℕ) : Function.Injective (projectiveFirstHom K s) := by
  apply (MonoidHom.ker_eq_bot_iff (projectiveFirstHom K s)).mp
  apply bot_unique
  intro a ha
  have hc : firstHom K s a ∈ Subgroup.center (elementaryRootGroup K (s + 4)) :=
    (QuotientGroup.eq_one_iff _).mp ha
  have hz := first_parameter_zero_of_central K s a hc
  exact (Subgroup.mem_bot).mpr (congrArg Multiplicative.ofAdd hz)

def projectiveFirstRoot (s : ℕ) : Subgroup (elementaryProjective K (s + 4)) :=
  (projectiveFirstHom K s).range

def projectiveFirstRootEquiv (s : ℕ) : Multiplicative K ≃* projectiveFirstRoot K s :=
  MonoidHom.ofInjective (projectiveFirstHom_injective K s)

theorem projectiveFirstRoot_card (s : ℕ) : Nat.card (projectiveFirstRoot K s) = Nat.card K := by
  calc
    Nat.card (projectiveFirstRoot K s) = Nat.card (Multiplicative K) :=
      Nat.card_congr (projectiveFirstRootEquiv K s).symm.toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootSubgroup
