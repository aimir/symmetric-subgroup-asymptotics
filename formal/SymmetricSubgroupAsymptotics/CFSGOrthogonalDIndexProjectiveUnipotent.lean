import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylow
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter

/-! The original central quotient is injective on the SAME literal D
unipotent subgroup. Hence its projected defining-characteristic Sylow
has the original U, including its centre, as an actual group chart.
No projective automorphism is assumed to lift to the matrix group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveUnipotent
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDIndexSylow
variable (K : Type) [Field K]

def projection (s : ℕ) : elementaryRootGroup K (s + 4) →* elementaryProjective K (s + 4) :=
  QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))

def projectiveUnipotent (s : ℕ) : Subgroup (elementaryProjective K (s + 4)) :=
  (unipotent K (s + 4)).map (projection K s)

def projectiveUnipotentMap (s : ℕ) : unipotent K (s + 4) →* projectiveUnipotent K s where
  toFun u := ⟨projection K s u.val, ⟨u.val, u.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (projection K s))
  map_mul' u v := Subtype.ext (map_mul (projection K s) u.val v.val)

theorem projectiveUnipotentMap_injective (s : ℕ) :
    Function.Injective (projectiveUnipotentMap K s) := by
  apply (projectiveUnipotentMap K s).ker_eq_bot_iff.mp
  apply bot_unique
  intro u hu
  change projectiveUnipotentMap K s u = 1 at hu
  have hp : projection K s u.val = 1 := congrArg Subtype.val hu
  have hc : u.val ∈ Subgroup.center (elementaryRootGroup K (s + 4)) :=
    (QuotientGroup.eq_one_iff _).mp hp
  obtain ⟨a, ha⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) u.val).mp hc
  have hdiag := u.property.2 (Sum.inl (0 : Fin (s + 4)))
  change (u.val.val : Mat K (s + 4)) (Sum.inl (0 : Fin (s + 4)))
    (Sum.inl (0 : Fin (s + 4))) = 1 at hdiag
  rw [ha] at hdiag
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hdiag
  change u = 1
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [ha, hdiag, one_smul]
  rfl

theorem projectiveUnipotentMap_surjective (s : ℕ) :
    Function.Surjective (projectiveUnipotentMap K s) := by
  rintro ⟨x, u, hu, he⟩
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

def unipotentProjectiveEquiv (s : ℕ) : unipotent K (s + 4) ≃* projectiveUnipotent K s :=
  MulEquiv.ofBijective (projectiveUnipotentMap K s)
    ⟨projectiveUnipotentMap_injective K s, projectiveUnipotentMap_surjective K s⟩

theorem unipotentProjectiveEquiv_val (s : ℕ) (u : unipotent K (s + 4)) :
    ((unipotentProjectiveEquiv K s u : projectiveUnipotent K s) :
      elementaryProjective K (s + 4)) = projection K s u.val := rfl

def projectiveSylow [Finite K] (s p : ℕ) [Fact p.Prime] [CharP K p] :
    Sylow p (elementaryProjective K (s + 4)) :=
  (unipotentSylow K s p).mapSurjective (f := projection K s) (QuotientGroup.mk'_surjective _)

@[simp] theorem projectiveSylow_coe [Finite K] (s p : ℕ) [Fact p.Prime] [CharP K p] :
    (projectiveSylow K s p : Subgroup (elementaryProjective K (s + 4))) =
      projectiveUnipotent K s := rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveUnipotent
