import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentSylow

/-! The SAME relative Sylow injects into the actual central quotient.
Its projected subgroup is a Sylow, with its original centre transported
by a literal isomorphism. No quotient automorphism is assumed to lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveUnipotent
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeUnipotentSylow CFSGTwistedDRelativeCenter

abbrev Projective (s : ℕ) (q : CFSG.PrimePower) :=
  relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)

def projection (s : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup (s + 2) q →* Projective s q :=
  QuotientGroup.mk' (Subgroup.center (relativeRootGroup (s + 2) q))

def projectiveUnipotent (s : ℕ) (q : CFSG.PrimePower) : Subgroup (Projective s q) :=
  (unipotent s q).map (projection s q)

def projectiveUnipotentMap (s : ℕ) (q : CFSG.PrimePower) :
    unipotent s q →* projectiveUnipotent s q where
  toFun u := ⟨projection s q u.val, ⟨u.val, u.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (projection s q))
  map_mul' u v := Subtype.ext (map_mul (projection s q) u.val v.val)

theorem projectiveUnipotentMap_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (projectiveUnipotentMap s q) := by
  apply (projectiveUnipotentMap s q).ker_eq_bot_iff.mp
  apply bot_unique
  intro u hu
  change projectiveUnipotentMap s q u = 1 at hu
  have hp : projection s q u.val = 1 := congrArg Subtype.val hu
  have hc : u.val ∈ Subgroup.center (relativeRootGroup (s + 2) q) :=
    (QuotientGroup.eq_one_iff _).mp hp
  obtain ⟨a, ha⟩ := (relativeRootGroup_center_iff_scalar (s + 2) q u.val).mp hc
  have hdiag := u.property.2 (Sum.inl (0 : Fin (s + 4)))
  change (u.val.val : Mat (q.Extension 2) (s + 4)) (Sum.inl (0 : Fin (s + 4)))
    (Sum.inl (0 : Fin (s + 4))) = 1 at hdiag
  rw [ha] at hdiag
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hdiag
  change u = 1
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [ha, hdiag, one_smul]
  rfl

theorem projectiveUnipotentMap_surjective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Surjective (projectiveUnipotentMap s q) := by
  rintro ⟨x, u, hu, he⟩
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

def unipotentProjectiveEquiv (s : ℕ) (q : CFSG.PrimePower) :
    unipotent s q ≃* projectiveUnipotent s q :=
  MulEquiv.ofBijective (projectiveUnipotentMap s q)
    ⟨projectiveUnipotentMap_injective s q, projectiveUnipotentMap_surjective s q⟩

theorem unipotentProjectiveEquiv_val (s : ℕ) (q : CFSG.PrimePower) (u : unipotent s q) :
    ((unipotentProjectiveEquiv s q u : projectiveUnipotent s q) : Projective s q) =
      projection s q u.val := rfl

def projectiveSylow (s : ℕ) (q : CFSG.PrimePower) : Sylow q.prime (Projective s q) :=
  (unipotentSylow s q).mapSurjective (f := projection s q) (QuotientGroup.mk'_surjective _)

@[simp] theorem projectiveSylow_coe (s : ℕ) (q : CFSG.PrimePower) :
    (projectiveSylow s q : Subgroup (Projective s q)) = projectiveUnipotent s q := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveUnipotent
