import SymmetricSubgroupAsymptotics.PrimeEquivariantCharacters
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Relative heads along actual normal chains B≤C in A. The quotient is
the literal image of C in A/B and retains the conjugation action of A/B.
The exact identity keeps the extendible restriction image inside the
relative characters of the original B. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A : Type*} [Group A]
variable (B C : Subgroup A) [B.Normal] [C.Normal]

def normalChainQuotient : Subgroup (A ⧸ B) := C.map (QuotientGroup.mk' B)

instance normalChainQuotient_normal : (normalChainQuotient B C).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective B)

def normalChainMap : C →* normalChainQuotient B C where
  toFun c := ⟨QuotientGroup.mk' B (c:A),⟨c,c.2,rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [C.Normal] in
theorem normalChainMap_surjective : Function.Surjective (normalChainMap B C) := by
  rintro ⟨x,a,ha,rfl⟩
  exact ⟨⟨a,ha⟩,rfl⟩

def normalChainSourceAction : A →* MulAut C := MulAut.conjNormal

def normalChainTargetAction : A →* MulAut (normalChainQuotient B C) :=
  MulAut.conjNormal.comp (QuotientGroup.mk' B)

theorem normalChainMap_equivariant (a : A) (c : C) :
    normalChainMap B C (normalChainSourceAction C a c) =
      normalChainTargetAction B C a (normalChainMap B C c) := by
  apply Subtype.ext
  change QuotientGroup.mk' B (a*(c:A)*a⁻¹) =
    QuotientGroup.mk' B a * QuotientGroup.mk' B (c:A) * (QuotientGroup.mk' B a)⁻¹
  simp only [map_mul,map_inv]

def normalChainKernelEquiv (hBC : B≤C) : (normalChainMap B C).ker ≃* B where
  toFun x := ⟨(x.1:A),(QuotientGroup.eq_one_iff (N := B) (x.1:A)).mp
    (congrArg Subtype.val x.2)⟩
  invFun b := ⟨⟨(b:A),hBC b.2⟩,Subtype.ext
    ((QuotientGroup.eq_one_iff (N := B) (b:A)).mpr b.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (p : ℕ) [Fact p.Prime]

def normalChainSourceCharactersEquiv :
    primeActionCharacters p (normalChainSourceAction C) ≃ₗ[ZMod p]
      primeRelativeCharacters p C where
  toFun χ := ⟨χ.1,fun a c => χ.2 a c⟩
  invFun χ := ⟨χ.1,fun a c => χ.2 a c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def normalChainTargetCharactersEquiv :
    primeActionCharacters p (normalChainTargetAction B C) ≃ₗ[ZMod p]
      primeRelativeCharacters p (normalChainQuotient B C) where
  toFun χ := ⟨χ.1,by
    intro a c
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective B a
    exact χ.2 x c⟩
  invFun χ := ⟨χ.1,fun a c => χ.2 (QuotientGroup.mk' B a) c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def normalChainKernelCharactersEquiv (hBC : B≤C) :
    primeActionKernelCharacters p (normalChainMap B C) (normalChainSourceAction C)
      (normalChainTargetAction B C) (normalChainMap_equivariant B C) ≃ₗ[ZMod p]
        primeRelativeCharacters p B where
  toFun χ := ⟨χ.1.comp (normalChainKernelEquiv B C hBC).symm.toMonoidHom.toAdditive,by
    intro a b
    exact χ.2 a ((normalChainKernelEquiv B C hBC).symm b)⟩
  invFun χ := ⟨χ.1.comp (normalChainKernelEquiv B C hBC).toMonoidHom.toAdditive,by
    intro a b
    exact χ.2 a (normalChainKernelEquiv B C hBC b)⟩
  left_inv χ := by
    apply Subtype.ext
    ext b
    rfl
  right_inv χ := by
    apply Subtype.ext
    ext b
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual restriction into the relative characters of the original B. -/
def normalChainRestriction (hBC : B≤C) :
    primeActionCharacters p (normalChainSourceAction C) →ₗ[ZMod p]
      primeRelativeCharacters p B :=
  (normalChainKernelCharactersEquiv B C p hBC).toLinearMap.comp
    (primeActionRestriction p (normalChainMap B C) (normalChainSourceAction C)
      (normalChainTargetAction B C) (normalChainMap_equivariant B C))

def normalChainRetainedCharacters (hBC : B≤C) :
    Submodule (ZMod p) (primeRelativeCharacters p B) :=
  LinearMap.range (normalChainRestriction B C p hBC)

/-- Exact relative-head chain formula, retaining actual extendibility. -/
theorem primeRelativeHead_chain_eq [Finite A] (hBC : B≤C) :
    Module.finrank (ZMod p) (primeRelativeCharacters p C) =
      Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient B C)) +
        Module.finrank (ZMod p) (normalChainRetainedCharacters B C p hBC) := by
  have hk : LinearMap.ker (normalChainRestriction B C p hBC) =
      LinearMap.ker (primeActionRestriction p (normalChainMap B C) (normalChainSourceAction C)
        (normalChainTargetAction B C) (normalChainMap_equivariant B C)) := by
    ext χ
    simp only [LinearMap.mem_ker,normalChainRestriction,LinearMap.comp_apply]
    exact (normalChainKernelCharactersEquiv B C p hBC).injective.eq_iff' (map_zero _)
  have h := (normalChainRestriction B C p hBC).finrank_range_add_finrank_ker
  rw [hk,primeActionRestriction_ker p _ _ _ _ (normalChainMap_surjective B C),
    LinearMap.finrank_range_of_inj (primeActionInflation_injective p _ _ _ _
      (normalChainMap_surjective B C))] at h
  have hs := (normalChainSourceCharactersEquiv C p).finrank_eq
  have ht := (normalChainTargetCharactersEquiv B C p).finrank_eq
  rw [hs,ht] at h
  exact h.symm.trans (Nat.add_comm _ _)

/-- The ordinary relative-head inequality follows by enlarging the
retained annihilator only at the final dimension comparison. -/
theorem primeRelativeHead_chain_le [Finite A] (hBC : B≤C) :
    Module.finrank (ZMod p) (primeRelativeCharacters p C) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p B) +
        Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient B C)) := by
  rw [primeRelativeHead_chain_eq B C p hBC]
  exact (Nat.add_le_add_left (Submodule.finrank_le _) _).trans_eq (Nat.add_comm _ _)

end SymmetricSubgroupAsymptotics
