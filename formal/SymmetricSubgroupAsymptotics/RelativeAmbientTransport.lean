import SymmetricSubgroupAsymptotics.RelativeSecondIsomorphism

/-! Relative character heads transport through the original ambient map.
In particular the quotient ambient of a block action is identified with
its actual permutation range; the normal image and its conjugation are
transported together. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
variable {A B : Type*} [Group A] [Group B]

def relativeActionCharactersEquiv (π : A →* B) (hπ : Function.Surjective π)
    (M : Subgroup B) [M.Normal] :
    primeActionCharacters p ((MulAut.conjNormal (H := M)).comp π) ≃ₗ[ZMod p]
      primeRelativeCharacters p M where
  toFun χ := ⟨χ.1,by
    intro b m
    obtain ⟨a,rfl⟩ := hπ b
    exact χ.2 a m⟩
  invFun χ := ⟨χ.1,fun a m => χ.2 (π a) m⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def relativeCharacterEquivariantCongr (π : A →* B) (hπ : Function.Surjective π)
    (N : Subgroup A) (M : Subgroup B) [N.Normal] [M.Normal]
    (e : N ≃* M)
    (he : ∀ a n, e (MulAut.conjNormal a n) = MulAut.conjNormal (π a) (e n)) :
    primeRelativeCharacters p M ≃ₗ[ZMod p] primeRelativeCharacters p N :=
  (relativeActionCharactersEquiv p π hπ M).symm.trans
    ((primeActionCharacterCongr p e MulAut.conjNormal
      ((MulAut.conjNormal (H := M)).comp π) he).trans
        (normalChainSourceCharactersEquiv N p))

def normalAmbientEquiv (e : A ≃* B) (N : Subgroup A) (M : Subgroup B)
    (he : N.map e.toMonoidHom = M) : N ≃* M :=
  (N.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr he)

@[simp] theorem normalAmbientEquiv_coe (e : A ≃* B) (N : Subgroup A) (M : Subgroup B)
    (he : N.map e.toMonoidHom = M) (n : N) :
    (normalAmbientEquiv e N M he n : B) = e (n:A) := rfl

def relativeCharacterAmbientCongr (e : A ≃* B) (N : Subgroup A) (M : Subgroup B)
    [N.Normal] [M.Normal] (he : N.map e.toMonoidHom = M) :
    primeRelativeCharacters p M ≃ₗ[ZMod p] primeRelativeCharacters p N :=
  relativeCharacterEquivariantCongr p e.toMonoidHom e.surjective N M
    (normalAmbientEquiv e N M he) (by
      intro a n
      apply Subtype.ext
      change e (a*(n:A)*a⁻¹) = e a*e (n:A)*(e a)⁻¹
      simp only [map_mul,map_inv])

section Range
variable {C : Type*} [Group C] (φ : A →* C) (N : Subgroup A) [N.Normal]

def originalNormalRange : Subgroup φ.range := N.map φ.rangeRestrict

instance originalNormalRange_normal : (originalNormalRange φ N).Normal :=
  Subgroup.Normal.map inferInstance _ φ.rangeRestrict_surjective

theorem originalNormalRange_map :
    (normalChainQuotient φ.ker N).map (QuotientGroup.quotientKerEquivRange φ).toMonoidHom =
      originalNormalRange φ N := by
  change (N.map (QuotientGroup.mk' φ.ker)).map _ = _
  rw [Subgroup.map_map]
  rfl

/-- The normal section of the original quotient ambient and its actual
permutation image have precisely the same invariant characters. -/
def originalNormalRangeCharacters :
    primeRelativeCharacters p (originalNormalRange φ N) ≃ₗ[ZMod p]
      primeRelativeCharacters p (normalChainQuotient φ.ker N) :=
  relativeCharacterAmbientCongr p (QuotientGroup.quotientKerEquivRange φ)
    (normalChainQuotient φ.ker N) (originalNormalRange φ N)
    (originalNormalRange_map φ N)

theorem primeRelativeHead_original_range :
    Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient φ.ker N)) =
      Module.finrank (ZMod p) (primeRelativeCharacters p (originalNormalRange φ N)) :=
  (originalNormalRangeCharacters p φ N).finrank_eq.symm

end Range
end SymmetricSubgroupAsymptotics
