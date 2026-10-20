import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierWordCertificate
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralKernelOrbitCover
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralOriginalQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! The shared original-quotient endpoint for selected signed-S4 word
certificates. A physical two-orbit cover controls every correlated normal
subkernel. Actual commutator words control the whole kernel coinvariants;
the normal-image dichotomy keeps the top sign in the same two slots. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
local instance schreierSocles_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
namespace SymmetricPairSchreierWordData
variable {n : ℕ} {generators : Fin n → Equiv.Perm (Fin 12)}
  {D : SymmetricPairGeneratorData generators}
  (C : SymmetricPairSchreierWordData generators D)

include C in
theorem original_quotientSocle_of_orbitCover
    (cubic : Subgroup.closure (Set.range generators))
    (representative : Fin 2 → Fin 6)
    (hcoverPoints : ∀ x : Fin 6, ∃ (j : Fin 2) (k : ℕ),
      ((D.frame.top cubic)^k) (representative j)=x)
    (N : Subgroup (Subgroup.closure (Set.range generators))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range generators)) ⧸ N) 2 := by
  let U := Subgroup.closure (Set.range generators)
  let F : BinaryPairFrame U (Fin 6) := D.frame
  letI : MulAction U (Fin 6) := MulAction.compHom (Fin 6) F.top
  let bits : D.beta.ker →* Multiplicative (Fin 6 → ZMod 2) :=
    F.bitsHom.comp (Subgroup.inclusion D.beta_kernel.le)
  have hi : Function.Injective bits :=
    F.bitsHom_injective.comp (Subgroup.inclusion_injective D.beta_kernel.le)
  have hK : IsMulCommutative D.beta.ker := IsMulCommutative.of_comm fun k l => by
    apply hi
    rw [map_mul,map_mul,mul_comm]
  have hKtwo : IsPGroup 2 D.beta.ker := F.kernel_isPGroup.of_injective
    (Subgroup.inclusion D.beta_kernel.le) (Subgroup.inclusion_injective D.beta_kernel.le)
  have hpow (k : D.beta.ker) : (k : U)^2=1 := by
    have hk : k^2=1 := by
      apply hi
      rw [map_pow,map_one]
      apply Multiplicative.toAdd.injective
      change 2 • (bits k).toAdd=0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_self,zero_smul]
    exact congrArg Subtype.val hk
  have hcover : ∀ x : Fin 6, ∃ (j : Fin 2) (n : ℕ), cubic^n • representative j=x := by
    intro x
    obtain ⟨j,n,hn⟩ := hcoverPoints x
    refine ⟨j,n,?_⟩
    change F.top (cubic^n) (representative j)=x
    rw [map_pow]
    exact hn
  have hkernel (L : Subgroup U) [L.Normal] (hL : L ≤ D.beta.ker) :
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L) ≤ 2 :=
    normal_kernel_relativeHead_le_orbitCover F (fun _ _ => rfl)
      cubic representative hcover L (hL.trans D.beta_kernel.le)
  have hwhole : Module.finrank (ZMod 2) (primeRelativeCharacters 2 D.beta.ker) ≤ 1 := by
    let e : U ≃* U := MulEquiv.refl _
    have he : D.beta.ker.map e.toMonoidHom=F.top.ker := by
      change D.beta.ker.map (MonoidHom.id _)=F.top.ker
      rw [Subgroup.map_id]
      exact D.beta_kernel
    exact (relativeCharacterAmbientCongr 2 e D.beta.ker F.top.ker he).finrank_eq.symm.le.trans
      (SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural.SymmetricPairSchreierWordData.kernel_relative_head_le_one (C := C))
  exact quotientSocle_two_of_signed_symmetricTop (X := Fin 12) (by simp) D.beta D.beta_surjective
    hK hKtwo hpow hkernel hwhole N


end SymmetricPairSchreierWordData
end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
