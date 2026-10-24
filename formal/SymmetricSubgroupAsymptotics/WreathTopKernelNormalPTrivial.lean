import SymmetricSubgroupAsymptotics.WreathCompressionNormalPTrivial

/-! A faithful sign compression cannot conceal a top kernel when the
actual full local component has no normal p-subgroups.  The sign group
has exponent p; its coordinate maps therefore make the actual top
kernel a p-group.  All coordinates remain correlated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathTopKernelNormalPTrivial
open PermutationalWreathProduct

variable {A D S Q I : Type} [Group A] [Group D] [Group S] [Group Q]
    [MulAction Q I] (rho : A →* PermutationalWreathProduct D Q I)

abbrev topKernel : Subgroup A := (rightHom.comp rho).ker

def topCoordinate (i : I) : topKernel rho →* D where
  toFun k := (rho k.val).left i
  map_one' := by simp only [Subgroup.coe_one,map_one,one_left,Pi.one_apply]
  map_mul' k l := by
    change (rho (k.val * l.val)).left i = (rho k.val).left i * (rho l.val).left i
    rw [map_mul,mul_left]
    have hk : (rho k.val).right = 1 := k.property
    simp only [hk,inv_one,Pi.mul_apply,one_smul]

def signCoordinates (chi : D →* S) : topKernel rho →* (I → S) where
  toFun k i := chi (topCoordinate rho i k)
  map_one' := by
    funext i
    exact (chi.comp (topCoordinate rho i)).map_one
  map_mul' k l := by
    funext i
    exact (chi.comp (topCoordinate rho i)).map_mul k l

theorem signCoordinates_injective (chi : D →* S)
    (hcore : Compression.kernel rho chi = ⊥) :
    Function.Injective (signCoordinates rho chi) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hkcore : k.val ∈ Compression.kernel rho chi := by
    change mapBase chi (rho k.val) = 1
    apply PermutationalWreathProduct.ext
    · funext i
      exact congrFun hk i
    · exact k.property
  rw [hcore] at hkcore
  exact Subtype.ext hkcore

theorem topKernel_isPGroup (p : ℕ) (chi : D →* S)
    (hcore : Compression.kernel rho chi = ⊥) (hs : ∀ s : S, s ^ p = 1) :
    IsPGroup p (topKernel rho) := by
  have hpi : IsPGroup p (I → S) := by
    intro f
    refine ⟨1,?_⟩
    funext i
    simpa only [pow_one,Pi.pow_apply,Pi.one_apply] using hs (f i)
  exact hpi.of_injective (signCoordinates rho chi) (signCoordinates_injective rho chi hcore)

theorem topKernel_eq_bot (p : ℕ) (hrho : Function.Injective rho)
    (hfull : Compression.FullComponent rho)
    (hlocal : ∀ N : Subgroup D, N.Normal → IsPGroup p N → N = ⊥)
    (hK : IsPGroup p (topKernel rho)) : topKernel rho = ⊥ := by
  let phi : D →* PUnit.{1} := 1
  let e : phi.ker ≃* D :=
    { toFun := Subtype.val
      invFun := fun d => ⟨d,rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hlocal' : ∀ N : Subgroup phi.ker, N.Normal → IsPGroup p N → N = ⊥ := by
    intro N hn hp
    letI : N.Normal := hn
    let M : Subgroup D := N.comap e.symm.toMonoidHom
    have hM : IsPGroup p M := hp.comap_of_injective e.symm.toMonoidHom e.symm.injective
    have hMbot : M = ⊥ := hlocal M inferInstance hM
    apply le_antisymm ?_ bot_le
    intro z hz
    have hzM : e z ∈ M := by
      change e.symm (e z) ∈ N
      simpa only [MulEquiv.symm_apply_apply] using hz
    rw [hMbot] at hzM
    change z = 1
    apply e.injective
    simpa only [map_one] using hzM
  have hker : Compression.kernel rho phi = topKernel rho := by
    ext g
    constructor
    · intro hg
      have he : mapBase phi (rho g) = 1 := hg
      exact congrArg right he
    · intro hg
      change mapBase phi (rho g) = 1
      apply PermutationalWreathProduct.ext
      · rfl
      · exact hg
  rw [← hker]
  apply WreathCompressionNormalPTrivial.kernel_eq_bot rho phi p hrho hfull hlocal'
  rwa [hker]

theorem top_injective_of_sign_core_eq_bot (p : ℕ) (hrho : Function.Injective rho)
    (hfull : Compression.FullComponent rho)
    (hlocal : ∀ N : Subgroup D, N.Normal → IsPGroup p N → N = ⊥)
    (chi : D →* S) (hs : ∀ s : S, s ^ p = 1)
    (hcore : Compression.kernel rho chi = ⊥) :
    Function.Injective (rightHom.comp rho) := by
  exact (rightHom.comp rho).ker_eq_bot_iff.mp
    (topKernel_eq_bot rho p hrho hfull hlocal (topKernel_isPGroup rho p chi hcore hs))

end SymmetricSubgroupAsymptotics.WreathTopKernelNormalPTrivial
