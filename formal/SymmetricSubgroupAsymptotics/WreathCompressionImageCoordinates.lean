import SymmetricSubgroupAsymptotics.WreathTopKernelNormalPTrivial

/-! The literal image of a local compression has full coordinates in the
literal local image. This retains the actual correlated group and avoids
assuming the original compression is injective or its local map is onto
an ambient group larger than its range. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathCompressionImageCoordinates
open PermutationalWreathProduct

variable {A D L S Q I : Type} [Group A] [Group D] [Group L] [Group S] [Group Q]
    [MulAction Q I] (rho : A →* PermutationalWreathProduct D Q I) (phi : D →* L)

abbrev image : Subgroup (PermutationalWreathProduct L Q I) :=
  (Compression.map rho phi).range

def embedding : image rho phi →* PermutationalWreathProduct phi.range Q I where
  toFun w := ⟨fun i => ⟨w.val.left i,by
    obtain ⟨a,ha⟩ := w.property
    exact ⟨(rho a).left i,congrArg (fun z => z.left i) ha⟩⟩,w.val.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply Subtype.ext
      rfl
    · rfl
  map_mul' u v := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply Subtype.ext
      rfl
    · rfl

theorem embedding_injective : Function.Injective (embedding rho phi) := by
  intro u v h
  apply Subtype.ext
  apply PermutationalWreathProduct.ext
  · funext i
    exact congrArg (fun z : PermutationalWreathProduct phi.range Q I => (z.left i).val) h
  · exact congrArg (fun z : PermutationalWreathProduct phi.range Q I => z.right) h

theorem embedding_fullComponent (hfull : Compression.FullComponent rho) :
    Compression.FullComponent (embedding rho phi) := by
  intro i d
  obtain ⟨c,hc⟩ := d.property
  obtain ⟨a,ha,hai⟩ := hfull i c
  refine ⟨⟨Compression.map rho phi a,⟨a,rfl⟩⟩,ha,?_⟩
  apply Subtype.ext
  change phi ((rho a).left i) = d.val
  rw [hai,hc]

theorem embedding_to_ambient (w : image rho phi) :
    mapBase phi.range.subtype (embedding rho phi w) = w.val := rfl

theorem top_injective_of_sign_core_eq_bot (p : ℕ)
    (hfull : Compression.FullComponent rho)
    (hlocal : ∀ N : Subgroup phi.range, N.Normal → IsPGroup p N → N = ⊥)
    (chi : L →* S) (hs : ∀ s : S, s ^ p = 1)
    (hcore : Compression.kernel (image rho phi).subtype chi = ⊥) :
    Function.Injective (rightHom.comp (image rho phi).subtype) := by
  have hcore' : Compression.kernel (embedding rho phi) (chi.comp phi.range.subtype) = ⊥ := by
    have he : Compression.map (embedding rho phi) (chi.comp phi.range.subtype) =
        Compression.map (image rho phi).subtype chi := by
      apply MonoidHom.ext
      intro w
      rfl
    change (Compression.map (embedding rho phi) (chi.comp phi.range.subtype)).ker = ⊥
    rw [he]
    exact hcore
  exact WreathTopKernelNormalPTrivial.top_injective_of_sign_core_eq_bot
    (embedding rho phi) p (embedding_injective rho phi)
    (embedding_fullComponent rho phi hfull) hlocal (chi.comp phi.range.subtype) hs hcore'

end SymmetricSubgroupAsymptotics.WreathCompressionImageCoordinates
