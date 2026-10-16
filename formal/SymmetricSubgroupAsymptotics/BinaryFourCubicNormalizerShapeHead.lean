import SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerPointShapes

/-! Original external local planes retain their exact source and twist.
Only actual point conjugacy to the tiny normalized shapes is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerShapeHead
open BinaryFourCubicNormalizerPointShapes
variable {G X L V : Type} [Group G] [Finite G] [MulAction G X]
  [MulAction.IsPretransitive G X] [Group L] [Finite L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem head_of_shape (e : X ≃ Points) (P : Sylow 3 G) (s g : G)
    (hP : (P : Subgroup G) = Subgroup.zpowers s)
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (t : Equiv.Perm Points)
    (hs : e.permCongrHom ((MulAction.toPermHom G X) s) = BinaryFourCubicNormalizerPointShapes.rotation)
    (ht : e.permCongrHom ((MulAction.toPermHom G X) g) = t)
    {n : ℕ} (representative : Fin n → Points)
    (hcover : ∀ z : Points, BinaryFourCubicNormalizerPointShapes.rotation z = z ∨
      ∃ j : Fin n, ∃ a : Fin 3, ∃ b : Fin 2,
        (BinaryFourCubicNormalizerPointShapes.rotation^a.val * t^b.val) (representative j) = z)
    (x : X) (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2*n := by
  let gamma : G →* Equiv.Perm Points :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hsg : gamma s = BinaryFourCubicNormalizerPointShapes.rotation := hs
  have htg : gamma g = t := ht
  have hsP : s ∈ (P : Subgroup G) := by
    rw [hP]
    exact Subgroup.mem_zpowers s
  have cover : ∀ z : X, z ∈ MulAction.fixedPoints P X ∨
      ∃ j : Fin n, z ∈ MulAction.orbit
        ↥((P : Subgroup G) ⊔ Subgroup.zpowers g) (e.symm (representative j)) := by
    intro z
    rcases hcover (e z) with hfix | ⟨j,a,b,hword⟩
    · left
      have hz : s • z = z := by
        apply e.injective
        have he := congrArg (fun q : Equiv.Perm Points => q (e z)) hsg
        change e (s • e.symm (e z)) = BinaryFourCubicNormalizerPointShapes.rotation (e z) at he
        rw [e.symm_apply_apply] at he
        exact he.trans hfix
      have hle : Subgroup.zpowers s ≤ MulAction.stabilizer G z :=
        Subgroup.zpowers_le.mpr hz
      intro p
      exact hle (hP ▸ p.2)
    · right
      let w : G := s^a.val * g^b.val
      have hw : w ∈ (P : Subgroup G) ⊔ Subgroup.zpowers g :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left ((P : Subgroup G).pow_mem hsP _))
          (Subgroup.mem_sup_right ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) _))
      refine ⟨j,MulAction.mem_orbit_iff.mpr ⟨⟨w,hw⟩,?_⟩⟩
      apply e.injective
      change gamma w (representative j) = e z
      have he : gamma w = BinaryFourCubicNormalizerPointShapes.rotation^a.val * t^b.val := by
        simp only [w,map_mul,map_pow,hsg,htg]
      rw [he]
      exact hword
  exact BinaryCoinducedNormalizerPointCover.head_le_twice_cover_on_points
    x P g hg (fun j => e.symm (representative j)) cover f hf rho hL hdim hrho B

theorem translation_head_le_six (e : X ≃ Points) (P : Sylow 3 G) (s g : G)
    (hP : (P : Subgroup G) = Subgroup.zpowers s)
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (v : BinaryFourBlockAugmentation.Local) (hv : v ≠ 0)
    (hs : e.permCongrHom ((MulAction.toPermHom G X) s) = BinaryFourCubicNormalizerPointShapes.rotation)
    (ht : e.permCongrHom ((MulAction.toPermHom G X) g) = translation v)
    (x : X) (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 6 :=
  head_of_shape e P s g hP hg (translation v) hs ht (translationRepresentatives v)
    (translation_cover v hv) x f hf rho hL hdim hrho B

theorem reflection_head_le_eight (e : X ≃ Points) (P : Sylow 3 G) (s g : G)
    (hP : (P : Subgroup G) = Subgroup.zpowers s)
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hs : e.permCongrHom ((MulAction.toPermHom G X) s) = BinaryFourCubicNormalizerPointShapes.rotation)
    (ht : e.permCongrHom ((MulAction.toPermHom G X) g) = reflection)
    (x : X) (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 8 :=
  head_of_shape e P s g hP hg reflection hs ht reflectionRepresentatives
    reflection_cover x f hf rho hL hdim hrho B

end SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerShapeHead
end
