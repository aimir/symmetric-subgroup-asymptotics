import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathQuotientSocles
import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Exact original16T1932 quotient-socle bound two from its cyclic four-quartet
image. All four local Singers are short words in the two actual generators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles
open BinaryPlanePermutationAffineEquiv BinaryPlanePermutationWreathCoordinates
open BinaryPlaneWreathIrreducible BinaryPlaneWreathNormalGenerators
open Non2UnipotentPrefixFiniteMenu

abbrev Blocks := Subgroup.zpowers (finRotate 4)
def rotation : Blocks := ⟨finRotate 4,Subgroup.mem_zpowers _⟩
abbrev Point := BinaryPlanePermutationWreathCoordinates.W (R := Blocks) (I := Fin 4)
abbrev Affine := BinaryPlaneWreathNormalGenerators.Model (R := Blocks) (I := Fin 4)
abbrev Lin := BinaryPlaneWreathIrreducible.W (R := Blocks) (I := Fin 4)
def localPerm (g : Equiv.Perm (Fin 4)) : Equiv.Perm Plane :=
  BinaryThreeQuartetLiteralSocles.planeLabel.symm.permCongr g

def pointChart : Plane × Fin 4 ≃ Fin 16 :=
  ((Equiv.prodCongr BinaryThreeQuartetLiteralSocles.planeLabel (Equiv.refl (Fin 4))).trans
    (Equiv.prodComm (Fin 4) (Fin 4))).trans finProdFinEquiv

def action : Affine →* Equiv.Perm (Fin 16) :=
  pointChart.permCongrHom.toMonoidHom.comp BinaryPlanePermutationWreathCoordinates.pointAction

def generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,7,5,6,9,8,10,11,12,15,14,13,1,2,0,3] : Array (Fin 16))[x.val]!
  invFun x := (#[14,12,13,15,0,2,3,1,5,4,6,7,8,11,10,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,2,1,0,3,5,4,7,6,8,10,11,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,5,4,7,9,8,11,10,12,15,13,14,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 16) := ![generator0,generator1]
abbrev Original := Subgroup.closure (Set.range generators)

def pointLifts : Fin 2 → Point := ![⟨![localPerm (Equiv.swap 0 2 * Equiv.swap 0 1),localPerm (Equiv.swap 1 2 * Equiv.swap 1 3),localPerm (Equiv.swap 0 1),localPerm (Equiv.swap 1 3)],rotation⟩,
  ⟨![localPerm (Equiv.swap 0 2),localPerm (Equiv.swap 0 1 * Equiv.swap 2 3),localPerm (Equiv.swap 1 3 * Equiv.swap 1 2),localPerm (Equiv.swap 0 2 * Equiv.swap 1 3)],rotation⁻¹⟩]
def lifted : Fin 2 → Affine := fun j => coordinates (pointLifts j)

theorem bindings (j : Fin 2) : action (lifted j) = generators j := by
  apply Equiv.ext; intro x; revert j x; decide +kernel

def singerSeed : Lin := ((lifted 0).right * (lifted 1).right)^2
def exponents : Fin 4 → ℕ := ![1,1,2,1]
def singerWords (i : Fin 4) : Lin :=
  (lifted 0).right^i.val * singerSeed^(exponents i) * ((lifted 0).right^i.val)⁻¹

theorem singerWords_eq (i : Fin 4) : singerWords i = localEmbedding i singer := by
  apply PermutationalWreathProduct.ext
  · funext j
    apply LinearEquiv.ext
    intro v
    revert i j v
    decide +kernel
  · apply Subtype.ext
    apply Equiv.ext
    intro j
    revert i j
    decide +kernel

theorem blocks_cycle (j : Fin 4) : ∃ n : ℕ, rotation^n • (0 : Fin 4) = j :=
  ⟨j.val,(by decide +kernel : ∀ j : Fin 4, ((finRotate 4)^j.val) 0 = j) j⟩

theorem blocks_transitive (i j : Fin 4) : ∃ r : Blocks, r • i = j :=
  ⟨rotation^(j.val+4-i.val),
    (by decide +kernel : ∀ i j : Fin 4, ((finRotate 4)^(j.val+4-i.val)) i = j) i j⟩

theorem blocks_coprime : Nat.Coprime 3 (Nat.card Blocks) := by
  rw [Nat.card_zpowers]
  exact (by decide : Nat.Coprime 3 4).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (by decide +kernel : (finRotate 4)^4 = 1))

theorem quotientSocle (N : Subgroup Original) [N.Normal] :
    SocleNormalGeneratorBound (Original ⧸ N) 2 := by
  let K := Subgroup.closure (Set.range lifted)
  let C := actualImage K
  have hgen (j : Fin 2) : (lifted j).right ∈ C := ⟨closureGenerators lifted j,rfl⟩
  have hz : singerSeed ∈ C := C.pow_mem (C.mul_mem (hgen 0) (hgen 1)) 2
  have hlocal (i : Fin 4) : localEmbedding i singer ∈ C := by
    rw [← singerWords_eq i]
    exact C.mul_mem
      (C.mul_mem (C.pow_mem (hgen 0) i.val) (C.pow_mem hz (exponents i)))
      (C.inv_mem (C.pow_mem (hgen 0) i.val))
  let beta : C →* Blocks := PermutationalWreathProduct.rightHom.comp C.subtype
  have hbeta : Function.Surjective beta := by
    have hr : rotation ∈ beta.range := ⟨⟨(lifted 0).right,hgen 0⟩,rfl⟩
    intro r
    obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
    have he : rotation^z = r := Subtype.ext hz
    rw [← he]
    exact beta.range.zpow_mem hr z
  have hmove : ∀ i j : Fin 4, ∃ q : C, (q : Lin).right • i = j := by
    intro i j
    obtain ⟨r,hr⟩ := blocks_transitive i j
    obtain ⟨q,hq⟩ := hbeta r
    exact ⟨q,by change beta q • i = j; rw [hq,hr]⟩
  let f : K →* Equiv.Perm (Fin 16) := action.comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) generators
    (Equiv.refl _) (closureGenerators_full lifted) bindings
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) generators
      (Equiv.refl _) (closureGenerators_full lifted) bindings
  exact BinaryPlaneCyclicWreathQuotientSocles.socle_of_surjective K hlocal hmove hbeta
    rotation 0 blocks_cycle blocks_coprime ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi)

theorem affine_card_le : Nat.card Affine ≤ 2^22 := by
  have hL : Nat.card Linear ≤ 6 := by
    have h := Nat.card_le_card_of_injective BinaryPlaneWreathNormalGenerators.toThree
      BinaryPlaneWreathNormalGenerators.toThree_injective
    have he : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm,Nat.card_fin]
      decide
    simpa only [he] using h
  have hB : Nat.card Blocks ≤ 4 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide : 0 < 4)
      (orderOf_dvd_of_pow_eq_one (by decide +kernel : (finRotate 4)^4 = 1))
  have hLin : Nat.card Lin ≤ 6^4*4 := by
    have h := Nat.card_le_card_of_injective
      (fun g : Lin => (g.left,g.right)) (by
        intro g h he
        exact PermutationalWreathProduct.ext (congrArg Prod.fst he) (congrArg Prod.snd he))
    rw [Nat.card_prod,Nat.card_fun,Nat.card_fin] at h
    exact h.trans (Nat.mul_le_mul (Nat.pow_le_pow_left hL 4) hB)
  have hV : Nat.card V = 4 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    norm_num
  rw [SemidirectProduct.card,Nat.card_fun,Nat.card_fin,hV]
  have h := Nat.mul_le_mul_left (4^4) hLin
  norm_num at h ⊢
  exact h.trans (by decide)

theorem original_card_le : Nat.card Original ≤ 2^22 := by
  let K := Subgroup.closure (Set.range lifted)
  let f : K →* Equiv.Perm (Fin 16) := action.comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) generators
    (Equiv.refl _) (closureGenerators_full lifted) bindings
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) generators
      (Equiv.refl _) (closureGenerators_full lifted) bindings
  exact ((Nat.card_le_card_of_surjective pi hpi).trans
    (Subgroup.card_le_card_group K)).trans affine_card_le

noncomputable def registry : FiniteNormalStateRegistry Original := FiniteNormalStateRegistry.allNormals
noncomputable def family : registry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds registry
    (fun N => by letI := N.2; exact quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles

end
