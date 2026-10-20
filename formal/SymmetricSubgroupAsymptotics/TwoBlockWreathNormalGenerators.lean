import SymmetricSubgroupAsymptotics.SubdirectPairNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratingTuplesExtension
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding

/-! On two blocks, the block kernel has the full local component in both
coordinates. This proves a genuine subdirect-pair bound on the actual
kernel; all transporter twists and diagonal correlations are retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TwoBlockWreathNormalGenerators

variable {G L Q I : Type} [Group G] [Group L] [Group Q]
    [MulAction Q I] [FaithfulSMul Q I] [Finite I]

private theorem eq_one_of_fixed (hI : Nat.card I = 2) (q : Q) (i : I)
    (hi : q • i = i) : q = 1 := by
  let e : I ≃ Fin 2 := Finite.equivFinOfCardEq hI
  have hsmall : ∀ (s : Equiv.Perm (Fin 2)) (j : Fin 2), s j = j → s = 1 := by decide
  have hperm : e.permCongr (MulAction.toPerm q) = 1 :=
    hsmall _ (e i) (by simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using congrArg e hi)
  have he : MulAction.toPerm q = 1 := e.permCongrHom.injective
    (hperm.trans (map_one e.permCongrHom).symm)
  apply eq_of_smul_eq_smul (M := Q) (α := I)
  intro j
  rw [one_smul]
  exact congrArg (fun s : Equiv.Perm I => s j) he

variable (rho : G →* PermutationalWreathProduct L Q I)

abbrev top : G →* Q := PermutationalWreathProduct.rightHom.comp rho

def coordinate (i : I) : (top rho).ker →* L where
  toFun x := (rho x.1).left i
  map_one' := by simp only [Subgroup.coe_one, map_one, PermutationalWreathProduct.one_left, Pi.one_apply]
  map_mul' x y := by
    have hx : (rho x.1).right = 1 := x.2
    change (rho (x.1 * y.1)).left i = (rho x.1).left i * (rho y.1).left i
    rw [map_mul]
    change (rho x.1).left i * (rho y.1).left ((rho x.1).right⁻¹ • i) = _
    rw [hx, inv_one, one_smul]

theorem coordinate_surjective (hI : Nat.card I = 2)
    (hfull : PermutationalWreathProduct.Compression.FullComponent rho) (i : I) :
    Function.Surjective (coordinate rho i) := by
  intro l
  obtain ⟨g, hg, he⟩ := hfull i l
  have hker : g ∈ (top rho).ker := eq_one_of_fixed hI (rho g).right i hg
  exact ⟨⟨g, hker⟩, he⟩

theorem coordinates_joint_injective (hrho : Function.Injective rho) :
    Function.Injective (fun x : (top rho).ker => fun i : I => coordinate rho i x) := by
  intro x y h
  apply Subtype.ext
  apply hrho
  apply PermutationalWreathProduct.ext
  · exact h
  · exact x.2.trans y.2.symm

theorem kernel_normal_generating_tuples {a : ℕ} (hI : Nat.card I = 2)
    (hrho : Function.Injective rho)
    (hfull : PermutationalWreathProduct.Compression.FullComponent rho)
    (hL : ∀ N : Subgroup L, N.Normal →
      ∃ x : Fin a → L, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (top rho).ker, N.Normal →
      ∃ x : Fin (a + a) → (top rho).ker, Subgroup.normalClosure (Set.range x) = N := by
  let e : I ≃ Fin 2 := Finite.equivFinOfCardEq hI
  apply normal_generating_tuples_subdirect_pair
    (coordinate rho (e.symm 0)) (coordinate rho (e.symm 1))
    (coordinate_surjective rho hI hfull _) (coordinate_surjective rho hI hfull _)
    _ hL hL
  intro x y h
  apply coordinates_joint_injective rho hrho
  funext i
  have hi : i = e.symm (e i) := (e.symm_apply_apply i).symm
  rw [hi]
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  generalize e i = j
  fin_cases j
  · exact h0
  · exact h1

theorem normal_generating_tuples [Finite Q] [IsCyclic Q] {a : ℕ}
    (hI : Nat.card I = 2) (hrho : Function.Injective rho)
    (htop : Function.Surjective (top rho))
    (hfull : PermutationalWreathProduct.Compression.FullComponent rho)
    (hL : ∀ N : Subgroup L, N.Normal →
      ∃ x : Fin a → L, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin (a + a + 1) → G, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_cyclic_extension (top rho) htop
    (kernel_normal_generating_tuples rho hI hrho hfull hL)

end SymmetricSubgroupAsymptotics.TwoBlockWreathNormalGenerators

end
