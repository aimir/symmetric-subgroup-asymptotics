import SymmetricSubgroupAsymptotics.TernarySignedWreathLinearEquiv
import SymmetricSubgroupAsymptotics.ProperTransitiveMonomialScalarCode

/-! For an ACTUAL signed four-coordinate subgroup surjecting onto S4,
a nonzero proper invariant ternary submodule forces its original
permutation-kernel to have order at most two. The monomial signs need
not split over S4. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourProperModuleSignKernel
open TernarySignedWreathLinearEquiv OddMarkerTernaryChart

abbrev Signed := Model (Fin 4)

def topHom (R : Subgroup Signed) : R →* Equiv.Perm (Fin 4) :=
  (permutationHom (Fin 4)).comp R.subtype

private theorem conjugate_base (g n : Signed) (hn : n.right=1) (i : Fin 4) :
    (g*n*g⁻¹).left i=n.left (g.right⁻¹ i) := by
  simp [PermutationalWreathProduct.mul_left,
    PermutationalWreathProduct.inv_left,hn,mul_comm,mul_assoc]

theorem kernel_card_le_two
    (R : Subgroup Signed) (ht : Function.Surjective (topHom R))
    (W : Submodule (ZMod 3) (Fin 4 → ZMod 3)) (hne : W≠⊥) (hproper : W≠⊤)
    (hstable : ∀ (g : R) w,w∈W → linearHom (Fin 4) g.val w∈W) :
    Nat.card (topHom R).ker≤2 := by
  let J := (topHom R).ker
  let scalar : J → (Fin 4 → ZMod 3) :=
    fun n i => (coefficient (Fin 4) n.val.val i : ZMod 3)
  let C : Set (Fin 4 → ZMod 3) := Set.range scalar
  have hperm : ∀ (s : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod 3),
      c∈C → c ∘ s∈C := by
    intro s c hc
    obtain ⟨n,rfl⟩ := hc
    obtain ⟨g,hg⟩ := ht s⁻¹
    let m : J := ⟨g*n.val*g⁻¹,by
      change topHom R (g*n.val*g⁻¹)=1
      rw [map_mul,map_mul,map_inv,n.property,mul_one,mul_inv_cancel]⟩
    refine ⟨m,?_⟩
    funext i
    change (signUnitHom ((g.val*n.val.val*g.val⁻¹).left i) : ZMod 3)=
      (signUnitHom (n.val.val.left (s i)) : ZMod 3)
    have hn : n.val.val.right=1 := n.property
    have hg' : g.val.right=s⁻¹ := hg
    rw [conjugate_base g.val n.val.val hn,hg',inv_inv]
  have hdiag : ∀ (c : Fin 4 → ZMod 3),c∈C → ∀w,w∈W →
      (fun i => c i*w i)∈W := by
    intro c hc w hw
    obtain ⟨n,rfl⟩ := hc
    have hn : permutationHom (Fin 4) n.val.val=1 := n.property
    have he : linearHom (Fin 4) n.val.val w=(fun i => scalar n i*w i) := by
      funext i
      have hid : (1 : Equiv.Perm (Fin 4)).symm=1 := rfl
      simp only [linearHom_apply,hn,hid,Equiv.Perm.one_apply,scalar]
    rw [←he]
    exact hstable n.val w hw
  have htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j := by
    intro i j
    obtain ⟨g,hg⟩ := ht (Equiv.swap i j)
    exact ⟨g,(congrArg (fun s : Equiv.Perm (Fin 4) => s i) hg).trans
      (Equiv.swap_apply_left i j)⟩
  have hconstant : ∀n : J,∀i j,scalar n i=scalar n j := by
    have hc := ProperTransitiveMonomialScalarCode.scalar_code_constant_of_proper_transitive_monomial_submodule
        ((linearHom (Fin 4)).comp R.subtype) (topHom R)
        (fun g i => coefficient (Fin 4) g.val i)
        (fun g w i => linearHom_apply (Fin 4) g.val w i)
        htrans W hne hproper hstable C hperm hdiag
    intro n
    exact hc (scalar n) ⟨n,rfl⟩
  let f : J → Multiplicative (ZMod 2) := fun n => n.val.val.left 0
  have hf : Function.Injective f := by
    intro n m he
    have hbase (x : J) (i : Fin 4) : x.val.val.left i=x.val.val.left 0 := by
      apply signUnitHom_injective
      apply Units.ext
      exact hconstant x i 0
    apply Subtype.ext
    apply Subtype.ext
    apply PermutationalWreathProduct.ext
    · funext i
      exact (hbase n i).trans (he.trans (hbase m i).symm)
    · exact (show n.val.val.right=1 from n.property).trans
        (show m.val.val.right=1 from m.property).symm
  exact (Nat.card_le_card_of_injective f hf).trans_eq
    ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
      (Nat.card_zmod 2))

end SymmetricSubgroupAsymptotics.TernaryFourProperModuleSignKernel
