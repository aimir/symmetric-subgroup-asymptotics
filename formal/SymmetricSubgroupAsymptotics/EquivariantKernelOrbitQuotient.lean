import SymmetricSubgroupAsymptotics.FiniteActionFibreBurnside

/-! Complete orbit labels survive quotienting actual kernel-filled fibres. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EquivariantKernelOrbitQuotient

/-- All original orbits, not only their number, correspond to the block orbits. -/
def orbitQuotientEquiv {G X I : Type*} [Group G]
    [MulAction G X] [MulAction G I]
    (b : X → I) (hsurj : Function.Surjective b)
    (hb : ∀ (g : G) (x : X), b (g • x) = g • b x)
    (K : Subgroup G)
    (hfill : ∀ x y : X, b x = b y → ∃ k : K, (k : G) • y = x) :
    MulAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient G I := by
  classical
  let f : X → MulAction.orbitRel.Quotient G I :=
    fun x => Quotient.mk _ (b x)
  have hf : Function.Surjective f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro i
    obtain ⟨x,hx⟩ := hsurj i
    exact ⟨x, congrArg (fun j : I => Quotient.mk (MulAction.orbitRel G I) j) hx⟩
  have hmap (g : G) (x : X) : f (g • x) = f x := by
    apply Quotient.sound
    exact ⟨g, (hb g x).symm⟩
  have hfibre (x y : X) (hxy : f x = f y) : ∃ g : G, g • y = x := by
    obtain ⟨g,hg⟩ := Quotient.exact hxy
    have he : b x = b (g • y) := hg.symm.trans (hb g y).symm
    obtain ⟨k,hk⟩ := hfill x (g • y) he
    exact ⟨(k : G)*g, by simpa only [mul_smul] using hk⟩
  exact FiniteActionFibreBurnside.orbitQuotientEquiv f hf hmap hfibre

end SymmetricSubgroupAsymptotics.EquivariantKernelOrbitQuotient
