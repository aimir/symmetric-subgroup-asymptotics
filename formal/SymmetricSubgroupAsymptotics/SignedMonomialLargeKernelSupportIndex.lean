import SymmetricSubgroupAsymptotics.SignedMonomialFixedTopCode
import SymmetricSubgroupAsymptotics.TransitiveSetStabilizerIndexBounds

/-! If the actual permutation kernel is too large to be encoded by
the zero-coordinate signs, it moves the vector while preserving its
support. In a transitive coordinate action this gives two strict
stabilizer inclusions and a genuine factor four in the vector index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.SignedMonomialLargeKernelSupportIndex
open SignedMonomialFixedCoordinateCode SignedMonomialStabilizerClassBound

theorem exists_kernel_move_of_large
    {G I K : Type*} [Group G] [Field K] [Finite G] [Finite I] [Finite K]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))
    (hρ : Function.Injective ρ) (v : I → K)
    (hlarge : Nat.card Kˣ ^ Nat.card {i : I // v i=0}<Nat.card t.ker) :
    ∃g : t.ker,ρ g.val v≠v := by
  by_contra hmove
  have hfix (g : t.ker) : ρ g.val v=v := by
    by_contra hg
    exact hmove ⟨g,hg⟩
  letI : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) Units.val_injective
  let code : t.ker → ({i : I // v i=0} → Kˣ) := fun g i => a g.val i.val
  have hinj : Function.Injective code := by
    intro g h he
    apply Subtype.ext
    apply fixed_element_eq_of_zero_coefficients ρ t a hformula hρ v
      g.val h.val (hfix g) (hfix h)
    · exact (show t g.val=1 from g.property).trans (show t h.val=1 from h.property).symm
    · intro i hi
      exact congrFun he ⟨i,hi⟩
  have hcard := Nat.card_le_card_of_injective code hinj
  rw [Nat.card_fun] at hcard
  omega

theorem four_mul_fixed_card_le_of_large_kernel
    {G I K : Type*} [Group G] [Field K] [Finite G] [Finite I] [Finite K]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))
    (hρ : Function.Injective ρ)
    (htrans : ∀ i j : I,∃g : G,t g i=j)
    (v : I → K) (hS : {i : I | v i≠0}.Nonempty) (hC : {i : I | v i=0}.Nonempty)
    (hlarge : Nat.card Kˣ ^ Nat.card {i : I // v i=0}<Nat.card t.ker) :
    4*Nat.card (fixedSubgroup ρ v)≤Nat.card G := by
  letI : MulAction G I := MulAction.compHom I t
  let S : Set I := {i : I | v i≠0}
  let A := fixedSubgroup ρ v
  let B := MulAction.stabilizer G S
  have hB : B≠⊤ :=
    TransitiveSetStabilizerIndexBounds.set_stabilizer_ne_top htrans S hS
      (by
        obtain ⟨i,hi⟩ := hC
        refine ⟨i,?_⟩
        change ¬v i≠0
        exact fun hn => hn hi)
  have hle : A≤B := by
    intro g hg
    change t g • S=S
    apply Set.ext
    intro i
    simp only [Set.mem_smul_set_iff_inv_smul_mem,Set.mem_setOf_eq]
    change v ((t g).symm i)≠0 ↔ v i≠0
    have h := fixed_support_iff ρ t a hformula g v hg ((t g).symm i)
    simpa only [Equiv.apply_symm_apply] using h.symm
  obtain ⟨g,hg⟩ := exists_kernel_move_of_large ρ t a hformula hρ v hlarge
  have hstrict : A<B := lt_of_le_of_ne hle (by
    intro he
    apply hg
    have hb : g.val∈B := by
      change t g.val • S=S
      simp only [show t g.val=1 from g.property,one_smul]
    rw [←he] at hb
    exact hb)
  exact TransitiveSetStabilizerIndexBounds.four_mul_card_le_of_strict_chain A B hstrict hB

end SymmetricSubgroupAsymptotics.SignedMonomialLargeKernelSupportIndex
