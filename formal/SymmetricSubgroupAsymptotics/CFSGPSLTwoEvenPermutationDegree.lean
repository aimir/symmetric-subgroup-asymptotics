import SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! In characteristic two every nonzero field coefficient is an
actual square. Conjugation by the actual torus therefore makes all
nonidentity additive-root fixed counts equal. Burnside's checked
constant-fixed-count bound pays the full field order, rather than half
of it, in every faithful proper coset action of simple PSL2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenPermutationDegree
open MulAction CFSGConjugateSubgroupDegree

theorem field_card_le_of_root_movement {K G X : Type*}
    [Field K] [Finite K] [Group G] [Finite X] [MulAction G X]
    (hchar : ringChar K=2) (root : Multiplicative K →* G) (torus : Kˣ → G)
    (hact : ∀ t a, torus t*root (Multiplicative.ofAdd a)*(torus t)⁻¹=
      root (Multiplicative.ofAdd (a*(t:K)^2)))
    (hmove : ∃ x : X, root (Multiplicative.ofAdd 1) • x≠x) :
    Nat.card K≤Nat.card X := by
  letI : MulAction (Multiplicative K) X := MulAction.compHom X root
  rw [← show Nat.card (Multiplicative K)=Nat.card K from Nat.card_congr Multiplicative.toAdd]
  apply CFSGConjugateSubgroupDegree.card_le_of_constant_fixedBy
    (Nat.card (fixedBy X (root (Multiplicative.ofAdd 1))))
  · intro a ha
    have ha0 : a.toAdd≠0 := by
      intro he
      exact ha (congrArg Multiplicative.ofAdd he)
    obtain ⟨t,ht⟩ := FiniteField.isSquare_of_char_two hchar a.toAdd
    have ht0 : t≠0 := by
      intro hz
      exact ha0 (by rw [ht,hz,zero_mul])
    let u : Kˣ := Units.mk0 t ht0
    have hs : (u:K)^2=a.toAdd := by simpa only [u,Units.val_mk0,pow_two] using ht.symm
    have he := Nat.card_congr (fixedByConjugateEquiv (X:=X)
      (root (Multiplicative.ofAdd 1)) (torus u))
    rw [hact,one_mul,hs] at he
    simpa only [MulAction.fixedBy,MulAction.compHom_smul_def] using he.symm
  · obtain ⟨x,hx⟩ := hmove
    exact ⟨Multiplicative.ofAdd 1,x,hx⟩

open CFSGPSLTwoRootCoordinates PrimitiveSocleRawStructure
variable {F : Type} [Field F] [Finite F] [IsSimpleGroup (PSL (F:=F))]

theorem field_card_le_proper_index (hchar : ringChar F=2)
    (H : Subgroup (PSL (F:=F))) (hH : H≠⊤) : Nat.card F≤H.index := by
  change Nat.card F≤Nat.card (PSL (F:=F) ⧸ H)
  apply field_card_le_of_root_movement hchar (projectiveUpperHom (F:=F))
    (projectiveTorus (F:=F))
  · intro t a
    simpa only [projectiveUpperHom_apply,mul_comm] using projective_torus_conjugation t a
  · apply CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
    intro he
    exact one_ne_zero (projectiveUpper_injective (F:=F) (he.trans projectiveUpper_zero.symm))

theorem field_card_le_leastProperIndex (hchar : ringChar F=2) (ell : ℕ)
    (hell : LeastProperIndex (PSL (F:=F)) ell) : Nat.card F≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [← he]
  exact field_card_le_proper_index hchar H hH

end SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenPermutationDegree
