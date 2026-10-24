import SymmetricSubgroupAsymptotics.ThreePointFibreOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PermutationOrdinaryGeneratorSplit
import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions

/-! The full intransitive step for sharp ordinary permutation generation.
Only the literal sharp statement at strictly smaller degrees is used.
An actual invariant three-point set is handled by jointly faithful
restriction and generator sharing, including a full S3 on either side.
No product decomposition or orbit-by-orbit catalogue is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.IntransitiveOrdinaryGeneratorInduction
open PermutationCharacterRankSplit PermutationOrdinarySmallerActions

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

/-- The three-point fibre shares a generator even when its kernel image
is all of S3. Both restrictions are the original action restrictions. -/
theorem half_degree_of_three_point_subset (S : SubMulAction G X)
    (hS : (S:Set X).Nonempty) (hC : (Sᶜ:Set X).Nonempty) (hthree : Nat.card S=3)
    (hbelow : SmallerActionBound (Nat.card X)) :
    2*MarkedC4.genRank G≤Nat.card X := by
  let e : S≃Fin 3 := Finite.equivFinOfCardEq hthree
  let f : G→*Equiv.Perm (Fin 3) :=
    e.permCongrHom.toMonoidHom.comp (restrictionHom S)
  have hjoint : Function.Injective (fun g:G=>(f g,projection (Sᶜ) g)) := by
    intro g h he
    apply eq_of_smul_eq_smul (α:=X)
    intro x
    by_cases hx:x∈S
    · have hf : f g=f h := congrArg Prod.fst he
      have hr : restrictionHom S g=restrictionHom S h := e.permCongrHom.injective hf
      exact congrArg Subtype.val (Equiv.congr_fun hr ⟨x,hx⟩)
    · have hp : projection (Sᶜ) g=projection (Sᶜ) h := congrArg Prod.snd he
      have hr : restrictionHom (Sᶜ) g=restrictionHom (Sᶜ) h :=
        congrArg (fun q:Image (Sᶜ)=>(q:Equiv.Perm ↥(Sᶜ))) hp
      exact congrArg Subtype.val (Equiv.congr_fun hr ⟨x,hx⟩)
  have hG := ThreePointFibreOrdinaryGenerators.genRank_le_max
    (projection (Sᶜ)) (projection_surjective (Sᶜ)) f hjoint
  have hlt := degrees_lt S hS hC
  have hQ := rounded_rank_of_smaller (Nat.card X) hbelow (Image (Sᶜ)) ↥(Sᶜ) hlt.2
  have hsplit := card_split S
  rcases le_total 2 (MarkedC4.genRank (Image (Sᶜ))+1) with hle|hle
  · rw [max_eq_right hle] at hG
    omega
  · rw [max_eq_left hle] at hG
    omega

/-- Every nontrivial invariant split satisfies the sharp bound under
strictly smaller induction, without excluding three-point fibres. -/
theorem half_degree_of_split (S : SubMulAction G X)
    (hS : (S:Set X).Nonempty) (hC : (Sᶜ:Set X).Nonempty)
    (hbelow : SmallerActionBound (Nat.card X)) :
    2*MarkedC4.genRank G≤Nat.card X := by
  by_cases hthree:Nat.card S=3
  · exact half_degree_of_three_point_subset S hS hC hthree hbelow
  by_cases hcthree:Nat.card ↥(Sᶜ)=3
  · exact half_degree_of_three_point_subset (Sᶜ) hC
      (by
        obtain ⟨x,hx⟩ := hS
        refine ⟨x,?_⟩
        change ¬¬x∈S
        exact not_not.mpr hx) hcthree hbelow
  letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
  have hlt := degrees_lt S hS hC
  have hI := hbelow (Image S) S hlt.1 hthree
  have hK := hbelow (Kernel S) ↥(Sᶜ) hlt.2 hcthree
  have hG := PermutationOrdinaryGeneratorSplit.genRank_le_image_add_kernel S
  have hsplit := card_split S
  omega

/-- The entire intransitive action branch of the ordinary generator
induction. The transitive primitive and imprimitive branches are separate. -/
theorem half_degree_of_intransitive (hnot : ¬MulAction.IsPretransitive G X)
    (hbelow : SmallerActionBound (Nat.card X)) :
    2*MarkedC4.genRank G≤Nat.card X := by
  obtain ⟨S,hS,hC⟩ := exists_nonempty_proper_invariant hnot
  exact half_degree_of_split S hS hC hbelow

theorem exists_half_degree_generators (hnot : ¬MulAction.IsPretransitive G X)
    (hbelow : SmallerActionBound (Nat.card X)) :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤Nat.card X := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨S,hgen,by rw [hS]; exact half_degree_of_intransitive hnot hbelow⟩

/-- Literal original n-point subgroup interface. The induction premise
retains the full S3 exception and applies only at degrees k<n. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (hnot : ¬MulAction.IsPretransitive J (Fin n))
    (hbelow : ∀(k : ℕ),k<n→∀K:Subgroup (Equiv.Perm (Fin k)),
      (k=3→K≠⊤)→∃S:Finset K,Subgroup.closure (S:Set K)=⊤ ∧ 2*S.card≤k) :
    ∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤n := by
  have hb : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  simpa only [Nat.card_fin] using exists_half_degree_generators hnot hb

end SymmetricSubgroupAsymptotics.IntransitiveOrdinaryGeneratorInduction
