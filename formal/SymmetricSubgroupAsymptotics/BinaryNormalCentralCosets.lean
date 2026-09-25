import SymmetricSubgroupAsymptotics.BinaryNormalParentSteps

/-! Quotient-sized normal installation by compression of a checked parent
quotient. All new representatives are original parent representatives.
Each local edge differs by at most the selected actual central involution;
the original extension need not split. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι κ : Type*} [Group G] [Finite G]
    {generators : ι → G} {hgen : Subgroup.closure (Set.range generators)=⊤}
    {S : BinaryNormalState generators} {childGenerators : κ → G}

namespace BinaryNormalParentStep

variable (E : BinaryNormalParentStep hgen S childGenerators)

/-- An original element lies in the child precisely when its parent
quotient class lies in the selected cyclic subgroup. -/
theorem mem_child_iff (x : G) :
    x ∈ Subgroup.closure (Set.range childGenerators) ↔
      QuotientGroup.mk' S.kernel x ∈ Subgroup.zpowers (S.quotientEquiv hgen E.row) := by
  rw [E.kernel_eq]
  rfl

/-- A checked parent-row edge, equal or differing by the selected central
row, proves the required original coset equation in the child. -/
theorem compressed_step_mem (a b : S.Row) (j : ι)
    (he : letI := S.group hgen
      (⟨S.cosets.next a.index j⟩ : S.Row)=b ∨
        (⟨S.cosets.next a.index j⟩ : S.Row)=E.row*b) :
    S.cosets.representatives b.index /
      (S.cosets.representatives a.index * generators j) ∈
        Subgroup.closure (Set.range childGenerators) := by
  letI := S.group hgen
  rw [E.mem_child_iff,map_div,map_mul]
  have hr (i : S.Row) : S.quotientEquiv hgen i=
      QuotientGroup.mk' S.kernel (S.cosets.representatives i.index) :=
    S.cosets.rowQuotientEquiv_apply hgen S.cardinal S.prev S.prev_next i
  have hn : S.quotientEquiv hgen ⟨S.cosets.next a.index j⟩=
      QuotientGroup.mk' S.kernel (S.cosets.representatives a.index)*
        QuotientGroup.mk' S.kernel (generators j) := by
    rw [hr]
    exact S.cosets.quotientRow_next a.index j
  rw [← hn,← hr b]
  rcases he with he|he
  · rw [he,div_self']
    exact (Subgroup.zpowers _).one_mem
  · rw [he,map_mul,div_mul_eq_div_div_swap,div_self']
    simpa only [one_div] using (Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _)

/-- Install a child coset chart by checking only its parent quotient rows.
The quotient's recorded size is subsequently justified by the proved
parent-step cardinal identity. -/
def compressedCosets {q : ℕ} (lifts : Fin q → S.Row)
    (identity : Fin q) (hid : (lifts identity).index=S.cosets.identity)
    (next : Fin q → ι → Fin q)
    (step : ∀ i j, letI := S.group hgen
      (⟨S.cosets.next (lifts i).index j⟩ : S.Row)=lifts (next i j) ∨
        (⟨S.cosets.next (lifts i).index j⟩ : S.Row)=E.row*lifts (next i j))
    (rank : Fin q → ℕ)
    (parent : ∀ i, i≠identity → Fin q)
    (letter : ∀ i, i≠identity → ι)
    (parent_lt : ∀ i hi, rank (parent i hi)<rank i)
    (parent_next : ∀ i hi, next (parent i hi) (letter i hi)=i) :
    letI := E.normal
    BinaryNormalCosetCertificate generators
      (Subgroup.closure (Set.range childGenerators)) q := by
  letI := E.normal
  refine {
    representatives := fun i => S.cosets.representatives (lifts i).index
    identity := identity
    identity_mem := ?_
    next := next
    step_mem := fun i j => E.compressed_step_mem (lifts i) (lifts (next i j)) j (step i j)
    rank := rank
    parent := parent
    letter := letter
    parent_lt := parent_lt
    parent_next := parent_next }
  rw [hid,E.mem_child_iff]
  have h := S.cosets.quotientRow_identity
  change QuotientGroup.mk' S.kernel (S.cosets.representatives S.cosets.identity)=1 at h
  rw [h]
  exact (Subgroup.zpowers _).one_mem

end BinaryNormalParentStep
end SymmetricSubgroupAsymptotics
