import SymmetricSubgroupAsymptotics.PrimitiveReferencePairWitness

/-! A cyclic stabilizer orbit and one actual mover suffice for two-point
transitivity. No group order, presentation, or ordered-pair table is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

 theorem two_pretransitive_of_cyclic_stabilizer_and_mover
    {G X : Type*} [Group G] [MulAction G X]
    (a b : G) (f c : X) (haf : a • f=f)
    (hcycle : ∀ x : X,x≠f → ∃ n : ℕ,a^n • c=x)
    (hmover : b • f≠f) : MulAction.IsMultiplyPretransitive G X 2 := by
  have hfix (n : ℕ) : a^n • f=f := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,mul_smul,haf,ih]
  obtain ⟨k,hk⟩ := hcycle (b • f) hmover
  have hinv : (a^k)⁻¹ • (b • f)=c := by rw [← hk]; simp
  have hpoint (x : X) : ∃ m : G,m • f=x := by
    by_cases hx : x=f
    · exact ⟨1,by simpa only [one_smul] using hx.symm⟩
    · obtain ⟨n,hn⟩ := hcycle x hx
      exact ⟨a^n*(a^k)⁻¹*b,by simpa only [mul_smul,hinv] using hn⟩
  apply two_pretransitive_of_reference_pair f c
  intro x y hxy
  obtain ⟨m,hm⟩ := hpoint x
  have hy : m⁻¹ • y≠f := by
    intro he
    have h : y=m • f := by
      have ht := congrArg (fun z : X => m • z) he
      simpa only [smul_inv_smul] using ht
    exact hxy (hm.symm.trans h.symm)
  obtain ⟨j,hj⟩ := hcycle (m⁻¹ • y) hy
  refine ⟨m*a^j,?_,?_⟩
  · simpa only [mul_smul,hfix] using hm
  · rw [mul_smul,hj,smul_inv_smul]

 theorem primitive_of_cyclic_stabilizer_and_mover
    {G X : Type*} [Group G] [MulAction G X]
    (a b : G) (f c : X) (haf : a • f=f)
    (hcycle : ∀ x : X,x≠f → ∃ n : ℕ,a^n • c=x)
    (hmover : b • f≠f) : MulAction.IsPreprimitive G X :=
  MulAction.isPreprimitive_of_is_two_pretransitive
    (two_pretransitive_of_cyclic_stabilizer_and_mover a b f c haf hcycle hmover)
end SymmetricSubgroupAsymptotics
