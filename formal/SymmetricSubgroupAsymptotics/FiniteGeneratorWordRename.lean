import SymmetricSubgroupAsymptotics.FiniteGeneratorWord

set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FiniteGeneratorWord
variable {ι κ G : Type*} [Group G]

def rename (f : ι → κ) : FiniteGeneratorWord ι → FiniteGeneratorWord κ
  | .one => .one
  | .generator i => .generator (f i)
  | .mul u v => .mul (rename f u) (rename f v)
  | .inv u => .inv (rename f u)

theorem eval_rename (f : ι → κ) (w : FiniteGeneratorWord ι) (g : κ → G) :
    (rename f w).eval g = w.eval (fun i => g (f i)) := by
  induction w <;> simp_all [rename,eval]

end SymmetricSubgroupAsymptotics.FiniteGeneratorWord
