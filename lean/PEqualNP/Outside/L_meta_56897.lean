import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56897

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [13, 14]⟩], output := 15 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_56897

theorem PEqualNP.Outside.L_meta_56897 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165167 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_56897.c1, PEqualNP.Outside.L_meta_56897.f1, by decide +kernel, by decide +kernel⟩
