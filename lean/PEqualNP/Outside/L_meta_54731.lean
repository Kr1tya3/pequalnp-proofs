import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54731

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.not, [14]⟩], output := 15 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54731

theorem PEqualNP.Outside.L_meta_54731 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270585009 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54731.c1, PEqualNP.Outside.L_meta_54731.f1, by decide +kernel, by decide +kernel⟩
