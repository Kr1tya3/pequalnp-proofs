import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_58066

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [13, 14]⟩], output := 15 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_58066

theorem PEqualNP.Outside.L_meta_58066 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295077 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_58066.c1, PEqualNP.Outside.L_meta_58066.f1, by decide +kernel, by decide +kernel⟩
