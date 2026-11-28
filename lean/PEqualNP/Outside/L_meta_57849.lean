import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57849

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [12, 13]⟩], output := 14 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_57849

theorem PEqualNP.Outside.L_meta_57849 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147382 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_57849.c1, PEqualNP.Outside.L_meta_57849.f1, by decide +kernel, by decide +kernel⟩
