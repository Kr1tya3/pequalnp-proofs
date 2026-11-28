import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1493

open PEqualNP.CircuitLowerBounds

section Fold

variable {α : Type}

def sfold (F : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun W g => W ++ [F W g]) init

theorem sfold_length (F : List α → Gate → α) (init : List α) (gs : List Gate) :
    (sfold F init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [sfold]
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

theorem sfold_old (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : j < init.length) : (sfold F init gs).getD j d = init.getD j d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih (init ++ [F init g]) (by simp; omega)]
    exact List.getD_append _ _ _ _ hj

theorem sfold_append (F : List α → Gate → α) (init : List α) (gs1 gs2 : List Gate) :
    sfold F init (gs1 ++ gs2) = sfold F (sfold F init gs1) gs2 := by
  simp [sfold, List.foldl_append]

theorem sfold_snoc (F : List α → Gate → α) (init : List α) (gs : List Gate) (g : Gate) :
    sfold F init (gs ++ [g]) = sfold F init gs ++ [F (sfold F init gs) g] := by
  rw [sfold_append]; rfl

theorem sfold_at (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) (m : ℕ)
    (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init (gs.take m)) gs[m] := by
  have hsplit : gs.take m ++ (gs[m] :: gs.drop (m+1)) = gs := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hlen := sfold_length F init (gs.take m)
  rw [List.length_take, min_eq_left hm.le] at hlen
  conv_lhs => rw [← hsplit]
  rw [sfold_append]
  show (sfold F (sfold F init (gs.take m) ++ [F (sfold F init (gs.take m)) gs[m]])
    (gs.drop (m+1))).getD (init.length + m) d = _
  rw [sfold_old _ _ _ _ (by simp [hlen])]
  rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
  simp [hlen]

theorem sfold_gate (F : List α → Gate → α) (d : α)
    (hloc : ∀ W1 W2 g, (∀ j ∈ g.inputs, W1.getD j d = W2.getD j d) → F W1 g = F W2 g)
    (init : List α) (gs : List Gate)
    (hreads : ∀ m (hm : m < gs.length), ∀ j ∈ gs[m].inputs, j < init.length + m)
    (m : ℕ) (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init gs) gs[m] := by
  rw [sfold_at F init gs d m hm]
  apply hloc
  intro j hj
  have hjl := hreads m hm j hj
  have hfull : sfold F init gs = sfold F (sfold F init (gs.take m)) (gs.drop m) := by
    rw [← sfold_append, List.take_append_drop]
  rw [hfull]
  exact (sfold_old F (sfold F init (gs.take m)) (gs.drop m) d
    (by rw [sfold_length, List.length_take, min_eq_left hm.le]; exact hjl)).symm

theorem sfold_beyond (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : init.length + gs.length ≤ j) : (sfold F init gs).getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sfold_length]; exact hj)]
  rfl

end Fold

section Build

variable (k : ℕ)

noncomputable def inp (I : Finset (Fin k)) : List Bool :=
  List.ofFn (fun j : Fin k => @decide (j ∈ I) (Classical.propDecidable _)) ++ [false,true]

def evF (W : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => W.getD i false)

def dpF (W : List ℕ) (g : Gate) : ℕ := 1 + g.inputs.foldl (fun m j => max m (W.getD j 0)) 0

noncomputable def val (gs : List Gate) (I : Finset (Fin k)) (i : ℕ) : Bool := (sfold evF (inp k I) gs).getD i false

def dep (gs : List Gate) (i : ℕ) : ℕ := (sfold dpF (List.replicate (k+2) 0) gs).getD i 0

def Good (gs : List Gate) : Prop :=
  ∀ m (hm : m < gs.length), (gs[m].op = GateOp.and ∨ gs[m].op = GateOp.or) ∧
    gs[m].inputs.length ≤ 2 ∧ ∀ i ∈ gs[m].inputs, i < k+2+m

def Ok (gs : List Gate) (i : ℕ) (f : Finset (Fin k) → Prop) (d : ℕ) : Prop :=
  i < k+2+gs.length ∧ (∀ I, val k gs I i = true ↔ f I) ∧ dep k gs i ≤ d

variable {k}

theorem inp_length (I : Finset (Fin k)) : (inp k I).length = k+2 := by simp [inp]

theorem Ok.mono {gs gs' : List Gate} {i : ℕ} {f : Finset (Fin k) → Prop} {d : ℕ}
    (h : Ok k gs i f d) (hp : gs <+: gs') : Ok k gs' i f d := by
  obtain ⟨hs, rfl⟩ := hp
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp; omega, fun I => ?_, ?_⟩
  · rw [← h2 I]; unfold val
    rw [sfold_append, sfold_old _ _ _ _ (by rw [sfold_length, inp_length]; exact h1)]
  · unfold dep
    rw [sfold_append, sfold_old _ _ _ _ (by rw [sfold_length, List.length_replicate]; exact h1)]
    exact h3

theorem Ok.weaken {gs : List Gate} {i : ℕ} {f f' : Finset (Fin k) → Prop} {d d' : ℕ}
    (h : Ok k gs i f d) (hd : d ≤ d') (hf : ∀ I, f I ↔ f' I) : Ok k gs i f' d' :=
  ⟨h.1, fun I => (h.2.1 I).trans (hf I), h.2.2.trans hd⟩

theorem val_input (gs : List Gate) (I : Finset (Fin k)) {i : ℕ} (hi : i < k+2) :
    val k gs I i = (inp k I).getD i false := by
  unfold val; rw [sfold_old _ _ _ _ (by rw [inp_length]; exact hi)]

theorem dep_input (gs : List Gate) {i : ℕ} (hi : i < k+2) : dep k gs i = 0 := by
  unfold dep; rw [sfold_old _ _ _ _ (by rw [List.length_replicate]; exact hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem ok_false (gs : List Gate) : Ok k gs k (fun _ => False) 0 := by
  refine ⟨by omega, fun I => ?_, by rw [dep_input gs (by omega)]⟩
  rw [val_input gs I (by omega)]
  simp [inp, List.getD_eq_getElem?_getD]

theorem ok_true (gs : List Gate) : Ok k gs (k+1) (fun _ => True) 0 := by
  refine ⟨by omega, fun I => ?_, by rw [dep_input gs (by omega)]⟩
  rw [val_input gs I (by omega)]
  simp [inp, List.getD_eq_getElem?_getD]

theorem ok_var (gs : List Gate) (i : Fin k) : Ok k gs i.val (fun I => i ∈ I) 0 := by
  refine ⟨by omega, fun I => ?_, by rw [dep_input gs (by omega)]⟩
  rw [val_input gs I (by omega)]
  simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_left]

theorem good_snoc {gs : List Gate} {g : Gate} (hg : Good k gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2)
    (hi : ∀ i ∈ g.inputs, i < k+2+gs.length) : Good k (gs ++ [g]) := by
  intro m hm
  simp only [List.length_append, List.length_singleton] at hm
  rcases Nat.lt_or_ge m gs.length with h | h
  · rw [List.getElem_append_left h]; exact hg m h
  · have : m = gs.length := by omega
    subst this
    rw [List.getElem_append_right (by omega)]
    simpa using ⟨hop, hl, hi⟩

theorem gate2 {gs : List Gate} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) {a b : ℕ}
    {fa fb : Finset (Fin k) → Prop} {d : ℕ} (hg : Good k gs) (ha : Ok k gs a fa d) (hb : Ok k gs b fb d) :
    Good k (gs ++ [⟨op,[a,b]⟩]) ∧
    (∀ I, val k (gs ++ [⟨op,[a,b]⟩]) I (k+2+gs.length) = op.eval [val k gs I a, val k gs I b]) ∧
    dep k (gs ++ [⟨op,[a,b]⟩]) (k+2+gs.length) ≤ d+1 := by
  refine ⟨good_snoc hg hop (by simp) ?_, fun I => ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha.1
    · exact hb.1
  · unfold val
    rw [sfold_snoc, List.getD_append_right _ _ _ _ (by rw [sfold_length, inp_length])]
    rw [sfold_length, inp_length]
    simp [evF]
  · unfold dep
    rw [sfold_snoc, List.getD_append_right _ _ _ _ (by rw [sfold_length, List.length_replicate])]
    rw [sfold_length, List.length_replicate]
    simp only [Nat.sub_self, List.getD_cons_zero, dpF, List.foldl_cons, List.foldl_nil]
    have h1 := ha.2.2
    have h2 := hb.2.2
    unfold dep at h1 h2
    omega

theorem andGate {gs : List Gate} {a b : ℕ} {fa fb : Finset (Fin k) → Prop} {d : ℕ}
    (hg : Good k gs) (ha : Ok k gs a fa d) (hb : Ok k gs b fb d) :
    ∃ gs' c, gs <+: gs' ∧ gs'.length ≤ gs.length + 1 ∧ Good k gs' ∧
      Ok k gs' c (fun I => fa I ∧ fb I) (d+1) := by
  obtain ⟨h1, h2, h3⟩ := gate2 GateOp.and (Or.inl rfl) hg ha hb
  refine ⟨_, _, List.prefix_append _ _, by simp, h1, by simp, fun I => ?_, h3⟩
  show val k _ I _ = true ↔ fa I ∧ fb I
  rw [h2 I, ← ha.2.1 I, ← hb.2.1 I]
  simp [GateOp.eval]

theorem orGate {gs : List Gate} {a b : ℕ} {fa fb : Finset (Fin k) → Prop} {d : ℕ}
    (hg : Good k gs) (ha : Ok k gs a fa d) (hb : Ok k gs b fb d) :
    ∃ gs' c, gs <+: gs' ∧ gs'.length ≤ gs.length + 1 ∧ Good k gs' ∧
      Ok k gs' c (fun I => fa I ∨ fb I) (d+1) := by
  obtain ⟨h1, h2, h3⟩ := gate2 GateOp.or (Or.inr rfl) hg ha hb
  refine ⟨_, _, List.prefix_append _ _, by simp, h1, by simp, fun I => ?_, h3⟩
  show val k _ I _ = true ↔ fa I ∨ fb I
  rw [h2 I, ← ha.2.1 I, ← hb.2.1 I]
  simp [GateOp.eval]

theorem forEach {ι β : Type} [Inhabited β] (c : ℕ) (R : List Gate → ι → β → Prop)
    (Rmono : ∀ gs gs' x o, gs <+: gs' → R gs x o → R gs' x o) (L : List ι) :
    ∀ (gs : List Gate), Good k gs →
    (∀ x ∈ L, ∀ gs', gs <+: gs' → Good k gs' → ∃ gs'' o, gs' <+: gs'' ∧
        gs''.length ≤ gs'.length + c ∧ Good k gs'' ∧ R gs'' x o) →
    ∃ (gs' : List Gate) (out : ι → β), gs <+: gs' ∧ gs'.length ≤ gs.length + L.length * c ∧ Good k gs' ∧
      ∀ x ∈ L, R gs' x (out x) := by
  classical
  induction L with
  | nil => intro gs hg _; exact ⟨gs, fun _ => default, List.prefix_refl _, by simp, hg, by simp⟩
  | cons x L ih =>
    intro gs hg step
    obtain ⟨gs1, o1, p1, l1, g1, r1⟩ := step x List.mem_cons_self gs (List.prefix_refl _) hg
    obtain ⟨gs2, out2, p2, l2, g2, r2⟩ := ih gs1 g1 (fun y hy gs' hp hg' =>
      step y (List.mem_cons_of_mem _ hy) gs' (p1.trans hp) hg')
    refine ⟨gs2, fun y => if y ∈ L then out2 y else o1, p1.trans p2, ?_, g2, ?_⟩
    · simp only [List.length_cons, Nat.succ_mul]; omega
    · intro y hy
      by_cases h : y ∈ L
      · simp only [h, ↓reduceIte]; exact r2 y h
      · simp only [h, ↓reduceIte]
        rcases List.mem_cons.1 hy with rfl | h'
        · exact Rmono _ _ _ _ p2 r1
        · exact absurd h' h

theorem andLayer {ι : Type} (L : List ι) (a b : ι → ℕ) (fa fb : ι → Finset (Fin k) → Prop) (d : ℕ)
    (gs : List Gate) (hg : Good k gs) (ha : ∀ x ∈ L, Ok k gs (a x) (fa x) d)
    (hb : ∀ x ∈ L, Ok k gs (b x) (fb x) d) :
    ∃ (gs' : List Gate) (c : ι → ℕ), gs <+: gs' ∧ gs'.length ≤ gs.length + L.length ∧ Good k gs' ∧
      ∀ x ∈ L, Ok k gs' (c x) (fun I => fa x I ∧ fb x I) (d+1) := by
  obtain ⟨gs', c, p, l, g, r⟩ := forEach (k := k) 1 (fun gs x o => Ok k gs o (fun I => fa x I ∧ fb x I) (d+1))
    (fun _ _ _ _ hp h => h.mono hp) L gs hg (fun x hx gs' hp hg' =>
      andGate hg' ((ha x hx).mono hp) ((hb x hx).mono hp))
  exact ⟨gs', c, p, by simpa using l, g, r⟩

theorem orLayer {ι : Type} (L : List ι) (a b : ι → ℕ) (fa fb : ι → Finset (Fin k) → Prop) (d : ℕ)
    (gs : List Gate) (hg : Good k gs) (ha : ∀ x ∈ L, Ok k gs (a x) (fa x) d)
    (hb : ∀ x ∈ L, Ok k gs (b x) (fb x) d) :
    ∃ (gs' : List Gate) (c : ι → ℕ), gs <+: gs' ∧ gs'.length ≤ gs.length + L.length ∧ Good k gs' ∧
      ∀ x ∈ L, Ok k gs' (c x) (fun I => fa x I ∨ fb x I) (d+1) := by
  obtain ⟨gs', c, p, l, g, r⟩ := forEach (k := k) 1 (fun gs x o => Ok k gs o (fun I => fa x I ∨ fb x I) (d+1))
    (fun _ _ _ _ hp h => h.mono hp) L gs hg (fun x hx gs' hp hg' =>
      orGate hg' ((ha x hx).mono hp) ((hb x hx).mono hp))
  exact ⟨gs', c, p, by simpa using l, g, r⟩

end Build

section Merge

variable {k : ℕ}

theorem merge (v : ℕ) : ∀ (gs : List Gate) (A B : ℕ → ℕ) (ca cb : Finset (Fin k) → ℕ) (d : ℕ),
    Good k gs → (∀ I, ca I ≤ 2^v) → (∀ I, cb I ≤ 2^v) →
    (∀ i < 2^v, Ok k gs (A i) (fun I => ca I ≤ i) d) →
    (∀ i < 2^v, Ok k gs (B i) (fun I => cb I ≤ i) d) →
    ∃ (gs' : List Gate) (C : ℕ → ℕ), gs <+: gs' ∧ gs'.length ≤ gs.length + (2*v+2)*2^v ∧ Good k gs' ∧
      ∀ i < 2^(v+1), Ok k gs' (C i) (fun I => ca I + cb I ≤ i) (d+v+1) := by
  induction v with
  | zero =>
    intro gs A B ca cb d hg hca hcb hA hB
    simp only [pow_zero] at hca hcb hA hB ⊢
    have hA0 := hA 0 (by omega)
    have hB0 := hB 0 (by omega)
    obtain ⟨gs1, c1, p1, l1, g1, o1⟩ := andGate hg hA0 hB0
    obtain ⟨gs2, c2, p2, l2, g2, o2⟩ := orGate g1 (hA0.mono p1) (hB0.mono p1)
    refine ⟨gs2, fun i => if i = 0 then c1 else c2, p1.trans p2, by omega, g2, ?_⟩
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simp only [↓reduceIte]
      exact (o1.mono p2).weaken (by omega) (fun I => by have := hca I; have := hcb I; omega)
    · simp only [one_ne_zero, ↓reduceIte]
      exact o2.weaken (by omega) (fun I => by have := hca I; have := hcb I; omega)
  | succ v ih =>
    intro gs A B ca cb d hg hca hcb hA hB
    have e1 : 2^(v+1) = 2*2^v := by ring
    have e2 : 2^(v+1+1) = 4*2^v := by ring
    rw [e1] at hca hcb hA hB
    rw [e1, e2]
    obtain ⟨gs1, E, p1, l1, g1, hE⟩ := ih gs (fun i => A (2*i)) (fun i => B (2*i))
      (fun I => (ca I + 1)/2) (fun I => (cb I+1)/2) d hg
      (fun I => by have := hca I; omega) (fun I => by have := hcb I; omega)
      (fun i hi => (hA (2*i) (by omega)).weaken le_rfl (fun I => by omega))
      (fun i hi => (hB (2*i) (by omega)).weaken le_rfl (fun I => by omega))
    obtain ⟨gs2, O, p2, l2, g2, hO⟩ := ih gs1 (fun i => A (2*i+1)) (fun i => B (2*i+1))
      (fun I => ca I/2) (fun I => cb I/2) d g1
      (fun I => by have := hca I; omega) (fun I => by have := hcb I; omega)
      (fun i hi => ((hA (2*i+1) (by omega)).mono p1).weaken le_rfl (fun I => by omega))
      (fun i hi => ((hB (2*i+1) (by omega)).mono p1).weaken le_rfl (fun I => by omega))
    rw [e1] at hE hO
    have memL : ∀ x, x ∈ List.range (2*2^v - 1) ↔ x < 2*2^v - 1 := fun x => List.mem_range
    obtain ⟨gs3, Cor, p3, l3, g3, hor⟩ := orLayer (List.range (2*2^v - 1)) (fun x => E (x+1)) O
      (fun x I => (ca I + 1)/2 + (cb I + 1)/2 ≤ x+1) (fun x I => ca I/2 + cb I/2 ≤ x) (d+v+1) gs2 g2
      (fun x hx => (hE (x+1) (by rw [memL] at hx; omega)).mono p2)
      (fun x hx => hO x (by rw [memL] at hx; omega))
    obtain ⟨gs4, Cand, p4, l4, g4, hand⟩ := andLayer (List.range (2*2^v - 1)) (fun x => E (x+1)) O
      (fun x I => (ca I + 1)/2 + (cb I + 1)/2 ≤ x+1) (fun x I => ca I/2 + cb I/2 ≤ x) (d+v+1) gs3 g3
      (fun x hx => ((hE (x+1) (by rw [memL] at hx; omega)).mono p2).mono p3)
      (fun x hx => (hO x (by rw [memL] at hx; omega)).mono p3)
    refine ⟨gs4, fun i => if i = 0 then E 0 else if i = 4*2^v - 1 then O (2*2^v - 1) else
      if i % 2 = 0 then Cor (i/2 - 1) else Cand ((i-1)/2), p1.trans (p2.trans (p3.trans p4)), ?_, g4, ?_⟩
    · rw [List.length_range] at l3 l4
      have key : (2*(v+1)+2)*(2*2^v) = 2*((2*v+2)*2^v) + 4*2^v := by ring
      rw [key]
      generalize (2*v+2)*2^v = S at *
      omega
    · intro i hi
      by_cases h0 : i = 0
      · subst h0
        simp only [↓reduceIte]
        exact (((hE 0 (by omega)).mono p2).mono (p3.trans p4)).weaken (by omega)
          (fun I => by omega)
      by_cases h1 : i = 4*2^v - 1
      · subst h1
        simp only [h0, ↓reduceIte]
        exact ((hO (2*2^v-1) (by omega)).mono (p3.trans p4)).weaken (by omega)
          (fun I => by have := hca I; have := hcb I; omega)
      by_cases h2 : i % 2 = 0
      · simp only [h0, h1, h2, ↓reduceIte]
        exact ((hor (i/2-1) (by rw [memL]; omega)).mono p4).weaken (by omega)
          (fun I => by
            have : i/2 - 1 + 1 = i/2 := by omega
            simp only [this]; omega)
      · simp only [h0, h1, h2, ↓reduceIte]
        exact (hand ((i-1)/2) (by rw [memL]; omega)).weaken (by omega) (fun I => by omega)

theorem unary (P : ℕ → Prop) (hmono : ∀ b, P b → P (b+1)) (N : ℕ) :
    ∃ c ≤ N, ∀ b < N, (P b ↔ c ≤ b) := by
  have iter : ∀ c m, P c → P (c+m) := by
    intro c m hc
    induction m with
    | zero => exact hc
    | succ m ih => exact hmono _ ih
  induction N with
  | zero => exact ⟨0, le_rfl, fun b hb => absurd hb (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨c, hc, h⟩ := ih
    by_cases hcN : c < N
    · refine ⟨c, by omega, fun b hb => ?_⟩
      rcases Nat.lt_or_ge b N with hb' | hb'
      · exact h b hb'
      · have hb2 : b = N := by omega
        subst hb2
        have hPc : P c := (h c hcN).2 le_rfl
        have := iter c (b - c) hPc
        rw [Nat.add_sub_cancel' (by omega)] at this
        exact ⟨fun _ => by omega, fun _ => this⟩
    · have hcN' : c = N := by omega
      subst hcN'
      by_cases hP : P c
      · refine ⟨c, by omega, fun b hb => ?_⟩
        rcases Nat.lt_or_ge b c with hb' | hb'
        · exact h b hb'
        · have hb2 : b = c := by omega
          subst hb2
          exact ⟨fun _ => le_rfl, fun _ => hP⟩
      · refine ⟨c+1, le_rfl, fun b hb => ?_⟩
        rcases Nat.lt_or_ge b c with hb' | hb'
        · rw [h b hb']; omega
        · have hb2 : b = c := by omega
          subst hb2
          exact ⟨fun h' => absurd h' hP, fun h' => by omega⟩

theorem addRows (v : ℕ) (gs : List Gate) (A B : ℕ → ℕ) (Pa Pb : Finset (Fin k) → ℕ → Prop) (d : ℕ)
    (hg : Good k gs) (ma : ∀ I b, Pa I b → Pa I (b+1)) (mb : ∀ I b, Pb I b → Pb I (b+1))
    (hA : ∀ b < 2^v, Ok k gs (A b) (fun I => Pa I b) d) (hB : ∀ b < 2^v, Ok k gs (B b) (fun I => Pb I b) d) :
    ∃ (gs' : List Gate) (C : ℕ → ℕ), gs <+: gs' ∧ gs'.length ≤ gs.length + (2*v+2)*2^v ∧ Good k gs' ∧
      ∀ b < 2^v, Ok k gs' (C b) (fun I => ∃ b1 b2, b1 + b2 ≤ b ∧ Pa I b1 ∧ Pb I b2) (d+v+1) := by
  choose ca hca hA' using fun I => unary (Pa I) (ma I) (2^v)
  choose cb hcb hB' using fun I => unary (Pb I) (mb I) (2^v)
  obtain ⟨gs', C, p, l, g, hC⟩ := merge v gs A B ca cb d hg hca hcb
    (fun i hi => (hA i hi).weaken le_rfl (fun I => hA' I i hi))
    (fun i hi => (hB i hi).weaken le_rfl (fun I => hB' I i hi))
  refine ⟨gs', C, p, l, g, fun b hb => (hC b (by rw [pow_succ]; omega)).weaken le_rfl (fun I => ?_)⟩
  constructor
  · intro h
    exact ⟨ca I, cb I, h, (hA' I _ (by omega)).2 le_rfl, (hB' I _ (by omega)).2 le_rfl⟩
  · rintro ⟨b1, b2, h, h1, h2⟩
    have := (hA' I b1 (by omega)).1 h1
    have := (hB' I b2 (by omega)).1 h2
    omega

end Merge

section Table

variable {k : ℕ} [dk : DecidableEq (Fin k)]

def SP (price : Fin k → ℕ) (g : Finset (Fin k) → Prop) (S α : Finset (Fin k)) (b : ℕ)
    (I : Finset (Fin k)) : Prop :=
  ∃ X : Finset (Fin k), X ∩ S = α ∧ X \ S ⊆ I ∧ (X \ S).sum price ≤ b ∧ g X

theorem SP_succ {price : Fin k → ℕ} {g : Finset (Fin k) → Prop} {S α : Finset (Fin k)} {b : ℕ}
    {I : Finset (Fin k)} (h : SP price g S α b I) : SP price g S α (b+1) I := by
  obtain ⟨X, h1, h2, h3, h4⟩ := h
  exact ⟨X, h1, h2, by omega, h4⟩

theorem inter_erase_eq (X S : Finset (Fin k)) (i : Fin k) : X ∩ S.erase i = (X ∩ S).erase i := by
  ext y; simp only [Finset.mem_inter, Finset.mem_erase]; tauto

theorem sdiff_erase_in {X S : Finset (Fin k)} {i : Fin k} (hiS : i ∈ S) (hiX : i ∈ X) :
    X \ S.erase i = insert i (X \ S) := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
  by_cases h : y = i
  · subst h; tauto
  · tauto

theorem sdiff_erase_out {X S : Finset (Fin k)} {i : Fin k} (hiX : i ∉ X) :
    X \ S.erase i = X \ S := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  by_cases h : y = i
  · subst h; tauto
  · tauto

theorem sum_ins (price : Fin k → ℕ) {s : Finset (Fin k)} {i : Fin k} (hn : i ∉ s) :
    (insert i s).sum price = price i + s.sum price := Finset.sum_insert hn

theorem SP_forget (price : Fin k → ℕ) (g : Finset (Fin k) → Prop) {S α : Finset (Fin k)} {i : Fin k}
    (hi : i ∈ S) (hα : α ⊆ S.erase i) (b : ℕ) (I : Finset (Fin k)) :
    SP price g (S.erase i) α b I ↔ SP price g S α b I ∨
      (i ∈ I ∧ price i ≤ b ∧ SP price g S (insert i α) (b - price i) I) := by
  have hiα : i ∉ α := fun h => by have := hα h; simp at this
  constructor
  · rintro ⟨X, h1, h2, h3, h4⟩
    rw [inter_erase_eq] at h1
    by_cases hiX : i ∈ X
    · right
      rw [sdiff_erase_in hi hiX] at h2 h3
      have hn : i ∉ X \ S := by simp [hi]
      rw [sum_ins price hn] at h3
      refine ⟨h2 (Finset.mem_insert_self _ _), by omega, X, ?_, fun y hy => h2 (Finset.mem_insert_of_mem hy),
        by omega, h4⟩
      rw [← h1, Finset.insert_erase (Finset.mem_inter.2 ⟨hiX, hi⟩)]
    · left
      rw [sdiff_erase_out hiX] at h2 h3
      refine ⟨X, ?_, h2, h3, h4⟩
      rw [← h1, Finset.erase_eq_of_notMem (fun h => hiX (Finset.mem_inter.1 h).1)]
  · rintro (⟨X, h1, h2, h3, h4⟩ | ⟨hiI, hp, X, h1, h2, h3, h4⟩)
    · have hiX : i ∉ X := fun h => hiα (h1 ▸ Finset.mem_inter.2 ⟨h, hi⟩)
      refine ⟨X, ?_, by rw [sdiff_erase_out hiX]; exact h2, by rw [sdiff_erase_out hiX]; exact h3, h4⟩
      rw [inter_erase_eq, h1, Finset.erase_eq_of_notMem hiα]
    · have hiX : i ∈ X := (Finset.mem_inter.1 (h1 ▸ Finset.mem_insert_self i α : i ∈ X ∩ S)).1
      have hn : i ∉ X \ S := by simp [hi]
      refine ⟨X, ?_, ?_, ?_, h4⟩
      · rw [inter_erase_eq, h1, Finset.erase_insert hiα]
      · rw [sdiff_erase_in hi hiX]
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hiI
        · exact h2 hy
      · rw [sdiff_erase_in hi hiX, sum_ins price hn]; omega

def TabOk (gs : List Gate) (T : Finset (Fin k) → ℕ → ℕ) (price : Fin k → ℕ) (g : Finset (Fin k) → Prop)
    (S : Finset (Fin k)) (N d : ℕ) : Prop :=
  ∀ α ⊆ S, ∀ b < N, Ok k gs (T α b) (SP price g S α b) d

theorem TabOk.mono {gs gs' : List Gate} {T : Finset (Fin k) → ℕ → ℕ} {price : Fin k → ℕ}
    {g : Finset (Fin k) → Prop} {S : Finset (Fin k)} {N d : ℕ} (h : TabOk gs T price g S N d)
    (hp : gs <+: gs') : TabOk gs' T price g S N d :=
  fun α hα b hb => (h α hα b hb).mono hp

theorem TabOk.weaken {gs : List Gate} {T : Finset (Fin k) → ℕ → ℕ} {price : Fin k → ℕ}
    {g : Finset (Fin k) → Prop} {S : Finset (Fin k)} {N d d' : ℕ} (h : TabOk gs T price g S N d)
    (hd : d ≤ d') : TabOk gs T price g S N d' :=
  fun α hα b hb => (h α hα b hb).weaken hd (fun _ => Iff.rfl)

theorem forget1 (price : Fin k → ℕ) (g : Finset (Fin k) → Prop) (N d : ℕ) {S : Finset (Fin k)} {i : Fin k}
    (hi : i ∈ S) (gs : List Gate) (T : Finset (Fin k) → ℕ → ℕ) (hg : Good k gs)
    (hT : TabOk gs T price g S N d) :
    ∃ (gs' : List Gate) (T' : Finset (Fin k) → ℕ → ℕ), gs <+: gs' ∧
      gs'.length ≤ gs.length + 2^S.card * N ∧ Good k gs' ∧ TabOk gs' T' price g (S.erase i) N (d+2) := by
  classical
  set L := ((S.erase i).powerset ×ˢ Finset.range N).toList with hL
  have memL : ∀ x : Finset (Fin k) × ℕ, x ∈ L ↔ x.1 ⊆ S.erase i ∧ x.2 < N := by
    intro x; rw [hL, Finset.mem_toList, Finset.mem_product, Finset.mem_powerset, Finset.mem_range]
  have lenL : L.length = 2^(S.card - 1) * N := by
    rw [hL, Finset.length_toList, Finset.card_product, Finset.card_powerset, Finset.card_range,
      Finset.card_erase_of_mem hi]
  obtain ⟨gs1, c1, p1, l1, g1, h1⟩ := andLayer L (fun _ => i.val)
    (fun x => if price i ≤ x.2 then T (insert i x.1) (x.2 - price i) else k)
    (fun _ I => i ∈ I) (fun x I => if price i ≤ x.2 then SP price g S (insert i x.1) (x.2 - price i) I else False)
    d gs hg (fun x _ => (ok_var gs i).weaken (Nat.zero_le _) (fun _ => Iff.rfl)) (fun x hx => by
      rw [memL] at hx
      by_cases hp : price i ≤ x.2
      · simp only [hp, ↓reduceIte]
        exact hT _ (Finset.insert_subset hi (hx.1.trans (Finset.erase_subset _ _))) _ (by omega)
      · simp only [hp, ↓reduceIte]
        exact (ok_false gs).weaken (Nat.zero_le _) (fun _ => Iff.rfl))
  obtain ⟨gs2, c2, p2, l2, g2, h2⟩ := orLayer L (fun x => T x.1 x.2) c1
    (fun x I => SP price g S x.1 x.2 I)
    (fun x I => i ∈ I ∧ if price i ≤ x.2 then SP price g S (insert i x.1) (x.2 - price i) I else False)
    (d+1) gs1 g1 (fun x hx => by
      rw [memL] at hx
      exact ((hT _ (hx.1.trans (Finset.erase_subset _ _)) _ hx.2).mono p1).weaken (by omega)
        (fun _ => Iff.rfl)) h1
  refine ⟨gs2, fun α b => c2 (α, b), p1.trans p2, ?_, g2, ?_⟩
  · have hc : S.card = (S.card - 1) + 1 := by
      have := Finset.card_pos.2 ⟨i, hi⟩; omega
    have e : 2^S.card * N = 2 * (2^(S.card - 1) * N) := by rw [hc, pow_succ]; simp; ring
    rw [e]; omega
  · intro α hα b hb
    refine (h2 (α, b) ((memL _).2 ⟨hα, hb⟩)).weaken le_rfl (fun I => ?_)
    rw [SP_forget price g hi hα b I]
    by_cases hp : price i ≤ b
    · simp only [hp, ↓reduceIte, true_and]
    · simp only [hp, ↓reduceIte, and_false, false_and]

theorem forgetMany (price : Fin k → ℕ) (g : Finset (Fin k) → Prop) (N : ℕ) : ∀ (m : ℕ)
    (S S' : Finset (Fin k)) (gs : List Gate) (T : Finset (Fin k) → ℕ → ℕ) (d : ℕ),
    S' ⊆ S → (S \ S').card = m → Good k gs → TabOk gs T price g S N d →
    ∃ (gs' : List Gate) (T' : Finset (Fin k) → ℕ → ℕ), gs <+: gs' ∧
      gs'.length ≤ gs.length + 2 * 2^S.card * N ∧ Good k gs' ∧ TabOk gs' T' price g S' N (d + 2*m) := by
  intro m
  induction m with
  | zero =>
    intro S S' gs T d hsub hcard hg hT
    have : S = S' := by
      apply Finset.Subset.antisymm _ hsub
      intro y hy
      by_contra hy'
      have : y ∈ S \ S' := Finset.mem_sdiff.2 ⟨hy, hy'⟩
      rw [Finset.card_eq_zero.1 hcard] at this
      simp at this
    subst this
    exact ⟨gs, T, List.prefix_refl _, by omega, hg, by simpa using hT⟩
  | succ m ih =>
    intro S S' gs T d hsub hcard hg hT
    obtain ⟨i, hi⟩ : (S \ S').Nonempty := Finset.card_pos.1 (by omega)
    have hiS := (Finset.mem_sdiff.1 hi).1
    have hiS' := (Finset.mem_sdiff.1 hi).2
    obtain ⟨gs1, T1, p1, l1, g1, h1⟩ := forget1 price g N d hiS gs T hg hT
    have hsub' : S' ⊆ S.erase i := fun y hy => Finset.mem_erase.2 ⟨fun h => hiS' (h ▸ hy), hsub hy⟩
    have hcard' : (S.erase i \ S').card = m := by
      have : S.erase i \ S' = (S \ S').erase i := by
        ext y; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem hi, hcard]; rfl
    obtain ⟨gs2, T2, p2, l2, g2, h2⟩ := ih (S.erase i) S' gs1 T1 (d+2) hsub' hcard' g1 h1
    refine ⟨gs2, T2, p1.trans p2, ?_, g2, h2.weaken (by omega)⟩
    rw [Finset.card_erase_of_mem hiS] at l2
    have hc : S.card = (S.card - 1) + 1 := by
      have := Finset.card_pos.2 ⟨i, hiS⟩; omega
    have e : 2^S.card * N = 2 * (2^(S.card - 1) * N) := by rw [hc, pow_succ]; simp; ring
    have e2 : 2 * 2^(S.card - 1) * N = 2^(S.card - 1) * N + 2^(S.card - 1) * N := by ring
    have e3 : 2 * 2^S.card * N = 2 * (2^S.card * N) := by ring
    rw [e2] at l2
    rw [e3, e]
    omega

end Table

section Model

variable {k : ℕ} [dk : DecidableEq (Fin k)]

def Mono (f : ℕ → Finset (Fin k) → Prop) (P1 P2 : ℕ → Finset (Fin k)) : Prop :=
  ∀ j X X', (∀ i ∈ P1 j, i ∈ X → i ∈ X') → (∀ i ∈ P2 j, i ∈ X' → i ∈ X) → f j X → f j X'

variable {f : ℕ → Finset (Fin k) → Prop} {P1 P2 : ℕ → Finset (Fin k)}

theorem Mono.agree (hm : Mono f P1 P2) {j : ℕ} {X X' : Finset (Fin k)}
    (h : ∀ i ∈ P1 j ∪ P2 j, (i ∈ X ↔ i ∈ X')) : f j X ↔ f j X' :=
  ⟨hm j X X' (fun i hi => (h i (Finset.mem_union_left _ hi)).1)
      (fun i hi => (h i (Finset.mem_union_right _ hi)).2),
    hm j X' X (fun i hi => (h i (Finset.mem_union_left _ hi)).2)
      (fun i hi => (h i (Finset.mem_union_right _ hi)).1)⟩

theorem restrict (hm : Mono f P1 P2) (price : Fin k → ℕ) (j : ℕ) {F α : Finset (Fin k)} (hα : α ⊆ F)
    (b : ℕ) (I : Finset (Fin k)) :
    SP price (f j) F α b I ↔ SP price (f j) (F ∩ (P1 j ∪ P2 j)) (α ∩ (P1 j ∪ P2 j)) b I := by
  set V := P1 j ∪ P2 j
  have hαF : ∀ y, y ∈ α → y ∈ F := fun y hy => hα hy
  constructor
  · rintro ⟨X, h1, h2, h3, h4⟩
    have m1 : ∀ y, y ∈ X ∧ y ∈ F ↔ y ∈ α := fun y => by rw [← h1, Finset.mem_inter]
    have e2 : (X \ F ∪ α ∩ V) \ (F ∩ V) = X \ F := by
      ext y; have := hαF y
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
    refine ⟨X \ F ∪ α ∩ V, ?_, by rw [e2]; exact h2, by rw [e2]; exact h3, ?_⟩
    · ext y; have := hαF y
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
    · refine (hm.agree (fun y hy => ?_)).1 h4
      have := hαF y; have := m1 y
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      have hyV : y ∈ V := hy
      tauto
  · rintro ⟨X, h1, h2, h3, h4⟩
    have m1 : ∀ y, y ∈ X ∧ (y ∈ F ∧ y ∈ V) ↔ y ∈ α ∧ y ∈ V := fun y => by
      rw [← Finset.mem_inter, ← Finset.mem_inter, ← Finset.mem_inter, h1]
    have e2 : ((X ∩ V) \ F ∪ α) \ F = (X ∩ V) \ F := by
      ext y; have := hαF y
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
    have sub : (X ∩ V) \ F ⊆ X \ (F ∩ V) := by
      intro y; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    refine ⟨(X ∩ V) \ F ∪ α, ?_, by rw [e2]; exact sub.trans h2,
      by rw [e2]; exact (Finset.sum_le_sum_of_subset sub).trans h3, ?_⟩
    · ext y; have := hαF y
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
    · refine (hm.agree (fun y hy => ?_)).1 h4
      have := hαF y; have := m1 y
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      have hyV : y ∈ V := hy
      tauto

theorem sum_ui (price : Fin k → ℕ) (s t : Finset (Fin k)) :
    (s ∪ t).sum price + (s ∩ t).sum price = s.sum price + t.sum price := Finset.sum_union_inter

theorem sum_sub (price : Fin k → ℕ) {s t : Finset (Fin k)} (h : s ⊆ t) : s.sum price ≤ t.sum price :=
  Finset.sum_le_sum_of_subset h

theorem andComb (hm : Mono f P1 P2) (price : Fin k → ℕ) {a b w : ℕ} (hw : ∀ X, f w X ↔ f a X ∧ f b X)
    {F α : Finset (Fin k)} (hα : α ⊆ F) (c1 : P1 a ∩ P2 b ⊆ F) (c2 : P2 a ∩ P1 b ⊆ F)
    (c3 : ∀ i ∈ P1 a ∩ P1 b, 0 < price i → i ∈ F) (β : ℕ) (I : Finset (Fin k)) :
    SP price (f w) F α β I ↔ ∃ b1 b2, b1 + b2 ≤ β ∧ SP price (f a) F α b1 I ∧ SP price (f b) F α b2 I := by
  have hαF : ∀ y, y ∈ α → y ∈ F := fun y hy => hα hy
  have c1' : ∀ y, y ∈ P1 a → y ∈ P2 b → y ∈ F := fun y h1 h2 => c1 (Finset.mem_inter.2 ⟨h1, h2⟩)
  have c2' : ∀ y, y ∈ P2 a → y ∈ P1 b → y ∈ F := fun y h1 h2 => c2 (Finset.mem_inter.2 ⟨h1, h2⟩)
  constructor
  · rintro ⟨X, h1, h2, h3, h4⟩
    rw [hw] at h4
    have m1 : ∀ y, y ∈ X ∧ y ∈ F ↔ y ∈ α := fun y => by rw [← h1, Finset.mem_inter]
    have part : ∀ c, (c = a ∨ c = b) → f c X → SP price (f c) F α (((X ∩ P1 c) \ F).sum price) I := by
      intro c _ hc
      have e2 : (α ∪ (X ∩ P1 c) \ F) \ F = (X ∩ P1 c) \ F := by
        ext y; have := hαF y
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
      refine ⟨α ∪ (X ∩ P1 c) \ F, ?_, ?_, by rw [e2], ?_⟩
      · ext y; have := hαF y
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
      · rw [e2]; refine fun y hy => h2 ?_
        simp only [Finset.mem_sdiff, Finset.mem_inter] at hy ⊢; tauto
      · refine hm c X _ (fun y _ hy => ?_) (fun y _ hy => ?_) hc
        · have := m1 y
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
        · have := m1 y
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hy; tauto
    refine ⟨_, _, ?_, part a (Or.inl rfl) h4.1, part b (Or.inr rfl) h4.2⟩
    have hu := sum_ui price ((X ∩ P1 a) \ F) ((X ∩ P1 b) \ F)
    have h0 : (((X ∩ P1 a) \ F) ∩ ((X ∩ P1 b) \ F)).sum price = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hy
      by_contra hne
      exact hy.1.2 (c3 y (Finset.mem_inter.2 ⟨hy.1.1.2, hy.2.1.2⟩) (Nat.pos_of_ne_zero hne))
    have hsub : ((X ∩ P1 a) \ F) ∪ ((X ∩ P1 b) \ F) ⊆ X \ F := by
      intro y; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
    have := sum_sub price hsub
    omega
  · rintro ⟨b1, b2, hb, ⟨Xa, a1, a2, a3, a4⟩, ⟨Xb, e1, e2, e3, e4⟩⟩
    have ma : ∀ y, y ∈ Xa ∧ y ∈ F ↔ y ∈ α := fun y => by rw [← a1, Finset.mem_inter]
    have mb : ∀ y, y ∈ Xb ∧ y ∈ F ↔ y ∈ α := fun y => by rw [← e1, Finset.mem_inter]
    set X := α ∪ ((Xa ∩ P1 a) \ F) ∪ ((Xb ∩ P1 b) \ F) with hX
    have eX : X \ F = ((Xa ∩ P1 a) \ F) ∪ ((Xb ∩ P1 b) \ F) := by
      ext y; have := hαF y
      simp only [hX, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
    refine ⟨X, ?_, ?_, ?_, ?_⟩
    · ext y; have := hαF y
      simp only [hX, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
    · rw [eX]; intro y hy
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hy
      rcases hy with hy | hy
      · exact a2 (Finset.mem_sdiff.2 ⟨hy.1.1, hy.2⟩)
      · exact e2 (Finset.mem_sdiff.2 ⟨hy.1.1, hy.2⟩)
    · rw [eX]
      have hu := sum_ui price ((Xa ∩ P1 a) \ F) ((Xb ∩ P1 b) \ F)
      have s1 : (Xa ∩ P1 a) \ F ⊆ Xa \ F := by
        intro y; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      have s2 : (Xb ∩ P1 b) \ F ⊆ Xb \ F := by
        intro y; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      have := sum_sub price s1
      have := sum_sub price s2
      omega
    · rw [hw]
      constructor
      · refine hm a Xa X (fun y _ hy => ?_) (fun y hy2 hy => ?_) a4
        · have := ma y
          simp only [hX, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
        · have := ma y; have := c2' y hy2
          simp only [hX, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hy; tauto
      · refine hm b Xb X (fun y _ hy => ?_) (fun y hy2 hy => ?_) e4
        · have := mb y
          simp only [hX, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
        · have := mb y; have := c1' y
          simp only [hX, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hy; tauto

theorem SP_congr {price : Fin k → ℕ} {g g' : Finset (Fin k) → Prop} (h : ∀ X, g X ↔ g' X)
    (S α : Finset (Fin k)) (b : ℕ) (I : Finset (Fin k)) : SP price g S α b I ↔ SP price g' S α b I := by
  unfold SP; simp only [h]

theorem SP_or {price : Fin k → ℕ} {g g1 g2 : Finset (Fin k) → Prop} (h : ∀ X, g X ↔ g1 X ∨ g2 X)
    (S α : Finset (Fin k)) (b : ℕ) (I : Finset (Fin k)) :
    SP price g S α b I ↔ SP price g1 S α b I ∨ SP price g2 S α b I := by
  unfold SP; simp only [h]
  constructor
  · rintro ⟨X, h1, h2, h3, h4 | h4⟩
    · exact Or.inl ⟨X, h1, h2, h3, h4⟩
    · exact Or.inr ⟨X, h1, h2, h3, h4⟩
  · rintro (⟨X, h1, h2, h3, h4⟩ | ⟨X, h1, h2, h3, h4⟩)
    · exact ⟨X, h1, h2, h3, Or.inl h4⟩
    · exact ⟨X, h1, h2, h3, Or.inr h4⟩

theorem SP_true {price : Fin k → ℕ} {g : Finset (Fin k) → Prop} (h : ∀ X, g X)
    {S α : Finset (Fin k)} (hα : α ⊆ S) (b : ℕ) (I : Finset (Fin k)) : SP price g S α b I :=
  ⟨α, Finset.inter_eq_left.2 hα, by rw [Finset.sdiff_eq_empty_iff_subset.2 hα]; simp,
    by rw [Finset.sdiff_eq_empty_iff_subset.2 hα]; simp, h α⟩

theorem SP_false {price : Fin k → ℕ} {g : Finset (Fin k) → Prop} (h : ∀ X, ¬ g X)
    {S α : Finset (Fin k)} (b : ℕ) (I : Finset (Fin k)) : ¬ SP price g S α b I :=
  fun ⟨X, _, _, _, h4⟩ => h X h4

end Model

section Main

variable {k : ℕ} [dk : DecidableEq (Fin k)]

theorem shrink (price : Fin k → ℕ) (g : Finset (Fin k) → Prop) (N w : ℕ) {S S' : Finset (Fin k)}
    (gs : List Gate) (T : Finset (Fin k) → ℕ → ℕ) (d : ℕ) (hsub : S' ⊆ S) (hc : S.card ≤ w)
    (hg : Good k gs) (hT : TabOk gs T price g S N d) :
    ∃ (gs' : List Gate) (T' : Finset (Fin k) → ℕ → ℕ), gs <+: gs' ∧
      gs'.length ≤ gs.length + 2*(2^w*N) ∧ Good k gs' ∧ TabOk gs' T' price g S' N (d + 2*w) := by
  obtain ⟨gs', T', p, l, g', h⟩ := forgetMany price g N _ S S' gs T d hsub rfl hg hT
  have hm : (S \ S').card ≤ w := (Finset.card_le_card Finset.sdiff_subset).trans hc
  have hp : 2^S.card * N ≤ 2^w * N := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hc)
  refine ⟨gs', T', p, ?_, g', h.weaken (by omega)⟩
  have : 2 * 2^S.card * N = 2 * (2^S.card * N) := by ring
  omega

theorem gateStep (v w : ℕ) (price : Fin k → ℕ) (f : ℕ → Finset (Fin k) → Prop)
    (P1 P2 : ℕ → Finset (Fin k)) (hm : Mono f P1 P2) (B : ℕ → Finset (Fin k)) (dD : ℕ → ℕ)
    (wo : ℕ) (op : GateOp) (ins : List ℕ) (cr : Finset (Fin k))
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hsemA : op = GateOp.and → ∀ X, f wo X ↔ ∀ j ∈ ins, f j X)
    (hsemO : op = GateOp.or → ∀ X, f wo X ↔ ∃ j ∈ ins, f j X)
    (hV : ∀ i, i ∈ P1 wo ∪ P2 wo ↔ ∃ j ∈ ins, i ∈ P1 j ∪ P2 j)
    (hBV : B wo ⊆ P1 wo ∪ P2 wo)
    (hleg : ∀ j ∈ ins, (B wo ∪ cr) ∩ (P1 j ∪ P2 j) ⊆ B j)
    (hcr : op = GateOp.and → ∀ a b, ins = [a, b] → P1 a ∩ P2 b ⊆ cr ∧ P2 a ∩ P1 b ⊆ cr ∧
      ∀ i ∈ P1 a ∩ P1 b, 0 < price i → i ∈ cr)
    (hbnd : (B wo ∪ cr).card ≤ w) (hBj : ∀ j ∈ ins, (B j).card ≤ w)
    (hdep : dD wo = 1 + ins.foldl (fun m j => max m (dD j)) 0)
    (gs : List Gate) (hg : Good k gs) (T : ℕ → Finset (Fin k) → ℕ → ℕ)
    (hT : ∀ j ∈ ins, TabOk gs (T j) price (f j) (B j) (2^v) ((4*w+v+1) * dD j)) :
    ∃ (gs' : List Gate) (T' : Finset (Fin k) → ℕ → ℕ), gs <+: gs' ∧
      gs'.length ≤ gs.length + (2*v+8)*(2^v*2^w) ∧ Good k gs' ∧
      TabOk gs' T' price (f wo) (B wo) (2^v) ((4*w+v+1) * dD wo) := by
  classical
  have hQ : 2^w * 2^v = 2^v * 2^w := by ring
  have hQ0 : 0 ≤ v * (2^v*2^w) := Nat.zero_le _
  match ins, hlen, hsemA, hsemO, hV, hleg, hcr, hBj, hdep, hT with
  | [], _, hsemA, hsemO, _, _, _, _, hdep, _ =>
    refine ⟨gs, fun _ _ => if op = GateOp.and then k+1 else k, List.prefix_refl _, by omega, hg, ?_⟩
    intro α hα b hb
    by_cases ho : op = GateOp.and
    · simp only [ho, ↓reduceIte]
      exact (ok_true gs).weaken (Nat.zero_le _) (fun I => ⟨fun _ => SP_true (fun X => by
        rw [hsemA ho X]; simp) hα b I, fun _ => trivial⟩)
    · simp only [ho, ↓reduceIte]
      have hor : op = GateOp.or := hop.resolve_left ho
      exact (ok_false gs).weaken (Nat.zero_le _) (fun I => ⟨fun h => h.elim, fun h => SP_false (fun X hX => by
        rw [hsemO hor X] at hX; simp at hX) b I h⟩)
  | [a], _, hsemA, hsemO, hV, hleg, _, hBj, hdep, hT =>
    have hsem' : ∀ X, f wo X ↔ f a X := by
      intro X; rcases hop with ho | ho
      · rw [hsemA ho X]; simp
      · rw [hsemO ho X]; simp
    have hsub : B wo ⊆ B a := by
      intro y hy
      have hy' := (hV y).1 (hBV hy)
      simp only [List.mem_singleton, exists_eq_left] at hy'
      exact hleg a (List.mem_singleton_self a) (Finset.mem_inter.2 ⟨Finset.mem_union_left _ hy, hy'⟩)
    obtain ⟨gs', T', p, l, g', h⟩ := shrink price (f a) (2^v) w gs (T a) _ hsub
      (hBj a (List.mem_singleton_self a)) hg (hT a (List.mem_singleton_self a))
    refine ⟨gs', T', p, ?_, g', fun α hα b hb => ((h α hα b hb).weaken ?_ (fun I =>
      (SP_congr hsem' _ _ _ I).symm))⟩
    · rw [hQ] at l
      have : (2*v+8)*(2^v*2^w) = 2*(v*(2^v*2^w)) + 8*(2^v*2^w) := by ring
      omega
    · rw [hdep]
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_max]
      have : (4*w+v+1) * (1 + dD a) = (4*w+v+1) + (4*w+v+1) * dD a := by ring
      omega
  | [a, c], _, hsemA, hsemO, hV, hleg, hcr, hBj, hdep, hT =>
    set F := B wo ∪ cr with hF
    set Va := P1 a ∪ P2 a
    set Vb := P1 c ∪ P2 c
    set K := 4*w+v+1 with hK
    have ma : a ∈ [a, c] := by simp
    have mb : c ∈ [a, c] := by simp
    obtain ⟨gsA, TA, pA, lA, gA, hTA⟩ := shrink price (f a) (2^v) w gs (T a) _ (hleg a ma)
      (hBj a ma) hg (hT a ma)
    obtain ⟨gsB, TB, pB, lB, gB, hTB⟩ := shrink price (f c) (2^v) w gsA (T c) _ (hleg c mb)
      (hBj c mb) gA ((hT c mb).mono pA)
    set M := max (dD a) (dD c) with hM
    set dd := K * M + 2*w with hdd
    have hKa : K * dD a ≤ K * M := Nat.mul_le_mul_left _ (le_max_left _ _)
    have hKb : K * dD c ≤ K * M := Nat.mul_le_mul_left _ (le_max_right _ _)
    have hTA' : TabOk gsB TA price (f a) (F ∩ Va) (2^v) dd := (hTA.mono pB).weaken (by omega)
    have hTB' : TabOk gsB TB price (f c) (F ∩ Vb) (2^v) dd := hTB.weaken (by omega)
    have subI : ∀ {α : Finset (Fin k)} {V : Finset (Fin k)}, α ⊆ F → α ∩ V ⊆ F ∩ V := fun hα y hy =>
      Finset.mem_inter.2 ⟨hα (Finset.mem_inter.1 hy).1, (Finset.mem_inter.1 hy).2⟩
    have hF2 : 2^F.card ≤ 2^w := Nat.pow_le_pow_right (by norm_num) hbnd
    obtain ⟨gsC, TC, pC, lC, gC, hTC⟩ : ∃ (gsC : List Gate) (TC : Finset (Fin k) → ℕ → ℕ),
        gsB <+: gsC ∧ gsC.length ≤ gsB.length + 2^F.card * ((2*v+2)*2^v) ∧ Good k gsC ∧
        TabOk gsC TC price (f wo) F (2^v) (dd+v+1) := by
      rcases hop with hand | hor
      · have hw : ∀ X, f wo X ↔ f a X ∧ f c X := by intro X; rw [hsemA hand X]; simp
        obtain ⟨c1, c2, c3⟩ := hcr hand a c rfl
        have c1' : P1 a ∩ P2 c ⊆ F := c1.trans Finset.subset_union_right
        have c2' : P2 a ∩ P1 c ⊆ F := c2.trans Finset.subset_union_right
        have c3' : ∀ i ∈ P1 a ∩ P1 c, 0 < price i → i ∈ F :=
          fun i hi hp => Finset.mem_union_right _ (c3 i hi hp)
        obtain ⟨gsC, out, pC, lC, gC, hC⟩ := forEach (k := k) ((2*v+2)*2^v)
          (fun gs α (row : ℕ → ℕ) => ∀ b < 2^v, Ok k gs (row b) (SP price (f wo) F α b) (dd+v+1))
          (fun _ _ _ _ hp h b hb => (h b hb).mono hp) F.powerset.toList gsB gB
          (fun α hα gs' hp hg' => by
            have hαF : α ⊆ F := by simpa using hα
            obtain ⟨gs'', C, p, l, g, hCC⟩ := addRows v gs' (TA (α ∩ Va)) (TB (α ∩ Vb))
              (fun I b => SP price (f a) (F ∩ Va) (α ∩ Va) b I)
              (fun I b => SP price (f c) (F ∩ Vb) (α ∩ Vb) b I) dd hg'
              (fun I b h => SP_succ h) (fun I b h => SP_succ h)
              (fun b hb => (hTA' _ (subI hαF) b hb).mono hp)
              (fun b hb => (hTB' _ (subI hαF) b hb).mono hp)
            refine ⟨gs'', C, p, l, g, fun b hb => (hCC b hb).weaken le_rfl (fun I => ?_)⟩
            rw [andComb hm price hw hαF c1' c2' c3' b I]
            simp only [restrict hm price a hαF, restrict hm price c hαF]
            rfl)
        refine ⟨gsC, out, pC, ?_, gC, fun α hα b hb => hC α (by simpa using hα) b hb⟩
        rw [Finset.length_toList, Finset.card_powerset] at lC
        exact lC
      · have hw : ∀ X, f wo X ↔ f a X ∨ f c X := by intro X; rw [hsemO hor X]; simp
        set L := (F.powerset ×ˢ Finset.range (2^v)).toList with hL
        have memL : ∀ x : Finset (Fin k) × ℕ, x ∈ L ↔ x.1 ⊆ F ∧ x.2 < 2^v := by
          intro x; rw [hL, Finset.mem_toList, Finset.mem_product, Finset.mem_powerset, Finset.mem_range]
        have lenL : L.length = 2^F.card * 2^v := by
          rw [hL, Finset.length_toList, Finset.card_product, Finset.card_powerset, Finset.card_range]
        obtain ⟨gsC, cc, pC, lC, gC, hC⟩ := orLayer L (fun x => TA (x.1 ∩ Va) x.2) (fun x => TB (x.1 ∩ Vb) x.2)
          (fun x I => SP price (f a) (F ∩ Va) (x.1 ∩ Va) x.2 I)
          (fun x I => SP price (f c) (F ∩ Vb) (x.1 ∩ Vb) x.2 I) dd gsB gB
          (fun x hx => hTA' _ (subI ((memL x).1 hx).1) _ ((memL x).1 hx).2)
          (fun x hx => hTB' _ (subI ((memL x).1 hx).1) _ ((memL x).1 hx).2)
        refine ⟨gsC, fun α b => cc (α, b), pC, ?_, gC, fun α hα b hb =>
          (hC (α, b) ((memL _).2 ⟨hα, hb⟩)).weaken (by omega) (fun I => ?_)⟩
        · rw [lenL] at lC
          have : 2^F.card * 2^v ≤ 2^F.card * ((2*v+2)*2^v) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
          omega
        · rw [SP_or hw, restrict hm price a hα, restrict hm price c hα]
    obtain ⟨gsD, TD, pD, lD, gD, hTD⟩ := shrink price (f wo) (2^v) w gsC TC _ Finset.subset_union_left
      hbnd gC hTC
    refine ⟨gsD, TD, pA.trans (pB.trans (pC.trans pD)), ?_, gD, hTD.weaken ?_⟩
    · have e1 : 2^F.card * ((2*v+2)*2^v) ≤ 2^w * ((2*v+2)*2^v) := Nat.mul_le_mul_right _ hF2
      have e2 : 2^w * ((2*v+2)*2^v) = 2*(v*(2^v*2^w)) + 2*(2^v*2^w) := by ring
      have e3 : (2*v+8)*(2^v*2^w) = 2*(v*(2^v*2^w)) + 8*(2^v*2^w) := by ring
      rw [hQ] at lA lB lD
      omega
    · rw [hdep]
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_max]
      have : K * (1 + M) = K + K * M := by ring
      rw [← hM, this]
      omega
  | _ :: _ :: _ :: _, hlen, _, _, _, _, _, _, _, _ => simp at hlen

theorem build (v w : ℕ) (price : Fin k → ℕ) (f : ℕ → Finset (Fin k) → Prop)
    (P1 P2 : ℕ → Finset (Fin k)) (hm : Mono f P1 P2) (B : ℕ → Finset (Fin k)) (dD : ℕ → ℕ)
    (n0 s : ℕ) (op : ℕ → GateOp) (ins : ℕ → List ℕ) (cr : ℕ → Finset (Fin k))
    (hop : ∀ t < s, op t = GateOp.and ∨ op t = GateOp.or)
    (hlen : ∀ t < s, (ins t).length ≤ 2)
    (hrb : ∀ t < s, ∀ j ∈ ins t, j < n0 + t)
    (hsemA : ∀ t < s, op t = GateOp.and → ∀ X, f (n0+t) X ↔ ∀ j ∈ ins t, f j X)
    (hsemO : ∀ t < s, op t = GateOp.or → ∀ X, f (n0+t) X ↔ ∃ j ∈ ins t, f j X)
    (hV : ∀ t < s, ∀ i, i ∈ P1 (n0+t) ∪ P2 (n0+t) ↔ ∃ j ∈ ins t, i ∈ P1 j ∪ P2 j)
    (hBV : ∀ j < n0 + s, B j ⊆ P1 j ∪ P2 j)
    (hleg : ∀ t < s, ∀ j ∈ ins t, (B (n0+t) ∪ cr t) ∩ (P1 j ∪ P2 j) ⊆ B j)
    (hcr : ∀ t < s, op t = GateOp.and → ∀ a b, ins t = [a, b] → P1 a ∩ P2 b ⊆ cr t ∧
      P2 a ∩ P1 b ⊆ cr t ∧ ∀ i ∈ P1 a ∩ P1 b, 0 < price i → i ∈ cr t)
    (hbnd0 : ∀ j < n0, (B j).card ≤ w)
    (hbnd : ∀ t < s, (B (n0+t) ∪ cr t).card ≤ w)
    (hdep : ∀ t < s, dD (n0+t) = 1 + (ins t).foldl (fun m j => max m (dD j)) 0)
    (hleaf : ∀ j S α b, ∃ ℓ, j < n0 → α ⊆ S → ∀ gs, Ok k gs ℓ (SP price (f j) S α b) 0) :
    ∃ (gs : List Gate) (tap : ℕ → ℕ → ℕ), Good k gs ∧ gs.length ≤ s * ((2*v+10)*2^v*2^w) ∧
      ∀ j < n0 + s, ∀ b < 2^v, Ok k gs (tap j b) (SP price (f j) ∅ ∅ b) ((4*w+v+1) * dD j + 2*w) := by
  classical
  choose leaf hleaf using hleaf
  have main : ∀ t ≤ s, ∃ (gs : List Gate) (T : ℕ → Finset (Fin k) → ℕ → ℕ) (tap : ℕ → ℕ → ℕ),
      Good k gs ∧ gs.length ≤ t * ((2*v+10)*2^v*2^w) ∧
      (∀ j < n0 + t, TabOk gs (T j) price (f j) (B j) (2^v) ((4*w+v+1) * dD j)) ∧
      (∀ j < n0 + t, ∀ b < 2^v, Ok k gs (tap j b) (SP price (f j) ∅ ∅ b) ((4*w+v+1) * dD j + 2*w)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨[], fun j => leaf j (B j), fun j b => leaf j ∅ ∅ b, fun m hm => absurd hm (by simp),
        by simp, ?_, ?_⟩
      · intro j hj α hα b hb
        exact (hleaf j (B j) α b (by omega) hα []).weaken (Nat.zero_le _) (fun _ => Iff.rfl)
      · intro j hj b hb
        exact (hleaf j ∅ ∅ b (by omega) (subset_refl _) []).weaken (Nat.zero_le _) (fun _ => Iff.rfl)
    | succ t ih =>
      intro ht
      obtain ⟨gs, T, tap, hg, hl, hT, htap⟩ := ih (by omega)
      have hts : t < s := by omega
      have hBj : ∀ j ∈ ins t, (B j).card ≤ w := by
        intro j hj
        have hj' := hrb t hts j hj
        rcases Nat.lt_or_ge j n0 with h | h
        · exact hbnd0 j h
        · obtain ⟨t', rfl⟩ : ∃ t', j = n0 + t' := ⟨j - n0, by omega⟩
          exact (Finset.card_le_card Finset.subset_union_left).trans (hbnd t' (by omega))
      obtain ⟨gs1, T1, p1, l1, g1, h1⟩ := gateStep v w price f P1 P2 hm B dD (n0+t) (op t) (ins t)
        (cr t) (hop t hts) (hlen t hts) (hsemA t hts) (hsemO t hts) (hV t hts) (hBV _ (by omega))
        (hleg t hts) (hcr t hts) (hbnd t hts) hBj (hdep t hts) gs hg T
        (fun j hj => hT j (hrb t hts j hj))
      have hBc : (B (n0+t)).card ≤ w :=
        (Finset.card_le_card Finset.subset_union_left).trans (hbnd t hts)
      obtain ⟨gs2, T2, p2, l2, g2, h2⟩ := shrink price (f (n0+t)) (2^v) w gs1 T1 _
        (Finset.empty_subset _) hBc g1 h1
      refine ⟨gs2, fun j => if j = n0 + t then T1 else T j,
        fun j b => if j = n0 + t then T2 ∅ b else tap j b, g2, ?_, ?_, ?_⟩
      · have e : (t+1) * ((2*v+10)*2^v*2^w) =
            t * ((2*v+10)*2^v*2^w) + (2*v+8)*(2^v*2^w) + 2*(2^w*2^v) := by ring
        rw [e]; omega
      · intro j hj
        by_cases hjt : j = n0 + t
        · simp only [hjt, ↓reduceIte]; exact h1.mono p2
        · simp only [hjt, ↓reduceIte]; exact (hT j (by omega)).mono (p1.trans p2)
      · intro j hj b hb
        by_cases hjt : j = n0 + t
        · simp only [hjt, ↓reduceIte]; exact h2 ∅ (subset_refl _) b hb
        · simp only [hjt, ↓reduceIte]; exact (htap j (by omega) b hb).mono (p1.trans p2)
  obtain ⟨gs, T, tap, hg, hl, _, htap⟩ := main s le_rfl
  exact ⟨gs, tap, hg, hl, htap⟩

end Main

section DFacts

open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

variable {k : ℕ} [dk : DecidableEq (Fin k)]

noncomputable def word (ones zeros : Finset (Fin k)) : List Bool :=
  List.ofFn (fun j : Fin k => @decide (j ∈ ones) (Classical.propDecidable _)) ++
  List.ofFn (fun j : Fin k => @decide (j ∈ zeros) (Classical.propDecidable _)) ++ [false,true]

def fD (D : Circuit) (j : ℕ) (X : Finset (Fin k)) : Prop :=
  (D.wires (word X (Finset.univ \ X))).getD j false = true

def xs0 : List (Finset (Fin k) × Finset (Fin k)) :=
  List.ofFn (fun j : Fin k => (({j},∅) : Finset (Fin k) × Finset (Fin k))) ++
    List.ofFn (fun j : Fin k => ((∅,{j}) : Finset (Fin k) × Finset (Fin k))) ++ [(∅,∅),(∅,∅)]

def FI (ts : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) : Finset (Fin k) × Finset (Fin k) :=
  g.inputs.foldl (fun v t => (v.1 ∪ (ts.getD t (∅,∅)).1, v.2 ∪ (ts.getD t (∅,∅)).2)) (∅,∅)

def infoD (D : Circuit) : List (Finset (Fin k) × Finset (Fin k)) := sfold FI xs0 D.gates

theorem word_length (X Y : Finset (Fin k)) : (word X Y).length = 2*k+2 := by
  simp [word]; omega

theorem xs0_length : (xs0 (k := k)).length = 2*k+2 := by
  simp [xs0]; omega

theorem word_lo (X Y : Finset (Fin k)) {j : ℕ} (hj : j < k) :
    (word X Y).getD j false = true ↔ (⟨j, hj⟩ : Fin k) ∈ X := by
  simp [word, List.getD_eq_getElem?_getD, List.getElem?_append_left, hj]

theorem word_mid (X Y : Finset (Fin k)) {j : ℕ} (hj : k ≤ j) (hj2 : j < 2*k) :
    (word X Y).getD j false = true ↔ (⟨j - k, by omega⟩ : Fin k) ∈ Y := by
  simp only [word, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp only [List.length_ofFn, List.getElem?_ofFn]
  rw [dif_pos (by omega)]
  simp

theorem word_2k (X Y : Finset (Fin k)) : (word X Y).getD (2*k) false = false := by
  simp only [word, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp [List.length_ofFn, show 2*k - k - k = 0 by omega]

theorem word_2k1 (X Y : Finset (Fin k)) : (word X Y).getD (2*k+1) false = true := by
  simp only [word, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp [List.length_ofFn, show 2*k + 1 - k - k = 1 by omega]

theorem xs0_lo {j : ℕ} (hj : j < k) :
    (xs0 (k := k)).getD j (∅,∅) = ({⟨j, hj⟩}, ∅) := by
  simp only [xs0, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.getElem?_ofFn]
  rw [dif_pos hj]
  simp

theorem xs0_mid {j : ℕ} (hj : k ≤ j) (hj2 : j < 2*k) :
    (xs0 (k := k)).getD j (∅,∅) = (∅, {⟨j - k, by omega⟩}) := by
  simp only [xs0, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp only [List.length_ofFn, List.getElem?_ofFn]
  rw [dif_pos (by omega)]
  simp

theorem xs0_hi {j : ℕ} (hj : 2*k ≤ j) :
    (xs0 (k := k)).getD j (∅,∅) = (∅, ∅) := by
  simp only [xs0, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp only [List.length_ofFn]
  rcases (show j - k - k = 0 ∨ j - k - k = 1 ∨ 2 ≤ j - k - k by omega) with h | h | h
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem reads_get {n : ℕ} {D : Circuit} (hr : ReadsBack n D) :
    ∀ m (hm : m < D.gates.length), ∀ j ∈ D.gates[m].inputs, j < n + m := by
  intro m hm j hj
  apply hr m hm j
  show j ∈ (D.gates.getD m ⟨GateOp.or, []⟩).inputs
  rw [List.getD_eq_getElem _ _ hm]
  exact hj

theorem evF_loc (W1 W2 : List Bool) (g : Gate) (h : ∀ j ∈ g.inputs, W1.getD j false = W2.getD j false) :
    evF W1 g = evF W2 g := by
  unfold evF; congr 1; exact List.map_congr_left h

theorem foldl_max_loc (W1 W2 : List ℕ) (l : List ℕ) (h : ∀ j ∈ l, W1.getD j 0 = W2.getD j 0) (a : ℕ) :
    l.foldl (fun m j => max m (W1.getD j 0)) a = l.foldl (fun m j => max m (W2.getD j 0)) a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

theorem dpF_loc (W1 W2 : List ℕ) (g : Gate) (h : ∀ j ∈ g.inputs, W1.getD j 0 = W2.getD j 0) :
    dpF W1 g = dpF W2 g := by
  unfold dpF; rw [foldl_max_loc W1 W2 _ h]

theorem mem_foldl_union' {β : Type} [DecidableEq β] (F : ℕ → Finset β) (l : List ℕ) (base : Finset β)
    (z : β) : z ∈ l.foldl (fun acc j => acc ∪ F j) base ↔ z ∈ base ∨ ∃ j ∈ l, z ∈ F j := by
  induction l generalizing base with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih, Finset.mem_union]
    constructor
    · rintro ((h | h) | ⟨j', hj', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, List.mem_cons_self, h⟩
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', h⟩
    · rintro (h | ⟨j', hj', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hj' with rfl | h2
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨j', h2, h⟩

theorem foldl_pair (G1 G2 : ℕ → Finset (Fin k)) (l : List ℕ) (base : Finset (Fin k) × Finset (Fin k)) :
    l.foldl (fun v t => (v.1 ∪ G1 t, v.2 ∪ G2 t)) base =
      (l.foldl (fun acc t => acc ∪ G1 t) base.1, l.foldl (fun acc t => acc ∪ G2 t) base.2) := by
  induction l generalizing base with
  | nil => rfl
  | cons j rest ih => simp only [List.foldl_cons]; exact ih _

theorem mem_FI1 (W : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) (x : Fin k) :
    x ∈ (FI W g).1 ↔ ∃ j ∈ g.inputs, x ∈ (W.getD j (∅,∅)).1 := by
  unfold FI
  rw [foldl_pair, mem_foldl_union']
  simp

theorem mem_FI2 (W : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) (x : Fin k) :
    x ∈ (FI W g).2 ↔ ∃ j ∈ g.inputs, x ∈ (W.getD j (∅,∅)).2 := by
  unfold FI
  rw [foldl_pair, mem_foldl_union']
  simp

theorem FI_loc (W1 W2 : List (Finset (Fin k) × Finset (Fin k))) (g : Gate)
    (h : ∀ j ∈ g.inputs, W1.getD j (∅,∅) = W2.getD j (∅,∅)) : FI W1 g = FI W2 g := by
  apply Prod.ext
  · apply Finset.ext; intro x; rw [mem_FI1, mem_FI1]
    constructor
    · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rw [← h j hj]; exact hx⟩
    · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rw [h j hj]; exact hx⟩
  · apply Finset.ext; intro x; rw [mem_FI2, mem_FI2]
    constructor
    · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rw [← h j hj]; exact hx⟩
    · rintro ⟨j, hj, hx⟩; exact ⟨j, hj, by rw [h j hj]; exact hx⟩

variable {D : Circuit}

theorem fD_input (j : ℕ) (hj : j < 2*k+2) (X : Finset (Fin k)) :
    fD D j X ↔ (word X (Finset.univ \ X)).getD j false = true := by
  unfold fD
  rw [show D.wires (word X (Finset.univ \ X)) = sfold evF (word X (Finset.univ \ X)) D.gates from rfl,
    sfold_old _ _ _ _ (by rw [word_length]; exact hj)]

theorem fD_beyond (j : ℕ) (hj : 2*k+2+D.gates.length ≤ j) (X : Finset (Fin k)) : ¬ fD D j X := by
  unfold fD
  rw [show D.wires (word X (Finset.univ \ X)) = sfold evF (word X (Finset.univ \ X)) D.gates from rfl,
    sfold_beyond _ _ _ _ (by rw [word_length]; exact hj)]
  simp

theorem fD_gate (hrb : ReadsBack (2*k+2) D) (t : ℕ) (ht : t < D.gates.length) (X : Finset (Fin k)) :
    fD D (2*k+2+t) X ↔ evF (D.wires (word X (Finset.univ \ X))) D.gates[t] = true := by
  unfold fD
  have := sfold_gate evF false evF_loc (word X (Finset.univ \ X)) D.gates
    (by rw [word_length]; exact reads_get hrb) t ht
  rw [word_length] at this
  exact Iff.of_eq (congrArg (· = true) this)

theorem infoD_input (j : ℕ) (hj : j < 2*k+2) : (infoD (k := k) D).getD j (∅,∅) = (xs0 (k := k)).getD j (∅,∅) := by
  unfold infoD; rw [sfold_old _ _ _ _ (by rw [xs0_length]; exact hj)]

theorem infoD_gate (hrb : ReadsBack (2*k+2) D) (t : ℕ) (ht : t < D.gates.length) :
    (infoD (k := k) D).getD (2*k+2+t) (∅,∅) = FI (infoD D) D.gates[t] := by
  unfold infoD
  have := sfold_gate (FI (k := k)) (∅,∅) FI_loc xs0 D.gates
    (by rw [xs0_length]; exact reads_get hrb) t ht
  rw [xs0_length] at this
  exact this

theorem dep_gate (hrb : ReadsBack (2*k+2) D) (t : ℕ) (ht : t < D.gates.length) :
    (sfold dpF (List.replicate (2*k+2) 0) D.gates).getD (2*k+2+t) 0 =
      1 + D.gates[t].inputs.foldl (fun m j => max m ((sfold dpF (List.replicate (2*k+2) 0) D.gates).getD j 0)) 0 := by
  have := sfold_gate dpF 0 dpF_loc (List.replicate (2*k+2) 0) D.gates
    (by rw [List.length_replicate]; exact reads_get hrb) t ht
  rw [List.length_replicate] at this
  exact this

theorem gate_op (hfan : PEqualNP.MetaComplexity.FanInTwo D) (hnc : PEqualNP.NotBracket.notCount D = 0)
    (t : ℕ) (ht : t < D.gates.length) :
    D.gates[t].op = GateOp.and ∨ D.gates[t].op = GateOp.or := by
  have hmem : D.gates[t] ∈ D.gates := List.getElem_mem ht
  have h1 := (hfan _ hmem).1
  have h2 : D.gates[t].op ≠ GateOp.not := by
    intro h
    unfold PEqualNP.NotBracket.notCount at hnc
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hnc
    exact hnc _ hmem (by simp [h])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h2

theorem mono_D (hfan : PEqualNP.MetaComplexity.FanInTwo D) (hrb : ReadsBack (2*k+2) D)
    (hnc : PEqualNP.NotBracket.notCount D = 0) :
    Mono (fD D) (fun j => ((infoD (k := k) D).getD j (∅,∅)).1) (fun j => ((infoD (k := k) D).getD j (∅,∅)).2) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro X X' h1 h2 hf
  rcases Nat.lt_or_ge j (2*k+2) with hj | hj
  · rw [fD_input j hj] at hf ⊢
    rcases Nat.lt_or_ge j k with hk | hk
    · rw [word_lo _ _ hk] at hf ⊢
      exact h1 _ (by show _ ∈ ((infoD (k := k) D).getD j (∅,∅)).1; rw [infoD_input j hj, xs0_lo hk]; simp) hf
    rcases Nat.lt_or_ge j (2*k) with hk2 | hk2
    · rw [word_mid _ _ hk hk2] at hf ⊢
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hf ⊢
      exact fun h => hf (h2 _ (by show _ ∈ ((infoD (k := k) D).getD j (∅,∅)).2; rw [infoD_input j hj, xs0_mid hk hk2]; simp) h)
    · rcases (show j = 2*k ∨ j = 2*k+1 by omega) with rfl | rfl
      · rw [word_2k] at hf; exact absurd hf (by simp)
      · rw [word_2k1]
  · obtain ⟨t, rfl⟩ : ∃ t, j = 2*k+2+t := ⟨j - (2*k+2), by omega⟩
    rcases Nat.lt_or_ge t D.gates.length with ht | ht
    · have hinp := reads_get hrb t ht
      have sub1 : ∀ i ∈ D.gates[t].inputs, ∀ y ∈ ((infoD (k := k) D).getD i (∅,∅)).1,
          y ∈ ((infoD (k := k) D).getD (2*k+2+t) (∅,∅)).1 := by
        intro i hi y hy; rw [infoD_gate hrb t ht, mem_FI1]; exact ⟨i, hi, hy⟩
      have sub2 : ∀ i ∈ D.gates[t].inputs, ∀ y ∈ ((infoD (k := k) D).getD i (∅,∅)).2,
          y ∈ ((infoD (k := k) D).getD (2*k+2+t) (∅,∅)).2 := by
        intro i hi y hy; rw [infoD_gate hrb t ht, mem_FI2]; exact ⟨i, hi, hy⟩
      have step : ∀ i ∈ D.gates[t].inputs, fD D i X → fD D i X' := fun i hi =>
        ih i (hinp i hi) X X' (fun y hy => h1 y (sub1 i hi y hy)) (fun y hy => h2 y (sub2 i hi y hy))
      rw [fD_gate hrb t ht] at hf ⊢
      rcases gate_op hfan hnc t ht with hop | hop
      · simp only [evF, hop, GateOp.eval, List.all_eq_true, List.mem_map, id] at hf ⊢
        rintro _ ⟨i, hi, rfl⟩
        exact step i hi (hf _ ⟨i, hi, rfl⟩)
      · simp only [evF, hop, GateOp.eval, List.any_eq_true, List.mem_map, id] at hf ⊢
        obtain ⟨_, ⟨i, hi, rfl⟩, hv⟩ := hf
        exact ⟨_, ⟨i, hi, rfl⟩, step i hi hv⟩
    · exact absurd hf (fD_beyond _ (by omega) X)

theorem SP_self {price : Fin k → ℕ} {g : Finset (Fin k) → Prop} {S α : Finset (Fin k)} (hα : α ⊆ S)
    (hg : g α) (b : ℕ) (I : Finset (Fin k)) : SP price g S α b I :=
  ⟨α, Finset.inter_eq_left.2 hα, by rw [Finset.sdiff_eq_empty_iff_subset.2 hα]; simp,
    by rw [Finset.sdiff_eq_empty_iff_subset.2 hα]; simp, hg⟩

theorem leafPos (price : Fin k → ℕ) (g : Finset (Fin k) → Prop) (i : Fin k) (hg : ∀ X, g X ↔ i ∈ X)
    (S α : Finset (Fin k)) (b : ℕ) : ∃ ℓ, α ⊆ S → ∀ gs, Ok k gs ℓ (SP price g S α b) 0 := by
  classical
  by_cases hiS : i ∈ S
  · by_cases hiα : i ∈ α
    · exact ⟨k+1, fun hα gs => (ok_true gs).weaken le_rfl (fun I =>
        ⟨fun _ => SP_self hα ((hg α).2 hiα) b I, fun _ => trivial⟩)⟩
    · refine ⟨k, fun hα gs => (ok_false gs).weaken le_rfl (fun I => ⟨False.elim, ?_⟩)⟩
      rintro ⟨X, h1, -, -, h4⟩
      exact hiα (h1 ▸ Finset.mem_inter.2 ⟨(hg X).1 h4, hiS⟩)
  · by_cases hp : price i ≤ b
    · refine ⟨i.val, fun hα gs => (ok_var gs i).weaken le_rfl (fun I => ⟨fun hI => ?_, ?_⟩)⟩
      · have hαS : ∀ y, y ∈ α → y ∈ S := fun y hy => hα hy
        have e1 : insert i α ∩ S = α := by
          ext y; have := hαS y; simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | h, h'⟩
            · exact absurd h' hiS
            · exact h
          · intro h; exact ⟨Or.inr h, hαS y h⟩
        have e2 : insert i α \ S = {i} := by
          ext y; have := hαS y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | h, h'⟩
            · rfl
            · exact absurd (hαS y h) h'
          · rintro rfl; exact ⟨Or.inl rfl, hiS⟩
        refine ⟨insert i α, e1, by rw [e2]; simpa using hI, by rw [e2]; simpa using hp, ?_⟩
        exact (hg _).2 (Finset.mem_insert_self _ _)
      · rintro ⟨X, -, h2, -, h4⟩
        exact h2 (Finset.mem_sdiff.2 ⟨(hg X).1 h4, hiS⟩)
    · refine ⟨k, fun hα gs => (ok_false gs).weaken le_rfl (fun I => ⟨False.elim, ?_⟩)⟩
      rintro ⟨X, -, -, h3, h4⟩
      have hmem : i ∈ X \ S := Finset.mem_sdiff.2 ⟨(hg X).1 h4, hiS⟩
      have := Finset.single_le_sum (f := price) (fun _ _ => Nat.zero_le _) hmem
      exact hp (le_trans this h3)

theorem leafNeg (price : Fin k → ℕ) (g : Finset (Fin k) → Prop) (i : Fin k) (hg : ∀ X, g X ↔ i ∉ X)
    (S α : Finset (Fin k)) (b : ℕ) : ∃ ℓ, α ⊆ S → ∀ gs, Ok k gs ℓ (SP price g S α b) 0 := by
  classical
  by_cases hiα : i ∈ α
  · refine ⟨k, fun hα gs => (ok_false gs).weaken le_rfl (fun I => ⟨False.elim, ?_⟩)⟩
    rintro ⟨X, h1, -, -, h4⟩
    have : i ∈ X ∩ S := h1 ▸ hiα
    exact (hg X).1 h4 (Finset.mem_inter.1 this).1
  · exact ⟨k+1, fun hα gs => (ok_true gs).weaken le_rfl (fun I =>
      ⟨fun _ => SP_self hα ((hg α).2 hiα) b I, fun _ => trivial⟩)⟩

theorem leaf_D (price : Fin k → ℕ) (j : ℕ) (S α : Finset (Fin k)) (b : ℕ) :
    ∃ ℓ, j < 2*k+2 → α ⊆ S → ∀ gs, Ok k gs ℓ (SP price (fD D j) S α b) 0 := by
  classical
  by_cases hj : j < 2*k+2
  · rcases Nat.lt_or_ge j k with hk | hk
    · obtain ⟨ℓ, h⟩ := leafPos price (fD D j) ⟨j, hk⟩ (fun X => by rw [fD_input j hj, word_lo _ _ hk]) S α b
      exact ⟨ℓ, fun _ => h⟩
    rcases Nat.lt_or_ge j (2*k) with hk2 | hk2
    · obtain ⟨ℓ, h⟩ := leafNeg price (fD D j) ⟨j - k, by omega⟩ (fun X => by
        rw [fD_input j hj, word_mid _ _ hk hk2]; simp) S α b
      exact ⟨ℓ, fun _ => h⟩
    · rcases (show j = 2*k ∨ j = 2*k+1 by omega) with rfl | rfl
      · refine ⟨k, fun _ _ gs => (ok_false gs).weaken le_rfl (fun I => ⟨False.elim, ?_⟩)⟩
        rintro ⟨X, -, -, -, h4⟩
        rw [fD_input _ hj, word_2k] at h4; exact absurd h4 (by simp)
      · exact ⟨k+1, fun _ hα gs => (ok_true gs).weaken le_rfl (fun I =>
          ⟨fun _ => SP_self hα (by rw [fD_input _ hj, word_2k1]) b I, fun _ => trivial⟩)⟩
  · exact ⟨0, fun h => absurd h hj⟩

end DFacts

end PEqualNP.Outside.L_lib_1493

theorem PEqualNP.Outside.L_lib_1493 : (
letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
let word := fun {k : Nat} (ones zeros : Finset (Fin k)) =>
  List.ofFn (fun j : Fin k => decide (j ∈ ones)) ++
  List.ofFn (fun j : Fin k => decide (j ∈ zeros)) ++ [false,true]
let bits := fun {k : Nat} (Y : Finset (Fin k)) =>
  List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true]
let wireInfo := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
  let xs := List.ofFn (fun j : Fin k => (({j},∅) : Finset (Fin k) × Finset (Fin k))) ++
    List.ofFn (fun j : Fin k => ((∅,{j}) : Finset (Fin k) × Finset (Fin k))) ++ [Z,Z]
  D.gates.foldl (fun (ts : List (Finset (Fin k) × Finset (Fin k))) g =>
    ts ++ [g.inputs.foldl (fun v t => let a := ts.getD t Z
                                      (v.1 ∪ a.1,v.2 ∪ a.2)) Z]) xs
let gateAt := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (t : Nat) => D.gates.getD t ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
let depths := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  D.gates.foldl (fun (ts : List Nat) g =>
    ts ++ [1+g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0]) (List.replicate (h+2) 0)
∀ (k cap width : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (held : Nat → Finset (Fin k)) (price : Fin k → Nat),
pos (2*k) D →
let src := 2*k+2
let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
let info := wireInfo k D
let vars := fun (j : Nat) => let s := info.getD j Z
                             s.1 ∪ s.2
let cross := fun (t : Nat) =>
  let g := gateAt D t
  let a := (g.inputs.head?.map (fun j => info.getD j Z)).getD Z
  let b := (g.inputs[1]?.map (fun j => info.getD j Z)).getD Z
  if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then (a.1 ∩ b.2) ∪ (a.2 ∩ b.1) ∪ ((a.1 ∩ b.1).filter (fun j => 0 < price j)) else ∅
let legal := fun (B : Nat → Finset (Fin k)) =>
  (∀ j, j<src+D.size → B j ⊆ vars j) ∧
  ∀ t, t<D.size → ∀ j ∈ (gateAt D t).inputs, (B (src+t) ∪ cross t) ∩ vars j ⊆ B j
let bounded := fun (w : Nat) (B : Nat → Finset (Fin k)) =>
  (∀ j, j<src → (B j).card ≤ w) ∧ ∀ t, t<D.size → (B (src+t) ∪ cross t).card ≤ w
legal held → bounded width held →
let v := Nat.clog 2 (cap+1)
∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (tap : Nat → Fin (cap+1) → Nat), pos k E ∧
  E.size ≤ (2*v+10)*2^v*2^width*D.size ∧ tap D.output (Fin.last cap)=E.output ∧
  ∀ j, j<src+D.size → ∀ b : Fin (cap+1), tap j b<k+2+E.size ∧
    (depths k E).getD (tap j b) 0 ≤ (4*width+v+1)*((depths (2*k) D).getD j 0)+2*width ∧
    ∀ I : Finset (Fin k), (E.wires (bits I)).getD (tap j b) false=true ↔
      ∃ X : Finset (Fin k), X ⊆ I ∧ X.sum price ≤ b.val ∧
        (D.wires (word X (Finset.univ \ X))).getD j false=true) := by
  intro valid pos word bits wireInfo gateAt depths k cap width D held price hpos src Z info vars cross legal bounded hlegal hbdd v
  obtain ⟨⟨hfan, hrb, hout⟩, hnc⟩ := hpos
  letI : DecidableEq (Fin k) := fun a b => Classical.propDecidable (a = b)
  have hrb' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k+2) D := hrb
  have hgt : ∀ t (ht : t < D.size), gateAt D t = D.gates[t] := fun t ht => List.getD_eq_getElem _ _ ht
  obtain ⟨gs, tap, hg, hl, htap⟩ := PEqualNP.Outside.L_lib_1493.build
    (dk := fun a b => Classical.propDecidable (a = b)) v width price
    (PEqualNP.Outside.L_lib_1493.fD (dk := fun a b => Classical.propDecidable (a = b)) D)
    (fun j => ((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD j (∅,∅)).1)
    (fun j => ((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD j (∅,∅)).2)
    (PEqualNP.Outside.L_lib_1493.mono_D (dk := fun a b => Classical.propDecidable (a = b)) hfan hrb' hnc) held
    (fun j => (PEqualNP.Outside.L_lib_1493.sfold PEqualNP.Outside.L_lib_1493.dpF (List.replicate (2*k+2) 0) D.gates).getD j 0)
    (2*k+2) D.size (fun t => (gateAt D t).op) (fun t => (gateAt D t).inputs) cross
    (fun t ht => by rw [hgt t ht]; exact PEqualNP.Outside.L_lib_1493.gate_op hfan hnc t ht)
    (fun t ht => by rw [hgt t ht]; exact (hfan _ (List.getElem_mem ht)).2)
    (fun t ht j hj => hrb t ht j hj)
    (fun t ht hand X => by
      rw [PEqualNP.Outside.L_lib_1493.fD_gate (dk := fun a b => Classical.propDecidable (a = b)) hrb' t ht]
      simp only [hgt t ht] at hand ⊢
      simp [PEqualNP.Outside.L_lib_1493.evF, hand, PEqualNP.CircuitLowerBounds.GateOp.eval,
        PEqualNP.Outside.L_lib_1493.fD])
    (fun t ht hor X => by
      rw [PEqualNP.Outside.L_lib_1493.fD_gate (dk := fun a b => Classical.propDecidable (a = b)) hrb' t ht]
      simp only [hgt t ht] at hor ⊢
      simp [PEqualNP.Outside.L_lib_1493.evF, hor, PEqualNP.CircuitLowerBounds.GateOp.eval,
        PEqualNP.Outside.L_lib_1493.fD])
    (fun t ht i => by
      simp only [hgt t ht]
      rw [Finset.mem_union, PEqualNP.Outside.L_lib_1493.infoD_gate (dk := fun a b => Classical.propDecidable (a = b)) hrb' t ht,
        PEqualNP.Outside.L_lib_1493.mem_FI1 (dk := fun a b => Classical.propDecidable (a = b)), PEqualNP.Outside.L_lib_1493.mem_FI2 (dk := fun a b => Classical.propDecidable (a = b))]
      constructor
      · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
        · exact ⟨j, hj, Finset.mem_union_left _ h⟩
        · exact ⟨j, hj, Finset.mem_union_right _ h⟩
      · rintro ⟨j, hj, h⟩
        rcases Finset.mem_union.1 h with h | h
        · exact Or.inl ⟨j, hj, h⟩
        · exact Or.inr ⟨j, hj, h⟩)
    (fun j hj => hlegal.1 j hj)
    (fun t ht j hj => hlegal.2 t ht j hj)
    (fun t ht hand a b hab => by
      have hc : cross t = ((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD a (∅,∅)).1 ∩ ((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD b (∅,∅)).2 ∪
          ((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD a (∅,∅)).2 ∩ ((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD b (∅,∅)).1 ∪
          @Finset.filter _ (fun j => 0 < price j) (fun j => Classical.propDecidable _) (((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD a (∅,∅)).1 ∩ ((PEqualNP.Outside.L_lib_1493.infoD (dk := fun a b => Classical.propDecidable (a = b)) D).getD b (∅,∅)).1) := by
        try simp only at hand hab
        simp only [cross, hab, hand, List.head?_cons, Option.map_some, Option.getD_some,
          List.getElem?_cons_succ, List.getElem?_cons_zero, if_true]
        rfl
      rw [hc]
      refine ⟨Finset.subset_union_left.trans Finset.subset_union_left,
        Finset.subset_union_right.trans Finset.subset_union_left, fun i hi hp => ?_⟩
      exact Finset.mem_union_right _ ((@Finset.mem_filter _ (fun j => 0 < price j) (fun j => Classical.propDecidable _) _ _).2 ⟨hi, hp⟩))
    hbdd.1 hbdd.2
    (fun t ht => by simp only [hgt t ht]; exact PEqualNP.Outside.L_lib_1493.dep_gate hrb' t ht)
    (fun j S α b => PEqualNP.Outside.L_lib_1493.leaf_D (dk := fun a b => Classical.propDecidable (a = b)) price j S α b)
  have hN : cap + 1 ≤ 2^v := Nat.le_pow_clog (by norm_num) _
  refine ⟨⟨gs, tap D.output cap⟩, fun j b => tap j b.val, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, rfl, ?_⟩
  · intro g hg'
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hg'
    obtain ⟨h1, h2, -⟩ := hg m hm
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> simp [h]
  · intro m hm i hi
    change i ∈ (gs.getD m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs at hi
    rw [List.getD_eq_getElem _ _ hm] at hi
    exact (hg m hm).2.2 i hi
  · exact (htap D.output hout cap (by omega)).1
  · unfold PEqualNP.NotBracket.notCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg'
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hg'
    rcases (hg m hm).1 with h | h <;> simp [h]
  · exact hl.trans (le_of_eq (mul_comm _ _))
  · intro j hj b
    have hb : b.val < 2^v := by have := b.isLt; omega
    obtain ⟨o1, o2, o3⟩ := htap j hj b.val hb
    refine ⟨o1, o3, fun I => (o2 I).trans ?_⟩
    unfold PEqualNP.Outside.L_lib_1493.SP
    simp only [Finset.inter_empty, Finset.sdiff_empty]
    constructor
    · rintro ⟨X, -, h2, h3, h4⟩; exact ⟨X, h2, h3, h4⟩
    · rintro ⟨X, h2, h3, h4⟩; exact ⟨X, trivial, h2, h3, h4⟩
