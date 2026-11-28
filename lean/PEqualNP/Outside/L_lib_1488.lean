import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1488

open Finset

def cb (n j a : Nat) : Nat := if a ≤ j then Nat.choose n (j - a) else 0

lemma card_trace_le {t : Nat} (k : Nat) (R T : Finset (Fin t)) :
    ((univ.powersetCard k).filter (fun X => X ∩ R = T)).card ≤ cb (t - R.card) k T.card := by
  classical
  unfold cb
  split_ifs with h
  · have key : ((univ.powersetCard k).filter (fun X => X ∩ R = T)).card
        ≤ (Rᶜ.powersetCard (k - T.card)).card := by
      apply Finset.card_le_card_of_injOn (fun X => X \ R)
      · intro X hX
        simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_ofPred_eq] at hX
        rw [Finset.mem_coe, mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro y hy
          simp only [mem_sdiff] at hy
          simpa using hy.2
        · show (X \ R).card = k - T.card
          have := Finset.card_sdiff_add_card_inter X R
          rw [hX.2, hX.1] at this
          omega
      · intro X hX Y hY hXY
        simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_ofPred_eq] at hX hY
        have e1 := Finset.sdiff_union_inter X R
        have e2 := Finset.sdiff_union_inter Y R
        simp only at hXY
        rw [hX.2] at e1
        rw [hY.2] at e2
        rw [← e1, ← e2, hXY]
    simpa [Finset.card_powersetCard, Finset.card_compl] using key
  · apply le_of_eq
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro X hX hXT
    rw [mem_powersetCard] at hX
    have : (X ∩ R).card ≤ X.card := Finset.card_le_card Finset.inter_subset_left
    rw [hXT, hX.2] at this
    omega

lemma middle_bound {t k : Nat} {ι : Type} (I : Finset ι) (P N : ι → Finset (Fin t))
    (R : Finset (Fin t)) (y0 : Fin t) (hy0 : y0 ∈ R)
    (hP : ∀ i ∈ I, (P i).card = k) (hN : ∀ i ∈ I, (N i).card = k)
    (hPy : ∀ i ∈ I, y0 ∈ P i)
    (hcompl : ∀ i ∈ I, N i ∩ R = R \ (P i ∩ R))
    (hPinj : Set.InjOn P I) (hNinj : Set.InjOn N I) :
    I.card ≤ ∑ m ∈ range R.card, Nat.choose (R.card - 1) m *
      min (cb (t - R.card) k (m + 1)) (cb (t - R.card) k (R.card - 1 - m)) := by
  classical
  have hmaps : (I : Set ι).MapsTo (fun i => (P i ∩ R).erase y0) (R.erase y0).powerset := by
    intro i _
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
    exact Finset.erase_subset_erase _ Finset.inter_subset_right
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hg : ∀ T ∈ (R.erase y0).powerset,
      (I.filter (fun i => (P i ∩ R).erase y0 = T)).card ≤
        min (cb (t - R.card) k (T.card + 1)) (cb (t - R.card) k (R.card - 1 - T.card)) := by
    intro T hT
    rw [mem_powerset] at hT
    have hy0T : y0 ∉ T := fun h => by simpa using hT h
    have hTR : insert y0 T ⊆ R := by
      intro y hy
      rw [mem_insert] at hy
      rcases hy with rfl | hy
      · exact hy0
      · exact Finset.mem_of_mem_erase (hT hy)
    have hPR : ∀ i ∈ I.filter (fun i => (P i ∩ R).erase y0 = T), P i ∩ R = insert y0 T := by
      intro i hi
      rw [mem_filter] at hi
      rw [← hi.2, Finset.insert_erase]
      exact mem_inter.2 ⟨hPy i hi.1, hy0⟩
    refine le_min ?_ ?_
    · have h1 : (I.filter (fun i => (P i ∩ R).erase y0 = T)).card ≤
          ((univ.powersetCard k).filter (fun X => X ∩ R = insert y0 T)).card := by
        apply Finset.card_le_card_of_injOn P
        · intro i hi
          have hi' := (mem_filter.1 hi).1
          simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_ofPred_eq]
          exact ⟨hP i hi', hPR i hi⟩
        · intro i hi j hj hij
          exact hPinj (mem_filter.1 hi).1 (mem_filter.1 hj).1 hij
      have h2 := card_trace_le k R (insert y0 T)
      rw [Finset.card_insert_of_notMem hy0T] at h2
      omega
    · have h1 : (I.filter (fun i => (P i ∩ R).erase y0 = T)).card ≤
          ((univ.powersetCard k).filter (fun X => X ∩ R = R \ insert y0 T)).card := by
        apply Finset.card_le_card_of_injOn N
        · intro i hi
          have hi' := (mem_filter.1 hi).1
          simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_ofPred_eq]
          refine ⟨hN i hi', ?_⟩
          rw [hcompl i hi', hPR i hi]
        · intro i hi j hj hij
          exact hNinj (mem_filter.1 hi).1 (mem_filter.1 hj).1 hij
      have h2 := card_trace_le k R (R \ insert y0 T)
      rw [Finset.card_sdiff_of_subset hTR, Finset.card_insert_of_notMem hy0T] at h2
      have e : R.card - (T.card + 1) = R.card - 1 - T.card := by omega
      rw [e] at h2
      omega
  refine (Finset.sum_le_sum hg).trans (le_of_eq ?_)
  rw [Finset.sum_powerset_apply_card
    (fun c => min (cb (t - R.card) k (c + 1)) (cb (t - R.card) k (R.card - 1 - c)))]
  have hc : (R.erase y0).card + 1 = R.card := Finset.card_erase_add_one hy0
  rw [hc, Finset.card_erase_of_mem hy0]
  simp only [smul_eq_mul]

lemma cbig (n : Nat) (hn : 5 ≤ n) : (n + 1) * (4 * n + 2) ≤ Nat.centralBinom n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have : (n + 1) * ((n + 1 + 1) * (4 * (n + 1) + 2)) ≤ (n + 1) * Nat.centralBinom (n + 1) := by
      rw [h]
      have : (n + 1 + 1) * (4 * (n + 1) + 2) ≤ (4 * n + 2) * (4 * n + 2) := by nlinarith
      calc (n + 1) * ((n + 1 + 1) * (4 * (n + 1) + 2))
          ≤ (n + 1) * ((4 * n + 2) * (4 * n + 2)) := Nat.mul_le_mul_left _ this
        _ = 2 * (2 * n + 1) * ((n + 1) * (4 * n + 2)) := by ring
        _ ≤ 2 * (2 * n + 1) * Nat.centralBinom n := Nat.mul_le_mul_left _ ih
    exact Nat.le_of_mul_le_mul_left this (by omega)

lemma num_big (k : Nat) (hk : 5 ≤ k) :
    2 * (Nat.choose (2 * k) (k - 1) + (2 * k + 1)) ≤ Nat.choose (2 * k + 1) k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e1 : Nat.choose (2 * (j + 1) + 1) (j + 1) =
      Nat.choose (2 * (j + 1)) j + Nat.choose (2 * (j + 1)) (j + 1) := Nat.choose_succ_succ' _ _
  have e2 := Nat.choose_succ_right_eq (2 * (j + 1)) j
  have e3 : 2 * (j + 1) - j = j + 2 := by omega
  rw [e3] at e2
  have hc := cbig (j + 1) hk
  rw [Nat.centralBinom] at hc
  simp only [Nat.add_sub_cancel]
  rw [e1]
  set a := Nat.choose (2 * (j + 1)) j
  set b := Nat.choose (2 * (j + 1)) (j + 1)
  nlinarith

def S (t k r : Nat) : Nat := ∑ m ∈ range r, Nat.choose (r - 1) m *
      min (cb (t - r) k (m + 1)) (cb (t - r) k (r - 1 - m))

lemma num_small (k q : Nat) (hk : k = 3 ∨ k = 4) (hq : q ≤ 2 * k + 1) :
    S (2 * k + 1) k q + q ≤ Nat.choose (2 * k + 1) k / 2 := by
  rcases hk with rfl | rfl
  · interval_cases q <;> decide
  · interval_cases q <;> decide

end PEqualNP.Outside.L_lib_1488

theorem PEqualNP.Outside.L_lib_1488 : ∀ (k m : Nat), 3 ≤ k →
  let t := 2*k+1
  (∃ f : Fin m × Bool → Finset (Fin t),
    Function.Injective f ∧ (∀ a, (f a).Nonempty) ∧
    (∀ i, Disjoint (f (i,false)) (f (i,true)) ∧
      f (i,false) ∪ f (i,true) ≠ Finset.univ) ∧
    ∀ a i, let u := f (i,false) ∪ f (i,true)
      f a ≠ u ∧ f a ≠ Finset.univ \ u) →
  m ≤ (∑ j ∈ Finset.Ico 2 k, Nat.choose t j) + Nat.choose t k/2 := by
  intro k m hk
  dsimp only
  rintro ⟨f, hinj, hne, hpair, hforb⟩
  classical

  have hfst : ∀ i j b b', f (i, b) = f (j, b') → i = j := fun i j b b' h =>
    congrArg Prod.fst (hinj h)
  let Q : Finset (Fin (2 * k + 1)) :=
    Finset.univ.filter (fun x => ∀ i, f (i, false) ∪ f (i, true) ≠ Finset.univ \ {x})
  have hsingQ : ∀ a y, f a = {y} → y ∈ Q := by
    intro a y hy
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hU
    apply (hforb a i).2
    rw [hU, hy]
    ext z
    simp
  let small := (Finset.univ : Finset (Fin m)).filter
    (fun i => (f (i, false)).card < k ∨ (f (i, true)).card < k)
  let mid := (Finset.univ : Finset (Fin m)).filter
    (fun i => ¬ ((f (i, false)).card < k ∨ (f (i, true)).card < k))
  have hm : small.card + mid.card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => (f (i, false)).card < k ∨ (f (i, true)).card < k)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this

  have hsmall : small.card ≤ (∑ j ∈ Finset.Ico 2 k, Nat.choose (2 * k + 1) j) + Q.card := by
    let g : Fin m → Finset (Fin (2 * k + 1)) :=
      fun i => if (f (i, false)).card < k then f (i, false) else f (i, true)
    have hg : ∀ i, ∃ b, g i = f (i, b) := by
      intro i
      by_cases h : (f (i, false)).card < k
      · exact ⟨false, by simp [g, h]⟩
      · exact ⟨true, by simp [g, h]⟩
    have h1 : small.card ≤ (((Finset.Ico 2 k).biUnion
        (fun j => (Finset.univ : Finset (Fin (2 * k + 1))).powersetCard j)) ∪
        Q.image (fun y => ({y} : Finset (Fin (2 * k + 1))))).card := by
      apply Finset.card_le_card_of_injOn g
      · intro i hi
        simp only [small, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
        have hlt : (g i).card < k := by
          by_cases h : (f (i, false)).card < k
          · simp [g, h]
          · simp only [g, h, ite_false]
            tauto
        obtain ⟨b, hb⟩ := hg i
        have hpos : 0 < (g i).card := by
          rw [hb]
          exact Finset.card_pos.2 (hne _)
        rw [Finset.mem_coe]
        by_cases h2 : 2 ≤ (g i).card
        · apply Finset.mem_union_left
          rw [Finset.mem_biUnion]
          exact ⟨(g i).card, Finset.mem_Ico.2 ⟨h2, hlt⟩,
            Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
        · apply Finset.mem_union_right
          obtain ⟨y, hy⟩ := Finset.card_eq_one.1 (show (g i).card = 1 by omega)
          rw [Finset.mem_image]
          exact ⟨y, hsingQ (i, b) y (hb ▸ hy), hy.symm⟩
      · intro i _ j _ hij
        obtain ⟨b, hb⟩ := hg i
        obtain ⟨b', hb'⟩ := hg j
        exact hfst i j b b' (hb ▸ hb' ▸ hij)
    refine h1.trans ((Finset.card_union_le _ _).trans (Nat.add_le_add ?_ Finset.card_image_le))
    refine (Finset.card_biUnion_le).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro j _
    simp [Finset.card_powersetCard]

  have hmidf : ∀ i ∈ mid, (f (i, false)).card = k ∧ (f (i, true)).card = k ∧
      ∀ y ∈ Q, y ∈ f (i, false) ∪ f (i, true) := by
    intro i hi
    simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_lt] at hi
    have hcu := Finset.card_union_of_disjoint (hpair i).1
    have hlt := (Finset.card_lt_iff_ne_univ _).2 (hpair i).2
    rw [Fintype.card_fin] at hlt
    refine ⟨by omega, by omega, ?_⟩
    have hc1 : (Finset.univ \ (f (i, false) ∪ f (i, true))).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hc1
    have hU : f (i, false) ∪ f (i, true) = Finset.univ \ {x} := by
      rw [← hx]
      ext z
      simp
    intro y hy
    have hxy : y ≠ x := by
      rintro rfl
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hy i hU
    rw [hU]
    simp [hxy]
  by_cases hq : Q.card = 0
  · have h2 : mid.card * 2 ≤ Nat.choose (2 * k + 1) k := by
      have h1 : (mid ×ˢ (Finset.univ : Finset Bool)).card ≤
          ((Finset.univ : Finset (Fin (2 * k + 1))).powersetCard k).card := by
        apply Finset.card_le_card_of_injOn f
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_product] at hp
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨Finset.subset_univ _, ?_⟩
          obtain ⟨i, b⟩ := p
          have := hmidf i hp.1
          cases b
          · exact this.1
          · exact this.2.1
        · intro p _ p' _ h
          exact hinj h
      simpa [Finset.card_product, Finset.card_powersetCard] using h1
    omega
  · obtain ⟨y0, hy0⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hq)
    let R : Finset (Fin (2 * k + 1)) := if k ≤ 4 then Q else {y0}
    have hRQ : R ⊆ Q := by
      by_cases h : k ≤ 4
      · simp [R, h]
      · simp [R, h, hy0]
    have hy0R : y0 ∈ R := by
      by_cases h : k ≤ 4
      · simp [R, h, hy0]
      · simp [R, h]
    let P : Fin m → Finset (Fin (2 * k + 1)) :=
      fun i => if y0 ∈ f (i, false) then f (i, false) else f (i, true)
    let N : Fin m → Finset (Fin (2 * k + 1)) :=
      fun i => if y0 ∈ f (i, false) then f (i, true) else f (i, false)
    have hPb : ∀ i, ∃ b, P i = f (i, b) := by
      intro i
      by_cases h : y0 ∈ f (i, false)
      · exact ⟨false, by simp [P, h]⟩
      · exact ⟨true, by simp [P, h]⟩
    have hNb : ∀ i, ∃ b, N i = f (i, b) := by
      intro i
      by_cases h : y0 ∈ f (i, false)
      · exact ⟨true, by simp [N, h]⟩
      · exact ⟨false, by simp [N, h]⟩
    have hcardb : ∀ i ∈ mid, ∀ b, (f (i, b)).card = k := by
      intro i hi b
      cases b
      · exact (hmidf i hi).1
      · exact (hmidf i hi).2.1
    have hmb := L_lib_1488.middle_bound mid P N R y0 hy0R
      (fun i hi => by obtain ⟨b, hb⟩ := hPb i; rw [hb]; exact hcardb i hi b)
      (fun i hi => by obtain ⟨b, hb⟩ := hNb i; rw [hb]; exact hcardb i hi b)
      (by
        intro i hi
        have := (hmidf i hi).2.2 y0 hy0
        rw [Finset.mem_union] at this
        by_cases h : y0 ∈ f (i, false)
        · simp [P, h]
        · simp only [P, h, ite_false]
          tauto)
      (by
        intro i hi
        have hd := Finset.disjoint_left.1 (hpair i).1
        ext y
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        by_cases hyR : y ∈ R
        · have hyU := (hmidf i hi).2.2 y (hRQ hyR)
          rw [Finset.mem_union] at hyU
          have hd' := @hd y
          by_cases h : y0 ∈ f (i, false)
          · simp only [P, N, h, ite_true]
            tauto
          · simp only [P, N, h, ite_false]
            tauto
        · simp [hyR])
      (by
        intro i _ j _ hij
        obtain ⟨b, hb⟩ := hPb i
        obtain ⟨b', hb'⟩ := hPb j
        exact hfst i j b b' (hb ▸ hb' ▸ hij))
      (by
        intro i _ j _ hij
        obtain ⟨b, hb⟩ := hNb i
        obtain ⟨b', hb'⟩ := hNb j
        exact hfst i j b b' (hb ▸ hb' ▸ hij))
    have hQle : Q.card ≤ 2 * k + 1 := by
      simpa using Finset.card_le_univ Q
    have hfin : mid.card + Q.card ≤ Nat.choose (2 * k + 1) k / 2 := by
      by_cases h : k ≤ 4
      · have hR : R = Q := by simp [R, h]
        rw [hR] at hmb
        have := L_lib_1488.num_small k Q.card (by omega) hQle
        unfold L_lib_1488.S at this
        omega
      · have hR : R = {y0} := by simp [R, h]
        rw [hR] at hmb
        simp only [Finset.card_singleton, Finset.range_one, Finset.sum_singleton,
          Nat.choose_self, one_mul] at hmb
        have h1 : mid.card ≤ Nat.choose (2 * k) (k - 1) := by
          refine hmb.trans ((min_le_left _ _).trans ?_)
          simp only [L_lib_1488.cb, show 1 ≤ k by omega, ite_true]
          have : 2 * k + 1 - 1 = 2 * k := by omega
          rw [this]
        have := L_lib_1488.num_big k (by omega)
        omega
    omega
