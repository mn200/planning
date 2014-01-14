open HolKernel Parse boolLib bossLib;

open lcsymtacs
val _ = new_theory "utils";

val twosorted_list_length = store_thm(
  "twosorted_list_length",
  ``!P1 P2 l k1 k2.
      (∀x. MEM x l ⇒ (~P1 x <=> P2 x)) ∧ LENGTH (FILTER P1 l) < k1 ∧
      (∀l'. (?pfx sfx. pfx ++ l' ++ sfx = l) /\ (∀x. MEM x l' ⇒ P2 x) ⇒ LENGTH l' < k2)
     ==>
      LENGTH l < k1 * k2``,
  NTAC 3 GEN_TAC >> Induct_on `FILTER P1 l`
  >- (simp[listTheory.FILTER_EQ_NIL] >> rpt strip_tac >>
      fs[listTheory.EVERY_MEM] >>
      first_x_assum (qspec_then `l` mp_tac) >> strip_tac >>
      `LENGTH l < k2` suffices_by
        (`k2 ≤ k1 * k2` by simp[] >> decide_tac) >>
      first_x_assum match_mp_tac >> simp[] >>
      rpt (qexists_tac `[]`) >> simp[]) >>
  map_every qx_gen_tac [`h`, `P1`, `l`] >>
  simp[listTheory.FILTER_EQ_CONS] >>
  disch_then (qx_choosel_then [`pfx`, `sfx`] strip_assume_tac) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, listTheory.FILTER_APPEND_DISTRIB] >>
  map_every qx_gen_tac [`k1`, `k2`] >> rpt strip_tac >> fs[] >>
  first_x_assum (qspecl_then [`P1`, `sfx`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`k1 - 1`, `k2`] mp_tac) >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.LEFT_SUB_DISTRIB] >>
  strip_tac >>
  `LENGTH pfx < k2`
    by (first_x_assum match_mp_tac >>
        fs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
        map_every qexists_tac [`[]`, `h::sfx`] >> simp[]) >>
  `LENGTH sfx < k1 * k2 - k2` suffices_by decide_tac >>
  first_x_assum match_mp_tac >> qx_gen_tac `ll` >>
  disch_then
    (CONJUNCTS_THEN2 (qx_choosel_then [`pp`, `ss`] (SUBST_ALL_TAC o SYM))
                     assume_tac) >>
  first_x_assum match_mp_tac >> simp[] >>
  map_every qexists_tac [`pfx ++ [h] ++ pp`, `ss`] >> simp[])

val _ = export_theory();
