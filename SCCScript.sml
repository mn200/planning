open HolKernel Parse boolLib bossLib;
open pred_setTheory;
open relationTheory;
val _ = new_theory "SCC";



val SCC_def = Define`SCC R vs <=> (!v v'. v IN vs /\ v' IN vs ==> R^+ v v' /\ R^+ v' v)
                                  /\ (!v v'. v IN vs /\ ~(v' IN vs) ==> ~(R^+ v v') \/ ~(R^+ v' v))
                                  /\ ~(vs = EMPTY)`

(* A function to lift a relation ('a -> 'a -> bool) to (('a -> bool) -> ('a -> bool) -> bool), i.e
yeilds a relation between sets of objects. *)
val lift_def = Define`lift R vs vs' <=> ?v v'. v IN vs /\ v' IN vs' ==> R v v'`


val scc_disjoint_lemma = store_thm("scc_disjoint_lemma",
``!R vs vs'. SCC R vs /\ SCC R vs' /\ ~(vs = vs') ==> DISJOINT vs vs'``,
SRW_TAC[][] 
THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
THEN FULL_SIMP_TAC(srw_ss()) [DISJOINT_DEF, INTER_DEF, GSPEC_ETA, GSYM MEMBER_NOT_EMPTY]
THEN FULL_SIMP_TAC(bool_ss)[SCC_def]
THEN `?v. v IN vs /\ ~(v IN vs')` by (FULL_SIMP_TAC(bool_ss)[EXTENSION, IN_DEF] THEN METIS_TAC[])
THEN METIS_TAC[])



val scc_tc_inclusion = store_thm("scc_tc_inclusion",
``!R vs v v'. v IN vs /\ v' IN vs/\ SCC R vs 
              ==> (\v v'. R v v' /\ v IN vs /\ v' IN vs)^+ v v'``,

cheat
(* 
TC_INDUCT_TAC(* check tc_cases1 proof for reference on how to use it*)
REWRITE_TAC[SCC_def]
THEN SRW_TAC[][]
THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
THEN FULL_SIMP_TAC(bool_ss)[Once TC_DEF]
THEN FULL_SIMP_TAC(bool_ss)[Once TC_DEF]



THEN `!P. ∀v v'.
        v ∈ vs ∧ v' ∈ vs ⇒
        ((∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
           P v v')` by PROVE_TAC[]

THEN FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[AND_IMP_INTRO] o Q.SPEC `P`)
THEN REPEAT STRIP_TAC
THEN `∀v v'.
             (v ∈ vs ∧ v' ∈ vs) ∧ (∀x y. R x y ⇒ P x y) ⇒
             P v v'` by METIS_TAC[]


THEN Q.PAT_ASSUM `∀x y. (λv v'. R v v' ∧ v ∈ vs ∧ v' ∈ vs) x y ⇒ P x y` (MP_TAC o SIMP_RULE(srw_ss())[])
THEN REPEAT STRIP_TAC
THEN `∀v v'.
        (v ∈ vs ∧ v' ∈ vs) ∧ (∀x y. R x y ⇒ P x y) ⇒
        P v v'` by PROVE_TAC[]
THEN 



THEN FIRST_X_ASSUM MATCH_MP_TAC



THEN LAST_ASSUM (MP_TAC o Q.SPECL[`v`, `v'`] )
THEN STRIP_TAC
THEN Q.PAT_ASSUM `∀v v'.
        v ∈ vs ∧ v' ∉ vs ⇒
        ¬(∀P.
            (∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
            P v v') ∨
        ¬∀P.
           (∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
           P v' v` (MP_TAC o SIMP_RULE(bool_ss)[NOT_FORALL_THM])
THEN REPEAT STRIP_TAC
THEN `R⁺ v v' ∧ R⁺ v' v` by METIS_TAC[]
THEN `∀v'. v' ∉ vs ⇒ ¬R⁺ v v' ∨ ¬R⁺ v' v` by METIS_TAC[]
THEN REWRITE_TAC[SCC_def, TC_DEF]
THEN REPEAT STRIP_TAC
THEN Q.PAT_ASSUM `∀v v'.
             v ∈ vs ∧ v' ∈ vs ⇒
             (∀P.
                (∀x y. R x y ⇒ P x y) ∧
                (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
                P v v') ∧
             ∀P.
               (∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
               P v' v` (MP_TAC o Q.SPECL[`v`, `v'`])
THEN REPEAT STRIP_TAC 
THEN `(∀P.
         (∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
         P v v')` by METIS_TAC[]
THEN 
METIS_TAC[]
THEN ASM_SIMP_TAC(bool_ss)[]
THEN REPEAT STRIP_TAC
SRW_TAC[][]
THEN Q.PAT_ASSUM `R⁺ v v'` (MP_TAC o REWRITE_RULE[TC_DEF])
THEN REPEAT STRIP_TAC
THEN TC_INDUCT *) )


val SCC_loop_contradict = store_thm("SCC_loop_contradict",
``!R vs vs'. (lift R)^+ vs vs' /\ (lift R)^+ vs' vs
             ==> ~(SCC R vs) /\ ~(SCC R vs')``,
cheat)


val _ = export_theory();

