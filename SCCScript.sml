open HolKernel Parse boolLib bossLib;
open pred_setTheory;
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


val _ = export_theory();

