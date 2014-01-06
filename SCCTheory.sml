structure SCCTheory :> SCCTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading SCCTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open listTheory
  in end;
  val _ = Theory.link_parents
          ("SCC",Arbnum.fromString "1388969806",Arbnum.fromString "979943")
          [("list",
           Arbnum.fromString "1378778539",
           Arbnum.fromString "899441")];
  val _ = Theory.incorporate_types "SCC" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("min", "bool"), ID("bool", "!"), ID("bool", "/\\"),
   ID("min", "="), ID("min", "==>"), ID("bool", "?"),
   ID("pred_set", "DISJOINT"), ID("pred_set", "EMPTY"), ID("bool", "IN"),
   ID("SCC", "SCC"), ID("relation", "TC"), ID("bool", "\\/"),
   ID("SCC", "lift"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYV "'b", TYOP [0, 1, 0], TYOP [0, 2, 0], TYV "'a",
   TYOP [0, 4, 0], TYOP [0, 5, 3], TYOP [0, 4, 2], TYOP [0, 7, 6],
   TYOP [0, 5, 0], TYOP [0, 4, 5], TYOP [0, 10, 9], TYOP [0, 9, 0],
   TYOP [0, 10, 0], TYOP [0, 13, 0], TYOP [0, 7, 0], TYOP [0, 15, 0],
   TYOP [0, 3, 0], TYOP [0, 0, 0], TYOP [0, 0, 18], TYOP [0, 5, 9],
   TYOP [0, 4, 9], TYOP [0, 1, 3], TYOP [0, 10, 10], TYOP [0, 20, 20],
   TYOP [0, 10, 20]]
  end
  val _ = Theory.incorporate_consts "SCC" tyvector
     [("lift", 8), ("SCC", 11)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("R", 10), TMV("R", 7), TMV("v", 4), TMV("v'", 4), TMV("v'", 1),
   TMV("vs", 5), TMV("vs'", 5), TMV("vs'", 2), TMC(2, 9), TMC(2, 12),
   TMC(2, 14), TMC(2, 16), TMC(2, 17), TMC(3, 19), TMC(4, 19), TMC(4, 20),
   TMC(5, 19), TMC(6, 9), TMC(6, 3), TMC(7, 20), TMC(8, 5), TMC(9, 21),
   TMC(9, 22), TMC(10, 11), TMC(11, 23), TMC(11, 24), TMC(12, 19),
   TMC(13, 25), TMC(13, 8), TMC(14, 18)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op SCC_def =
    DT([],
       [read"(%10 (|%0. (%9 (|%5. ((%14 ((%23 $1) $0)) ((%13 (%8 (|%2. (%8 (|%3. ((%16 ((%13 ((%21 $1) $2)) ((%21 $0) $2))) ((%13 (((%24 $3) $1) $0)) (((%24 $3) $0) $1)))))))) ((%13 (%8 (|%2. (%8 (|%3. ((%16 ((%13 ((%21 $1) $2)) (%29 ((%21 $0) $2)))) ((%26 (%29 (((%24 $3) $1) $0))) (%29 (((%24 $3) $0) $1))))))))) (%29 ((%15 $0) %20)))))))))"])
  val op lift_def =
    DT([],
       [read"(%11 (|%1. (%9 (|%5. (%12 (|%7. ((%14 (((%28 $2) $1) $0)) (%17 (|%2. (%18 (|%4. ((%16 ((%13 ((%21 $1) $3)) ((%22 $0) $2))) (($4 $1) $0)))))))))))))"])
  val op scc_disjoint_lemma =
    DT(["DISK_THM"],
       [read"(%10 (|%0. (%9 (|%5. (%9 (|%6. ((%16 ((%13 ((%23 $2) $1)) ((%13 ((%23 $2) $0)) (%29 ((%15 $1) $0))))) ((%19 $1) $0))))))))"])
  val op scc_tc_inclusion =
    DT(["cheat"],
       [read"(%10 (|%0. (%9 (|%5. (%8 (|%2. (%8 (|%3. ((%16 ((%13 ((%21 $1) $2)) ((%13 ((%21 $0) $2)) ((%23 $3) $2)))) (((%24 (|%2. (|%3. ((%13 (($5 $1) $0)) ((%13 ((%21 $1) $4)) ((%21 $0) $4)))))) $1) $0))))))))))"])
  val op SCC_loop_contradict =
    DT(["cheat"],
       [read"(%10 (|%0. (%9 (|%5. (%9 (|%6. ((%16 ((%13 (((%25 (%27 $2)) $1) $0)) (((%25 (%27 $2)) $0) $1))) ((%13 (%29 ((%23 $2) $1))) (%29 ((%23 $2) $0))))))))))"])
  end
  val _ = DB.bindl "SCC"
  [("SCC_def",SCC_def,DB.Def), ("lift_def",lift_def,DB.Def),
   ("scc_disjoint_lemma",scc_disjoint_lemma,DB.Thm),
   ("scc_tc_inclusion",scc_tc_inclusion,DB.Thm),
   ("SCC_loop_contradict",SCC_loop_contradict,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("listTheory.list_grammars",
                          listTheory.list_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("SCC", (Term.prim_mk_const { Name = "SCC", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("SCC", (Term.prim_mk_const { Name = "SCC", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lift", (Term.prim_mk_const { Name = "lift", Thy = "SCC"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lift", (Term.prim_mk_const { Name = "lift", Thy = "SCC"}))
  val SCC_grammars = Parse.current_lgrms()
  end
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "SCC", thydataty = "compute", data = "SCC.SCC_def SCC.lift_def"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "SCC"
end
