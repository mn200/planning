structure sublistTheory :> sublistTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading sublistTheory ... " else ()
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
          ("sublist",
          Arbnum.fromString "1389312277",
          Arbnum.fromString "459717")
          [("list",
           Arbnum.fromString "1378778539",
           Arbnum.fromString "899441")];
  val _ = Theory.incorporate_types "sublist" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("min", "bool"), ID("pair", "prod"),
   ID("list", "list"), ID("bool", "!"), ID("pair", ","), ID("bool", "/\\"),
   ID("arithmetic", "<="), ID("num", "num"), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("min", "@"), ID("list", "APPEND"),
   ID("list", "CONS"), ID("list", "EVERY"), ID("bool", "F"),
   ID("list", "FILTER"), ID("combin", "I"), ID("bool", "IN"),
   ID("list", "LENGTH"), ID("list", "LIST_TO_SET"), ID("list", "NIL"),
   ID("pred_set", "SUBSET"), ID("bool", "T"), ID("relation", "WF"),
   ID("relation", "WFREC"), ID("bool", "\\/"), ID("list", "list_CASE"),
   ID("pair", "pair_CASE"), ID("sublist", "sublist"),
   ID("sublist", "sublist_tupled"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYV "'a", TYOP [3, 1], TYOP [2, 2, 2], TYOP [0, 3, 0],
   TYOP [0, 2, 0], TYOP [0, 2, 5], TYOP [0, 1, 0], TYOP [0, 3, 4],
   TYV "'b", TYOP [3, 9], TYOP [0, 7, 0], TYOP [0, 11, 0], TYOP [0, 6, 0],
   TYOP [0, 13, 0], TYOP [0, 5, 0], TYOP [0, 2, 3], TYOP [0, 2, 16],
   TYOP [0, 0, 0], TYOP [0, 0, 18], TYOP [8], TYOP [0, 20, 0],
   TYOP [0, 20, 21], TYOP [0, 1, 7], TYOP [0, 4, 0], TYOP [0, 4, 24],
   TYOP [0, 8, 0], TYOP [0, 26, 8], TYOP [0, 2, 2], TYOP [0, 2, 28],
   TYOP [0, 1, 28], TYOP [0, 10, 10], TYOP [0, 9, 31], TYOP [0, 7, 5],
   TYOP [0, 7, 28], TYOP [0, 1, 11], TYOP [0, 2, 20], TYOP [0, 2, 7],
   TYOP [0, 7, 11], TYOP [0, 4, 4], TYOP [0, 39, 4], TYOP [0, 8, 40],
   TYOP [0, 1, 5], TYOP [0, 42, 0], TYOP [0, 0, 43], TYOP [0, 2, 44],
   TYOP [0, 3, 13], TYOP [0, 10, 0], TYOP [0, 10, 47]]
  end
  val _ = Theory.incorporate_consts "sublist" tyvector
     [("sublist_tupled", 4), ("sublist", 6)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("P", 7), TMV("P", 6), TMV("R", 8), TMV("a", 2), TMV("a", 3),
   TMV("b", 2), TMV("c", 2), TMV("d", 2), TMV("h", 1), TMV("h", 9),
   TMV("l", 2), TMV("l'", 2), TMV("l1", 2), TMV("l1'", 2), TMV("l2", 2),
   TMV("l2'", 2), TMV("l2a", 2), TMV("l2b", 2), TMV("l3", 2), TMV("l4", 2),
   TMV("sublist_tupled", 4), TMV("t", 2), TMV("t", 10), TMV("v", 2),
   TMV("v1", 2), TMV("x", 1), TMV("x", 2), TMV("x1", 2), TMV("y", 1),
   TMC(4, 11), TMC(4, 12), TMC(4, 14), TMC(4, 15), TMC(5, 17), TMC(6, 19),
   TMC(7, 22), TMC(9, 23), TMC(9, 19), TMC(9, 25), TMC(9, 6), TMC(9, 22),
   TMC(10, 19), TMC(11, 15), TMC(12, 27), TMC(13, 29), TMC(14, 30),
   TMC(14, 32), TMC(15, 33), TMC(16, 0), TMC(17, 34), TMC(18, 18),
   TMC(19, 35), TMC(20, 36), TMC(21, 37), TMC(22, 2), TMC(22, 10),
   TMC(23, 38), TMC(24, 0), TMC(25, 26), TMC(26, 41), TMC(27, 19),
   TMC(28, 45), TMC(29, 46), TMC(30, 6), TMC(30, 48), TMC(31, 4),
   TMC(32, 18)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  val op sublist_tupled_primitive_def =
    DT([],
       [read"((%38 %65) ((%59 (%43 (|%2. ((%34 (%58 $0)) ((%34 (%29 (|%28. (%29 (|%25. (%32 (|%14. (%32 (|%12. (($4 ((%33 $0) $1)) ((%33 ((%45 $2) $0)) ((%45 $3) $1)))))))))))) (%29 (|%28. (%32 (|%14. (%32 (|%12. (%29 (|%25. (($4 ((%33 ((%45 $0) $1)) $2)) ((%33 ((%45 $0) $1)) ((%45 $3) $2)))))))))))))))) (|%20. (|%4. ((%62 $0) (|%23. (|%12. (((%61 $1) (%50 %57)) (|%8. (|%21. (((%61 $2) (%50 %48)) (|%28. (|%14. (%50 ((%60 ((%34 ((%36 $3) $1)) ($7 ((%33 $2) $0)))) ($7 ((%33 ((%45 $3) $2)) $0)))))))))))))))))"])
  val op sublist_curried_def =
    DT([],
       [read"(%32 (|%26. (%32 (|%27. ((%37 ((%63 $1) $0)) (%65 ((%33 $1) $0)))))))"])
  val op sublist_every =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%30 (|%0. ((%41 ((%34 ((%63 $2) $1)) ((%47 $0) $1))) ((%47 $0) $2))))))))"])
  val op sublist_cons_2 =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%29 (|%8. ((%37 ((%63 ((%45 $0) $2)) ((%45 $0) $1))) ((%63 $2) $1))))))))"])
  val op sublist_cons_3 =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. ((%41 ((%63 ((%45 %8) $1)) $0)) ((%63 $1) $0))))))"])
  val op sublist_filter =
    DT(["DISK_THM"],
       [read"(%32 (|%10. (%30 (|%0. ((%63 ((%49 $0) $1)) $1)))))"])
  val op sublist_subset =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. ((%41 ((%63 $1) $0)) ((%56 (%53 $1)) (%53 $0)))))))"])
  val op append_sublist =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%32 (|%18. (%32 (|%10. ((%41 ((%63 ((%44 ((%44 $3) $2)) $1)) $0)) ((%63 ((%44 $3) $1)) $0))))))))))"])
  val op sublist_append_2 =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%32 (|%18. ((%41 ((%63 $2) $1)) ((%63 $2) ((%44 $1) $0)))))))))"])
  val op sublist_append =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%13. (%32 (|%14. (%32 (|%15. ((%41 ((%34 ((%63 $3) $2)) ((%63 $1) $0))) ((%63 ((%44 $3) $1)) ((%44 $2) $0)))))))))))"])
  val op sublist_append_both_I =
    DT(["DISK_THM"],
       [read"((%41 ((%34 ((%63 %3) %5)) ((%63 %6) %7))) ((%63 ((%44 %3) %6)) ((%44 %5) %7)))"])
  val op sublist_SING_MEM =
    DT(["DISK_THM"],
       [read"((%37 ((%63 ((%45 %8) %54)) %10)) ((%51 %8) (%53 %10)))"])
  val op sublist_ind =
    DT(["DISK_THM"],
       [read"(%31 (|%1. ((%41 ((%34 (%32 (|%12. (($1 %54) $0)))) ((%34 (%29 (|%8. (%32 (|%21. (($2 ((%45 $1) $0)) %54)))))) (%29 (|%25. (%32 (|%12. (%29 (|%28. (%32 (|%14. ((%41 ((%34 (($4 $2) $0)) (($4 ((%45 $3) $2)) $0))) (($4 ((%45 $3) $2)) ((%45 $1) $0)))))))))))))) (%32 (|%23. (%32 (|%24. (($2 $1) $0))))))))"])
  val op sublist_def =
    DT(["DISK_THM"],
       [read"((%34 (%32 (|%12. ((%37 ((%63 %54) $0)) %57)))) ((%34 (%32 (|%21. (%29 (|%8. ((%37 ((%63 ((%45 $0) $1)) %54)) %48)))))) (%29 (|%28. (%29 (|%25. (%32 (|%14. (%32 (|%12. ((%37 ((%63 ((%45 $2) $0)) ((%45 $3) $1))) ((%60 ((%34 ((%36 $2) $3)) ((%63 $0) $1))) ((%63 ((%45 $2) $0)) $1)))))))))))))"])
  val op sublist_EQNS =
    DT(["DISK_THM"],
       [read"((%34 ((%37 ((%63 %54) %10)) %57)) ((%37 ((%64 ((%46 %9) %22)) %55)) %48))"])
  val op sublist_refl =
    DT(["DISK_THM"], [read"(%32 (|%10. ((%63 $0) $0)))"])
  val op sublist_cons =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%29 (|%8. ((%41 ((%63 $2) $1)) ((%63 $2) ((%45 $0) $1)))))))))"])
  val op sublist_NIL =
    DT(["DISK_THM"], [read"((%37 ((%63 %12) %54)) ((%39 %12) %54))"])
  val op sublist_trans =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%32 (|%18. ((%41 ((%34 ((%63 $2) $1)) ((%63 $1) $0))) ((%63 $2) $0))))))))"])
  val op sublist_length =
    DT(["DISK_THM"],
       [read"(%32 (|%10. (%32 (|%11. ((%41 ((%63 $1) $0)) ((%35 (%52 $1)) (%52 $0)))))))"])
  val op sublist_CONS1_E =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. ((%41 ((%63 ((%45 %8) $1)) $0)) ((%63 $1) $0))))))"])
  val op sublist_equal_lengths =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. ((%41 ((%34 ((%63 $1) $0)) ((%40 (%52 $1)) (%52 $0)))) ((%39 $1) $0))))))"])
  val op sublist_antisym =
    DT(["DISK_THM"],
       [read"((%41 ((%34 ((%63 %12) %14)) ((%63 %14) %12))) ((%39 %12) %14))"])
  val op sublist_append_I =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. ((%63 $1) ((%44 $0) $1))))))"])
  val op sublist_snoc =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%29 (|%8. ((%41 ((%63 $2) $1)) ((%63 $2) ((%44 $1) ((%45 $0) %54))))))))))"])
  val op sublist_append_front =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. ((%63 $1) ((%44 $1) $0))))))"])
  val op sublist_append1_E =
    DT(["DISK_THM"],
       [read"((%41 ((%63 ((%44 %12) %14)) %10)) ((%34 ((%63 %12) %10)) ((%63 %14) %10)))"])
  val op append_sublist_1 =
    DT(["DISK_THM"],
       [read"((%41 ((%63 ((%44 %12) %14)) %10)) ((%34 ((%63 %12) %10)) ((%63 %14) %10)))"])
  val op sublist_cons_exists =
    DT(["DISK_THM"],
       [read"(%29 (|%8. (%32 (|%12. (%32 (|%14. ((%37 ((%63 ((%45 $2) $1)) $0)) (%42 (|%16. (%42 (|%17. ((%34 ((%39 $2) ((%44 ((%44 $1) ((%45 $4) %54))) $0))) ((%34 (%66 ((%51 $4) (%53 $1)))) ((%63 $3) $0))))))))))))))"])
  val op sublist_append_exists =
    DT(["DISK_THM"],
       [read"(%32 (|%12. (%32 (|%14. (%29 (|%8. ((%41 ((%63 ((%45 $0) $2)) $1)) (%42 (|%18. (%42 (|%19. ((%34 ((%39 $3) ((%44 ((%44 $1) ((%45 $2) %54))) $0))) ((%63 $4) $0)))))))))))))"])
  val op sublist_append_4 =
    DT(["cheat"],
       [read"(%32 (|%10. (%32 (|%12. (%32 (|%14. (%29 (|%8. ((%41 ((%34 ((%63 ((%45 $0) $3)) ((%44 ((%44 $2) ((%45 $0) %54))) $1))) ((%47 (|%25. (%66 ((%36 $1) $0)))) $2))) ((%63 $3) $1))))))))))"])
  val op sublist_append_5 =
    DT(["cheat"],
       [read"(%32 (|%10. (%32 (|%12. (%32 (|%14. (%29 (|%8. ((%41 ((%34 ((%63 ((%45 $0) $3)) ((%44 $2) $1))) ((%47 (|%25. (%66 ((%36 $1) $0)))) $2))) ((%63 ((%45 $0) $3)) $1))))))))))"])
  end
  val _ = DB.bindl "sublist"
  [("sublist_tupled_primitive_def",sublist_tupled_primitive_def,DB.Def),
   ("sublist_curried_def",sublist_curried_def,DB.Def),
   ("sublist_every",sublist_every,DB.Thm),
   ("sublist_cons_2",sublist_cons_2,DB.Thm),
   ("sublist_cons_3",sublist_cons_3,DB.Thm),
   ("sublist_filter",sublist_filter,DB.Thm),
   ("sublist_subset",sublist_subset,DB.Thm),
   ("append_sublist",append_sublist,DB.Thm),
   ("sublist_append_2",sublist_append_2,DB.Thm),
   ("sublist_append",sublist_append,DB.Thm),
   ("sublist_append_both_I",sublist_append_both_I,DB.Thm),
   ("sublist_SING_MEM",sublist_SING_MEM,DB.Thm),
   ("sublist_ind",sublist_ind,DB.Thm), ("sublist_def",sublist_def,DB.Thm),
   ("sublist_EQNS",sublist_EQNS,DB.Thm),
   ("sublist_refl",sublist_refl,DB.Thm),
   ("sublist_cons",sublist_cons,DB.Thm),
   ("sublist_NIL",sublist_NIL,DB.Thm),
   ("sublist_trans",sublist_trans,DB.Thm),
   ("sublist_length",sublist_length,DB.Thm),
   ("sublist_CONS1_E",sublist_CONS1_E,DB.Thm),
   ("sublist_equal_lengths",sublist_equal_lengths,DB.Thm),
   ("sublist_antisym",sublist_antisym,DB.Thm),
   ("sublist_append_I",sublist_append_I,DB.Thm),
   ("sublist_snoc",sublist_snoc,DB.Thm),
   ("sublist_append_front",sublist_append_front,DB.Thm),
   ("sublist_append1_E",sublist_append1_E,DB.Thm),
   ("append_sublist_1",append_sublist_1,DB.Thm),
   ("sublist_cons_exists",sublist_cons_exists,DB.Thm),
   ("sublist_append_exists",sublist_append_exists,DB.Thm),
   ("sublist_append_4",sublist_append_4,DB.Thm),
   ("sublist_append_5",sublist_append_5,DB.Thm)]

  local open Portable GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("listTheory.list_grammars",
                          listTheory.list_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sublist_tupled", (Term.prim_mk_const { Name = "sublist_tupled", Thy = "sublist"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sublist_tupled", (Term.prim_mk_const { Name = "sublist_tupled", Thy = "sublist"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sublist", (Term.prim_mk_const { Name = "sublist", Thy = "sublist"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("sublist", (Term.prim_mk_const { Name = "sublist", Thy = "sublist"}))
  val sublist_grammars = Parse.current_lgrms()
  end
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "sublist", thydataty = "compute", data = "sublist.sublist_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "sublist",
    thydataty = "BasicProvers.stateful_simpset",
    data =
        "sublist.sublist_EQNS sublist.sublist_NIL sublist.sublist_SING_MEM sublist.sublist_def sublist.sublist_refl"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "sublist"
end
