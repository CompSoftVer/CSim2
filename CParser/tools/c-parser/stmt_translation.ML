(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure ASM_Ignore_Hooks = struct

structure Data = Generic_Data
(
  type T = (int * (ProgramAnalysis.asm_stmt_elements -> bool)) list
  val empty = []
  val extend = I
  fun merge data = Ord_List.merge (int_ord o apply2 fst) data
)

fun add_hook hk = Data.map (Ord_List.insert (int_ord o apply2 fst)
    (serial (), hk))

fun ignore' nm = exists (fn (_, f) => f nm) o Data.get

fun ignore_thy nm thy = ignore' nm (Context.Theory thy)
fun ignore nm ctxt = ignore' nm (Context.Proof ctxt)

end

structure stmt_translation =
struct

open ExpressionTranslation TermsTypes Absyn Basics
open ExpressionTyping

val None_event_exp = Const(@{const_name "Option.None"}, Option_eventty)

fun might_raise trap s =
    case snode s of
      While (_, _, b) => might_raise trap b
    | IfStmt(_, s1, s2) => might_raise trap s1 orelse might_raise trap s2
    | Await (_,b) => might_raise trap b
    | Switch(_, cases) =>
        List.exists (List.exists (bi_might_raise trap) o #2) cases
    | Block bis => List.exists (bi_might_raise trap) bis
    | Trap(trap', s) => trap <> trap' andalso might_raise trap s
    | Spec(_, slist, _) => List.exists (might_raise trap) slist
    | Break => trap = BreakT
    | Continue => trap = ContinueT
    | _ => false
and bi_might_raise trap (BI_Stmt s) = might_raise trap s
  | bi_might_raise _ (BI_Decl _) = false

fun type_var_access vsort stty =
   let open CalculateState NameGeneration 
       val globalty = dest_statety1 stty
       val localty = dest_statety2 stty in      
   case vsort of Local _ =>  Const(@{const_name "snd"} , (stty-->localty))
                 | NSGlobal  => Const(@{const_name "fst"} , (stty-->globalty))
                 | _ => raise Fail "var_accessor: shouldn't be called on addressed global"
   end

fun type_var_access_abs vsort stty acc = 
  let open CalculateState NameGeneration     
      val svar = Free("s", stty)      
      val acc' = acc $ ((type_var_access vsort stty) $ (Bound 0))
   in 
        mk_abs(svar, acc')
   end

fun update_state vsort stty upd state =
   let open CalculateState NameGeneration
      val globty = dest_statety1 stty
      val localty = dest_statety2 stty
      val glob = Const(@{const_name "fst"} , (stty-->globty)) $ state
      val loc =  Const(@{const_name "snd"} , (stty-->localty)) $ state      
      val glob' = case vsort of Local _ => glob
                             | NSGlobal => upd $ glob
                             | _ => raise Fail "var_updator: shouldn't be called on addressed global"
      val loc' = case vsort of Local _ => upd $ loc
                             | NSGlobal  => loc
                             | _ => raise Fail "var_updator: shouldn't be called on addressed global"      
   in 
       Const(@{const_name "Product_Type.Pair"}, globty --> localty--> stty) $ glob' $ loc'
   end

fun update_state_abs vsort stty upd  =
   let open CalculateState NameGeneration     
      val t_upd = ((dest_statety1 (type_of upd)))
      val fvar = Free("f", t_upd)
      val svar = Free("s", stty)
      val upd' = upd $ (Bound 1)                  
   in 
        mk_abs(fvar, mk_abs(svar, update_state vsort stty upd' (Bound 0)))
   end


fun var_updator sg globty localty k_upd (name, ty, _(*cty*), vsort) newvalue state = let
  open CalculateState NameGeneration
  val pfx = case vsort of Local _ => local_rcd_name | _ => global_rcd_name
  val fullname =
      Sign.intern_const sg (pfx ^ "." ^ suffix Record.updateN name)
  val statety = type_of state
  val newvalue' = if k_upd then K_rec ty $ newvalue else newvalue
(* David Sanan updates take the field update in the global or local variable and
       it accordingly updates the product representing the state 
       globals do not have to udpate the global field.
       fldupd will be a function receiving an instance of the local or global component 
      (the update of the field being modified *)
  val ret_ty = case vsort of Local _ => localty | _ => globty
  val fldupd = (Const(fullname, (ty --> ty) --> (ret_ty --> ret_ty)) $
               newvalue')      
in  update_state vsort statety fldupd state 
  (* case vsort of    
    DS --prev code -- 
       Local _ => Const(fullname, (ty --> ty) --> (statety --> statety)) $
               newvalue' $ state 
  | (* David Sanan globals do not have to udpate the global field*)
    (* DS --prev code--  
      NSGlobal => let
      val glob_update =
          Sign.intern_const sg (suffix Record.updateN "globals")
      val globupd_t = #upd (get_globals_data statety globty sg)
      val fldupd = Const(fullname, (ty --> ty) --> (globty --> globty))
    in
      globupd_t $ (fldupd $ newvalue') $ state
    end*)
    NSGlobal => let      
      val fldupd = Const(fullname, (ty --> ty) --> (globty --> globty)) $ newvalue'
    in update_state vsort localty globty statety fldupd state      
    end
  | AddressedGlobal => raise Fail "var_updator: shouldn't be called on addressed global"
  | UntouchedGlobal => raise Fail "var_updator: shouldn't be called on untouched global"
 *)
end

fun var_accessor sg globty localty (name, ty, _ (*cty *), vsort) state = let
  open CalculateState NameGeneration
  val (pfx,tyy) = case vsort of Local _ => (local_rcd_name,localty) | _ => (global_rcd_name,globty)
  val access = type_var_access vsort (type_of state)   
  in     
    Const(Sign.intern_const sg (pfx ^ "." ^ name),
                     tyy --> ty) $ (access  $ state)
  (* David Sanan similarly to updators, accessors need to access the global or local
    component from the product state. The global component does not need an additional field access*)
  (* DS -- Prev Code 
   case vsort of
    Local _ => Const(Sign.intern_const sg (local_rcd_name ^ "." ^ name),
                     type_of state --> ty) $ state
  | NSGlobal => let
      val glob_t = #acc (get_globals_data (type_of state) globty sg)
    in
      Const(Sign.intern_const sg (global_rcd_name ^ "." ^ name),
            globty --> ty) $
      (glob_t $ state)
    end
  | AddressedGlobal => raise Fail "var_updator: shouldn't be called on addressed global"
  | UntouchedGlobal => raise Fail "var_updator: shouldn't be called on untouched global" *)
end


(* statement parsers now have type (conceptually)
     absyn.stmt  ->  (term list -> term) * (string * typ) list
   the list of strings returned is the strings that need to be parsed to
   invariants and the like.  The function returned takes the list of
   terms generated by the parsing process (which has to happen elsewhere)
   and gives back the completed term.
*)
type stmt_result = (term list -> term) * (string * typ) list

fun noparse tm = ((fn [] => tm | _ => raise Fail "noparse"), [])
fun un_noparse (f, []) = f []
  | un_noparse _ = raise Fail "noparse"
val single_id = (hd, [("", TermsTypes.bool)])

(* use split_apply when you have a list of stmt_results, and wish to create
   a function that takes a list of terms and returns another list of terms *)
fun split_apply f_s_list tlist = let
  fun recurse ts f_s_list acc =
      case f_s_list of
        [] => List.rev acc
      | (f,strs)::rest_f_s_list => let
          val (f_args, rest_ts) = Library.chop (length strs) ts
        in
          recurse rest_ts rest_f_s_list (f f_args :: acc)
        end
in
  recurse tlist f_s_list []
end

fun trans_list f styargs l : stmt_result = let  
  val parse_results = map f l
  fun strip acc s =
      case s of
        Const(@{const_name "LanguageCon.com.Seq"}, _) $ s1 $ s2 =>
          strip (strip acc s2) s1
      | _ => s::acc
  fun stripl acc [] = acc
    | stripl acc (s::rest) = strip (stripl acc rest) s
  fun doit terms = let
    val stmts = split_apply parse_results terms
  in
    case stripl [] stmts of
      [] => mk_skip_t styargs
    | list => list_mk_seq list
  end  
in
  (doit, List.concat (map #2 parse_results))
end

fun bilist2stmts [] = []
  | bilist2stmts (BI_Stmt st :: rest) = st :: bilist2stmts rest
  | bilist2stmts (BI_Decl _ :: rest) = bilist2stmts rest

fun calc_asm_params styargs statety globty thy = let
  open CalculateState
  val gs = get_standard_globals statety globty thy
  val ((ghost_acc, _), _) = #ghost gs
  val ((ms_acc, _), _) = #phantom gs
  val ((hp_acc, _), _) = #hp gs
  val gdata_acc = Abs ("s", domain_type (fastype_of ghost_acc),
    HOLogic.mk_prod (ghost_acc $ Bound 0,
        @{term "hrs_htd"} $ (hp_acc $ Bound 0)))
  val msT = range_type (fastype_of ms_acc)
in
  (msT, gdata_acc)
end

fun calc_asm_spec styargs statety globty thy vol spec lval rvals = let
  val (msT, gdata_acc) = calc_asm_params styargs statety globty thy
in
  mk_asm_spec styargs msT gdata_acc vol spec lval rvals
end

fun calc_asm_semantics_ok_to_ignore styargs statety globty thy vol spec = let
  val (msT, _) = calc_asm_params styargs statety globty thy
in
  mk_asm_ok_to_ignore msT vol spec
end


fun change_ty_f t_name t_name' ty_r' (Type(f,ty_args)) = 
    let            
      val ty_args' = map (change_ty_f t_name t_name' ty_r') ty_args
      (* val _ = writeln ("f: "^(@{make_string} (f)))
      val _ = writeln ("args: "^(@{make_string} (ty_args)))
      val _ = writeln ("args': "^(@{make_string} ty_args')) *)
    in 
      (if f = t_name then Type (t_name', filter (fn t => t<>ty_r') ty_args)
       else Type (f, ty_args'))
     end
| change_ty_f _ _ _ ty  = ty 

fun remove_ty_f ty_r (Type("fun",ty_args)) = 
    let        
      val (t_list,t) = strip_type (Type("fun",ty_args))
      val arg_list = t_list@[t]
      val arg_list' = (map (remove_ty_f ty_r) arg_list)
      val t_list' = filter (fn ty => (ty <> ty_r) andalso (ty <> Type("fun",[]))) arg_list'      
      (* val _ = writeln ("args: "^(@{make_string} (ty_args)))
      val _ = writeln ("args': "^(@{make_string} t_list')) *)
    in 
      if t_list' = [] then Type ("fun", []) 
      else if length t_list' = 1 then (nth t_list' 0)
      else (take ((length t_list') - 1) t_list') ---> (nth  t_list' ((length t_list')-1))          
     end
| remove_ty_f _ ty  = ty 




fun change_ty (Type(f,ty_args)) = 
    let      
      val filter_ty_args = filter (fn ty => ((ty <> Event_ty) andalso (ty <> Option_eventty))) ty_args
      val ty_args' = map change_ty filter_ty_args
      (* val _ = writeln ("f: "^(@{make_string} (f)))
      val _ = writeln ("args: "^(@{make_string} (ty_args)))
      val _ = writeln ("args': "^(@{make_string} ty_args')) *)
    in 
      (case f of 
        "LanguageCon.com" => Type ("Language.com", ty_args')
       |  n => Type (n, ty_args'))
     end
| change_ty ty = ty 





(* fun Csimpl2simpl' t =
  let val (t',ops) = strip_comb t
      val opsn = nth ops
      val (f,typf) = dest_Const t' 
      val (fl, last_typ) = strip_type typf
      val fln = nth fl
      val tyargs = fst (split_last (snd (dest_Type last_typ)))      
      val scom_ty = mk_scom_ty tyargs 
  in t
end *)



fun CSimpl2Simpl t_name t_name' ty_r ty_r' (Const (f,ty)) = 
 let (* val _ = writeln ("name t_name:" ^ t_name)
     val _ = writeln ("name t_name':" ^ t_name')
     val _ = writeln ("name ty_r:" ^ (@{make_string} ty_r))
     val _ = writeln ("name ty_r':" ^ (@{make_string} ty_r))
     val _ = writeln ("name f:" ^ f)
     val _ = writeln ("name ty:" ^ (@{make_string} ty)) *)
    fun last_type ty = 
      let val (_, last_typ) = strip_type ty
      in if (last_typ = ty) then ty else last_type last_typ
      end               
  in     
    case (last_type ty) of 
       (Type (ty_name,ty_l)) =>         
         let 
             val tkns = String.tokens Char.isPunct f              
         in          
         if (ty_name = t_name) then                                      
           if (can (unsuffix "Con") (nth tkns 0)) then 
             let val f' = fold (fn n => (fn c => (c^"."^n))) (drop 1 tkns) (unsuffix "Con" (nth tkns 0)) 
                 val ty' = remove_ty_f ty_r (change_ty_f t_name t_name' ty_r' ty)
             in 
               Const (f',ty') 
             end 
           else error ("No translation fuction for "^f)
         else Const(f,ty) end
      | _ => (Const (f,ty))
  end
|CSimpl2Simpl t_name t_name' ty_r ty_r' (Free (v,ty)) = 
  let val ty' = remove_ty_f ty_r (change_ty_f t_name t_name' ty_r' ty) in
    Free (v,ty')
  end 
|CSimpl2Simpl t_name t_name' ty_r ty_r' (Term.Var (v,ty)) = 
  let val ty' = remove_ty_f ty_r (change_ty_f t_name t_name' ty_r' ty) in
    Term.Var (v,ty')
  end  
|CSimpl2Simpl _ _  _ _ (Bound i) = Bound i
|CSimpl2Simpl t_name t_name' ty_r ty_r' (Abs (v,ty,t)) = Abs (v,change_ty ty, CSimpl2Simpl t_name t_name'  ty_r ty_r' t) 
|CSimpl2Simpl t_name t_name' ty_r ty_r' (t1 $ t2) =  
 let val t1' =  CSimpl2Simpl t_name t_name' ty_r ty_r' t1;
     val  t2' = CSimpl2Simpl t_name t_name' ty_r ty_r' t2
     fun filter t ti te = 
        case t of Const(_,ty') => if (ty' = ty_r) then ti else te
                  | _ => te  in 
 filter t1' t2' (filter t2' t1' (t1'$t2'))
 (* case t1' of (Const(_,ty_r1))=>       
    if (ty_r1 = ty_r) then t2'
    else (case t2' of (Const (_,ty_r2)) => if ty_r2 = ty_r then t1' else t1'$t2'
                     | _ => t1' $ t2')
 | _ => (case t2 of Const (_,ty_r2) => if (ty_r2 = ty_r) then t1' else t1' $ t2'
         | _ => t1' $ t2')*)
end
(* fun CSimpl2Simpl (Const (f,ty)) = 
 let 
    fun last_type ty = 
      let val (_, last_typ) = strip_type ty
      in if (last_typ = ty) then ty else last_type last_typ
      end           
  in 
    case (last_type ty) of 
       (Type ("LanguageCon.com",_)) => 
         let val tkns = String.tokens Char.isPunct f 
             val f' = fold (fn n => (fn c => (c^"."^n))) (drop 1 tkns) (unsuffix "Con" (nth tkns 0)) in
         if (can (unsuffix "Con") (nth tkns 0)) then 
            Const (f',change_ty ty) 
         else Const (f,change_ty ty) end
      | _ => (Const (f,ty))
  end
|CSimpl2Simpl (Free (v,ty)) = Free (v,change_ty ty)
|CSimpl2Simpl (Term.Var (v,ty)) = Term.Var (v,change_ty ty)
|CSimpl2Simpl (Bound i) = Bound i
|CSimpl2Simpl (Abs (v,ty,t)) = Abs (v,change_ty ty, CSimpl2Simpl t) 
|CSimpl2Simpl (t1 $ t2) = CSimpl2Simpl t1 $ CSimpl2Simpl t2
*)


(* fun CSimpl2Simpl t =
  let val (t',ops) = strip_comb t
      val opsn = nth ops
      val (f,typf) = dest_Const t' 
      val (fl, last_typ) = strip_type typf
      val fln = nth fl
      val tyargs = fst (split_last (snd (dest_Type last_typ)))      
      val scom_ty = mk_scom_ty tyargs
  in                                      
   case f of  
      "LanguageCon.com.Skip" => Const(@{const_name "Language.com.Skip"}, scom_ty)
     |"LanguageCon.com.Basic" => 
         Const(@{const_name "Language.com.Basic"},  
                  fln 0 --> scom_ty) $ hd ops
     |"LanguageCon.com.Spec" =>          
        Const(@{const_name "Language.com.Spec"},  
                   fln 0 --> scom_ty) $ hd ops
     |"LanguageCon.com.Seq" => 
        Const(@{const_name "Language.com.Seq"}, scom_ty --> (scom_ty --> scom_ty)) $
        CSimpl2Simpl (opsn 0) $ CSimpl2Simpl (opsn 1)
     | "LanguageCon.com.Cond" => 
                Const(@{const_name "Language.com.Cond"},  
                         (fln 0) --> ( scom_ty --> (scom_ty --> scom_ty))) $
                (opsn 0) $ CSimpl2Simpl (opsn 1) $ CSimpl2Simpl (opsn 2)
     | "LanguageCon.com.While" => 
                Const(@{const_name "Language.com.While"},  
                         (fln 0) --> ( scom_ty --> (scom_ty --> scom_ty))) $
                (opsn 0) $ CSimpl2Simpl (opsn 1) $ CSimpl2Simpl (opsn 2)    
     | "LanguageCon.com.Call" => 
                Const(@{const_name "Language.com.Call"},  
                         (fln 0) -->  scom_ty) $
                (opsn 0)
     |"LanguageCon.com.DynCom" => 
        Const(@{const_name "Language.com.DynCom"}, (fln 0) --> scom_ty) $ (opsn 0) 
     | "LanguageCon.com.Guard" => 
                Const(@{const_name "Language.com.Guard"},  
                         (fln 0) --> ((fln 1) --> (scom_ty --> scom_ty))) $
                (opsn 0) $ (opsn 1) $ CSimpl2Simpl (opsn 2)
     | "LanguageCon.com.Throw" => Const(@{const_name "Language.com.Throw"}, scom_ty)
     | "LanguageCon.com.Catch" => 
        Const(@{const_name "Language.com.Catch"}, scom_ty --> (scom_ty --> scom_ty)) $
        CSimpl2Simpl (opsn 0) $ CSimpl2Simpl (opsn 1)     
  end *)

fun stmt_term (ctxt : Proof.context)
              (cse : ProgramAnalysis.csenv)
              (fname : string)     
              (termbuilders : varinfo termbuilder)
              (varinfo : MString.t -> varinfo option)
              (fninfo : HPInter.fninfo list)
              (statetype : Term.typ)
              (globty : Term.typ)
              (localty : Term.typ)
              (styargs : Term.typ list)
              (ms : bool)
              (stmt : Absyn.statement) : stmt_result = let
  (* val _ = writeln ("args"^(@{make_string} styargs)) *)
  val stmt_term =
      stmt_term ctxt cse fname termbuilders varinfo fninfo
                statetype globty localty styargs ms
  val sg = Proof_Context.theory_of ctxt
  val progname = Config.get_global sg CalculateState.current_C_filename
  val region = Region.make{left = sleft stmt, right = sright stmt}
  val error = fn s => error(Region.toString region ^ ": " ^ s)
  val this_fn_info = valOf (List.find (fn r => #fname r = fname) fninfo)
                            handle Option =>
                                   error("No function information for "^ fname)

  val expr_term = expr_term ctxt cse termbuilders varinfo
  val emptystmt = mk_skip_t styargs
  fun stmtl (slist : statement list) = trans_list stmt_term styargs slist
  val svar = Free("s", statetype)
  val exn_var_data =  (NameGeneration.global_exn_var, c_exntype_ty,
                       true, (* unused parameter *)
                       CalculateState.Local "cparser'internal")
  fun exn_assign value = let
    val updator = var_updator sg globty localty true exn_var_data
  in
   (* David Sanan we add the event*)
    mk_basic_t styargs $ (mk_abs(svar, updator value svar)) $ None_event_exp
  end
  val exn_accessor = var_accessor sg globty localty exn_var_data
  fun wrap_cont_on_loop body_tm = let (* handles Continue "exception" *)
    val condition =
        mk_collect_t statetype $
                     mk_abs(svar, mk_eqt(exn_accessor svar, Continue_exn))
    val check_continue =
        mk_cond_t styargs $ condition $ emptystmt $
                  mk_throw_t styargs
  in
    mk_catch_t styargs $ body_tm $ check_continue
  end
  fun wrap_break_on_loop loop_tm = let
    val check_break = mk_ccatchbrk sg styargs statetype
  in
    mk_catch_t styargs $ loop_tm $ check_break
  end
  fun guard_it (gds : (term -> term * term) list) (com : term) : term = let
    fun foldthis (f,com) = let
      val (gcond, gtype) = f svar
      val gcond_set = mk_collect_t statetype $ mk_abs(svar, gcond)      
    in                      
      mk_guard gcond_set gtype com
    end    
  in
    List.foldr foldthis com gds
  end
  fun implicit_cast_rval (cty : int ctype) (e : Absyn.expr) : expr_info = let
      val e_info = array_decay (strip_kb (expr_term e))
      val e_cty  = ctype_of e_info
  in
      if cty = e_cty then e_info
      else if assignment_compatible (cty,e_cty,e) then
          typecast(sg, cty, e_info)
      else error ("Can't assign from type "^tyname e_cty^" to type "^
                  tyname cty)
  end  
in
  case snode stmt of
    Block bilist => stmtl (bilist2stmts bilist)
  | Assign(e1, e2) => let     
      (* val _ = writeln "Assign" *)
      val e1_info = expr_term e1
      val e1_cty = ctype_of e1_info
      val (e1_lval,e1_rval) = (valOf (lval_of e1_info), rval_of e1_info)
          handle Option => error "No lvalue for lhs of assignment"
      val e2' =
          (* if the lvar on the left is of array type, assume that this is an
             initialisation of an array, rather than an attempt to do an
             illegal assignment to an array object.  Could enforce by having
             two Assign forms in the statement type, but for now just rely
             on having a C compiler check code for well-formedness *)
          case e1_cty of
            Array _ => expr_term e2
          | _ => implicit_cast_rval e1_cty e2
      val gds = guards_of e1_info @ guards_of e2' @
                (if ms then lguards_of e1_info else [])
    in
     (* David Sanan we add the event *)
      noparse (guard_it gds (mk_basic_t styargs $
                               mk_abs(svar, e1_lval (rval_of e2' svar) svar) $ None_event_exp))
     (* noparse (guard_it gds
                        (mk_basic_t styargs $
                               mk_abs(svar, e1_lval (rval_of e2' svar) svar))) *)
    end
  (*David Sanan
    we need to change the types for the type of the field updator and the field accesor
    to localty --> vty
    and upd_ty is of type (vty --> vty) --> localty --> localty
    we need to wrap up the access to acc_ty and upd_ty from the state 
  *)
  | LocalInit v_e => let
      (* val _ = writeln "LocalInit" *)
      open TermsTypes
      val vname =
          case enode v_e of
            Var(nm, ref extra) => let
            in
              case extra of
                SOME (_, MungedVar mvi) => MString.dest (#munge mvi)
              | _ => error "Confused by lack of variable info"
            end
          | _ => error "Bad variable being initialised"
      val vinfo = expr_term v_e
      val vty = CalculateState.ctype_to_typ(sg, ctype_of vinfo)
      val acc_ty = statetype --> vty
      val acc_name =
          Sign.intern_const sg (HoarePackage.varname vname)
      val acc_ty' = localty --> vty
      val acc_t = Const(acc_name, acc_ty')
      val upd_ty = (vty --> vty) --> statetype --> statetype
      val upd_ty' = (vty --> vty) --> localty --> localty
      val upd_name =
          Sign.intern_const sg
                            (suffix Record.updateN
                                    (HoarePackage.varname vname))
      val vupd_t = Const (upd_name, upd_ty')
      val com_t = Const(@{const_name "lvar_nondet_init"},
                        acc_ty --> upd_ty --> mk_com_ty styargs)      
    in
     (* David Sanan 
        we need to wrap up the accessor in an abstract function from state to local component
       *)
      noparse (com_t $ (type_var_access_abs (CalculateState.Local "s") statetype acc_t) $ 
                        (update_state_abs (CalculateState.Local "s") statetype vupd_t))
      (* noparse (com_t $ acc_t $ vupd_t) *)
    end
  | Auxupd r => let
      (* val _ = writeln "Auxup" *)
      open MemoryModelExtras
      val hrs = (NameGeneration.global_heap_var,
                 extended_heap_ty,
                 NONE, (* no corresponding C type *)
                 CalculateState.NSGlobal)
      fun upd r_tm =
          mk_abs(svar,
                 var_updator sg globty localty  false hrs (mk_aux_update (r_tm $ svar))
                             svar)
      fun gcond_set r_tm =
          mk_collect_t statetype $ mk_abs(svar, mk_aux_guard (r_tm $ svar))
    in
      ((fn [r_tm] =>
           (mk_guard (gcond_set r_tm) safety_error (mk_basic_t styargs $ upd r_tm $ None_event_exp))),
       [(NameGeneration.apt_string r, mk_aux_type statetype)])
    end
  | Ghostupd s => let
      (* val _ = writeln "Ghostupd" *)
      open MemoryModelExtras
      val ghostty = case CalculateState.get_ghostty sg progname of
                      NONE => raise Fail ("No ghosttype data for "^progname)
                    | SOME typ => typ
      val ghostvar = (NameGeneration.global_var NameGeneration.ghost_state_name,
                      ghostty,
                      NONE,
                      CalculateState.NSGlobal)
      val stype = mk_prod_ty (bool,ghostty --> ghostty)
      val fst = Const(@{const_name "fst"}, stype --> bool)
      val snd = Const(@{const_name "snd"}, stype --> ghostty --> ghostty)
      fun upd t = mk_abs(svar,                          
                         var_updator sg globty localty false ghostvar (snd $ (t $ svar)) svar)
      fun guard t =
          mk_collect_t statetype $ mk_abs(svar, fst $ (t $ svar))
    in
      ((fn [t] =>
           (mk_guard (guard t)
                     @{const "GhostStateError"}
                     (mk_basic_t styargs $ upd t $ None_event_exp))),
       [(NameGeneration.apt_string s, statetype --> stype)])
    end
  | EmptyStmt => noparse emptystmt
  | Trap(trappable, stmt) => 
    let
      val _ = writeln "Trap"
      val (stmtf, stmt_parses) = stmt_term stmt
      val wrap0 = case trappable of BreakT => wrap_break_on_loop
                                  | ContinueT => wrap_cont_on_loop
      val wrap = if might_raise trappable stmt then wrap0 else (fn x => x)
    in
      ((fn tlist => (wrap (stmtf tlist))), stmt_parses)
    end
  | While(guard,inv,body) => let
      (* val _ = writeln "While" *)
      val guard' = mk_isabool (expr_term guard)
      val guard_val = rval_of guard'
      val guard_guards = guards_of guard'
      val guard_tm = mk_collect_t statetype $ mk_abs(svar, guard_val svar)
      val var_tm =
          mk_arbitrary (mk_set_type (mk_prod_ty(statetype, statetype)))
      val (body_f, body_parses) = stmt_term body
      fun mkloop body_tm inv_tm = let
        val body' = if null guard_guards then body_tm
                    else list_mk_seq [body_tm, guard_it guard_guards emptystmt]
        val base = mk_while_t styargs $ guard_tm $ inv_tm $ var_tm $ body'
      in
        guard_it guard_guards base
      end
    in
      case inv of
        NONE => let
          val inv_tm = mk_empty_INV statetype
          fun doit tlist = mkloop (body_f tlist) inv_tm
        in
          (doit, body_parses)
        end
      | SOME s => let 
          val parse_needed = (node s, mk_set_type statetype)
          
          fun doit tlist = 
              mkloop (body_f (tl tlist)) (hd tlist) 
        in
          (doit, parse_needed :: body_parses)
        end
    end
  | IfStmt(guard,thenbr,elsebr) => let
     (* val _ = writeln "If"      *)
      val guard_ei = mk_isabool (expr_term guard)
      val guard_val = rval_of guard_ei
      val then_r as (_, then_parses) = stmt_term thenbr
      val else_r as (_, else_parses) = stmt_term elsebr
      fun doit tlist = let  
        val [then_tm, else_tm] = split_apply [then_r, else_r] tlist
      in
        guard_it (guards_of guard_ei)
                 (mk_cond_t styargs $
                            (mk_collect_t statetype $
                                          mk_abs(svar, guard_val svar)) $
                            then_tm $
                            else_tm)
      end
    in
      (doit, then_parses @ else_parses)
    end
  | (* David Sanan code for Await *)
    Await(guard, body) => let
      (* val _ = writeln "Await"           *)
      val guard_ei = mk_isabool (expr_term guard)      
      val guard_val = rval_of guard_ei      
      val (body_f, body_parses) = stmt_term body      
      fun doit tlist = 
        let (* val _ = writeln ("tlist: "^(@{make_string} tlist)) *)
            (* val _ = writeln ("body_await_before: "^(@{make_string} ((body_f tlist)))) 
            val _ = writeln ("body_await_after: "^(@{make_string} (CSimpl2Simpl "LanguageCon.com" "Language.com" Option_eventty Event_ty (body_f tlist) ))) *)
           (* val _ = writeln ("body_await_after: "^(@{make_string} (CSimpl2Simpl (body_f tlist)))) *)  in
        guard_it (guards_of guard_ei)
                 (mk_await_t styargs $
                            (mk_collect_t statetype $
                                          mk_abs(svar, guard_val svar)) $
                            CSimpl2Simpl "LanguageCon.com" "Language.com" Option_eventty Event_ty (body_f tlist) $ None_event_exp)   
        end         
    in
      (doit, body_parses)
    end
  | (* David Sanan code for Lock *)
    Lock(l_exp) => let
      (* val _ = writeln "Lock"   *)
      val expr_info = expr_term l_exp
      val e1_cty = ctype_of expr_info
      val (e1_lval,e1_rval) = (valOf (lval_of expr_info), rval_of expr_info)
          handle Option => error "No lvalue for lhs of assignment"            
      val condition =
        mk_collect_t statetype $
                     mk_abs(svar, mk_eqt(e1_rval svar, mk_zero @{typ "sword32"})) 
      val guard_ei = mk_isabool expr_info   
      val sstyargs = take (length styargs - 1) styargs  
      val id_var_data =  ("id_'", c_id_ty,
                       true, (* unused parameter *)
                       CalculateState.Local "cparser'internal")

      val id_accessor = var_accessor sg globty localty id_var_data      
      val addition = mk_abs(svar, mk_plus ((id_accessor svar),mk_one @{typ "sword32"}))
      in
        noparse( guard_it (guards_of guard_ei) 
                        (mk_await_t styargs $ condition $ 
                           (mk_sbasic_t sstyargs $ mk_abs(svar, e1_lval (addition$svar) svar)) $ 
                           None_event_exp ) )
    end
 | (* David Sanan code for id *)
    Id(l_exp) => let
      val _ = writeln "Id"   
      val expr_info = expr_term l_exp
       val e1_cty = ctype_of expr_info
      val (e1_lval,e1_rval) = (valOf (lval_of expr_info), rval_of expr_info)
          handle Option => error "No lvalue for lhs of assignment"                   
      val guard_ei = mk_isabool expr_info           
      val id_var_data =  ("id_'", c_id_ty,
                       true, (* unused parameter *)
                       CalculateState.Local "cparser'internal")
      val id_accessor = var_accessor sg globty localty id_var_data      
      val addition = mk_abs(svar, (id_accessor svar))
      in
        noparse( guard_it (guards_of guard_ei)  
                         (mk_basic_t styargs $ mk_abs(svar, e1_lval (addition$svar) svar) $ None_event_exp))
    end
  | Return (SOME e) => let
      (* val _ = writeln "Return" *)
      val (retvar_name, retvar_ty, retvar_cty) = (hd (#outparams this_fn_info))
          handle Empty =>
                 error ("No return parameter for function "^fname)
      (* David Sanan 
        the return updator is now a function from the local component to local component *)
      val retvar = Const (Sign.intern_const sg (suffix Record.updateN
                                                       (Hoare.varname retvar_name)), (* ??? *)
                          (retvar_ty --> retvar_ty) --> localty --> localty)
      (* val retvar = Const (Sign.intern_const sg (suffix Record.updateN
                                                       (Hoare.varname retvar_name)), (* ??? *)
                          (retvar_ty --> retvar_ty) --> statetype --> statetype) *)
      val e'     = implicit_cast_rval retvar_cty e
      val value  = mk_abs (svar, rval_of e' svar) (* Is svar safe? *)
    in
      noparse (guard_it (guards_of e')
                        (mk_creturn sg styargs statetype retvar value))
    end                       

  | Return NONE =>
      noparse (mk_creturn_void sg styargs statetype)
  | ReturnFnCall (s, args) => let
      (* val _ = writeln "ReturnFnCall" *)
      val (retvar_name, _, cretty) =
          hd (#outparams this_fn_info)
          handle Empty => error ("No return parameter for function "^fname)
      val mvi = MungedVar {munge = MString.mk retvar_name, owned_by = NONE}
      val retvar =
          ewrap (Var (retvar_name, ref (SOME (cretty, mvi))),
                 eleft s,
                 eright s)
      val retvar_assign =
          un_noparse (stmt_term(swrap(AssignFnCall(SOME retvar, s, args),
                                      sleft stmt, sright stmt)))      
      val return_t =
          un_noparse (stmt_term (swrap(Return (SOME retvar),
                                       sleft stmt, sright stmt)))      
    in 
      noparse (list_mk_seq [retvar_assign, return_t])
    end
  | Break =>  let
          val _ = writeln "break" in noparse (mk_cbreak sg styargs statetype) end
  | Continue => let
          val _ = writeln "Continue"
      val exn_assign = exn_assign Continue_exn
    in
      noparse (list_mk_seq [exn_assign, mk_throw_t styargs])
    end
  | EmbFnCall(lval,callname,args) => let
    (* val _ = writeln "EmbFnCall" *)
    in
      stmt_term (swrap (AssignFnCall(SOME lval, callname, args),
                        sleft stmt,
                        sright stmt))
    end
  | AssignFnCall(lvalopt, call_e, args) => let      
       (*   val _ = writeln "AssignFnCall" *)
      open ProgramAnalysis
      val (HP_call_t, fndes_t, informals, outname_info_opt, callname, callgds) =
          case fndes_callinfo cse call_e of
            (DirectCall callname, _) => let
              fun mk_param (s,ty,ctyopt) =
                  (HoarePackage.varname s, ty, valOf ctyopt)
                  handle Option => error ("No C type recorded for "^s^
                                          " in function "^ callname)
              val (ips, outopt) =
                  case List.find (fn {fname,...} => fname = callname) fninfo of
                    NONE => error ("Unknown function: "^callname)
                  | SOME r => (#inparams r,
                               case #outparams r of [] => NONE
                                                  | p :: _ => SOME p)     
            in              
              (mk_call_t styargs,
               mk_VCGfn_name sg callname,
               map mk_param ips,
               outopt,
               callname,
               [])
            end
          | (FnPtrCall(rty, _ (* argtys *)), _) => let
              val call_ei = expr_term call_e
              open NameGeneration
              val naming = Const (Sign.intern_const sg naming_scheme_name,
                    int --> mk_option_ty string_ty)
              val (pbody, pguard) = MemoryModelExtras.mk_lookup_proc_pair
                      symbol_table naming
                      (mk_ptr_val (rval_of call_ei svar))
              val retinfo =
                  case rty of
                      Void => NONE
                    | _ => SOME (NameGeneration.return_var_name rty |> MString.dest,
                                 CalculateState.ctype_to_typ(sg,rty),
                                 rty)
              fun guard s = let
                val fptr_val = rval_of call_ei s
              in
                (mk_conj (@{const "c_fnptr_guard"} $ fptr_val, pguard),
                  c_guard_error)          
              end
            in
              (mk_dyncall_t styargs,
               mk_abs(svar, pbody), [], retinfo,
               "fn. ptr", [guard])
            end
      (* David Sanan we add the event for the initialisation and the mod function 
         the events will be None for the moment.
          call's arguments are: 
          1. initialisation (copying actual parameters to formals)
          2. initialisation event
          3. name of procedure to call (a string in all likelihood)
          4. a return modification function where the first argument is the
             very original state, and the next one is the final state that is
             going to be modified.
          5. return modification event
          6. the continuation, if you like: what to do after returning.
             Gets the same parameters as 3 gets.
             Doesn't get called with exception returns.  Will get called
             in a third state again, that pertaining after 3 has been
             applied.
      *)
      (* first step is to match up actuals to formals *)        
      val actuals = map (fn e => (array_decay (strip_kb (expr_term e)), e)) args       
      val gds = List.concat (map (fn (ei,_) => guards_of ei) actuals) @
                callgds      
      fun param_to_lval (param_name,ipty,pty) ((actual_info, actuale), st) = let
        val fullname =
            Sign.intern_const sg (suffix Record.updateN param_name)
        val stty = type_of st        
        val actual_cty = ctype_of actual_info
        val coerced_value =
            if actual_cty = pty then actual_info
            else if assignment_compatible(pty, actual_cty, actuale) then
              typecast(sg,pty,actual_info)
            else
              error ("Actual parameter's type: "^tyname actual_cty^
                     " is not compatible with formal parameter's type: "^
                     tyname pty)                
        val Kupd = K_rec ipty $ rval_of coerced_value svar                          
        val loc_update = Const(fullname, (ipty --> ipty) --> (localty --> localty)) $ Kupd
        (* David Sanan 
           the state is a tuple (globals, locals) it is necessary to 
           change the creation of local params accordingly*)       
      in 
      (* David Sanan we generate the new local variablesand the state
        is constructed leaving the global variables unchanged *)
        (* Const(fullname, (ipty --> ipty) --> (stty --> stty)) $ Kupd $ (local_comp st) *)
       update_state (CalculateState.Local "s") stty loc_update st
       (* Const(@{const_name "Product_Type.prod"}, globty --> localty--> stty) $ local_upd $ global_comp st *)
      end              
      val formal_fs = map param_to_lval informals      
      val _ = if length formal_fs <> length actuals then
                error("Number of arguments ("
                      ^Int.toString (length actuals)^
                      ") in call to "^callname^
                      " doesn't match declarations ("
                      ^Int.toString (length formal_fs)^")")
              else ()      
      fun mkinit formals actuals =       
          case (formals, actuals) of
            ([], []) => svar
          | (f::fs, ac::acs) => f (ac, mkinit fs acs) 
          | _ => raise Fail "Catastrophic invariant failure XXX"       
      val init = mk_abs(svar, mkinit (List.rev formal_fs) (List.rev actuals))       
      val return = mk_callreturn globty statetype    
      val result = let    
        val tvar = Free("t", statetype)
      in
        case lvalopt of
          NONE => let
            val skip_equivalent =
                mk_basic_t styargs $ mk_abs(svar, svar) $  None_event_exp          
          in
            mk_abs(svar, mk_abs(tvar, skip_equivalent))
          end
        | SOME e => let
            val lhs_ei = expr_term e
            val lhs_cty = ctype_of lhs_ei
            val outlval = valOf (lval_of lhs_ei)
                handle Option => error "Assigning function call to non-lvalue"
            val (outname0, out_typ, out_ctyp) = valOf outname_info_opt
                handle Option =>
                       error ("Using return value from void function "^
                              callname)
            val outname = HoarePackage.varname outname0
            (* David Sanan 
               the result takes the local component to update the return variable
               the type is localty and it access the second component of the state
            *)
            fun outrval0 st = let
              val fullname = Sign.intern_const sg outname              
            in             
              Const(fullname, localty --> out_typ) $ 
                 ((type_var_access (CalculateState.Local "s")  (type_of st))$st)
            end
            val out_einfo = mk_rval(outrval0, out_ctyp, false, sleft stmt,
                                    sright stmt)
            val outrval =
                if lhs_cty = out_ctyp then outrval0
                else if assignment_compatible(lhs_cty, out_ctyp,
                                              (* expression is irrelevant *)
                                              ewrap(Arbitrary (Signed Int),
                                                    SourcePos.bogus,
                                                    SourcePos.bogus))
                then
                  rval_of (typecast(sg,lhs_cty,out_einfo))
                else
                  error("Return type of function "^callname^
                        " not compatible with value assigned to")
            val uvar = Free("u", statetype)                                   
          in
            mk_abs(svar,
                   mk_abs(tvar,
                          mk_basic_t styargs $
                               mk_abs(uvar, outlval (outrval tvar) uvar) $ None_event_exp))
          end
      end
(*      val _ = writeln ("result: "^(@{make_string} result))
      val _ = writeln ("type result: "^(@{make_string} (type_of result))) *)
    in 
      noparse
        (guard_it gds
                  (HP_call_t $ init $ None_event_exp $ fndes_t $ return $ None_event_exp $ result))
    end
  | Spec((prevar, pre), body, post) => let
      (* val _ = writeln "Spec" *)
      val body_r as (_, body_parses) = stmtl body
      fun doit tlist = let
        val [pre_tm, post_tm, body_tm] =
            split_apply [single_id, single_id, body_r] tlist
      in
        mk_specAnno pre_tm (Abs(prevar, statetype, body_tm)) post_tm
      end
      fun mk_abs_string s = "\<lambda> "^prevar^" . (" ^ s ^")"
    in
      (doit, (mk_abs_string pre, statetype --> mk_set_type statetype) ::
             (mk_abs_string post, statetype --> mk_set_type statetype) ::
             body_parses)
    end
  | Switch (testexp, cases) => let
     (* val _ = writeln "Switch" *)
      (* "The integer promotions are performed on the controlling expression." *)
      val e = intprom_ei sg (expr_term testexp)
      val testexp_t = ctype_of e
      val e_rv = rval_of e
      val test_body = e_rv svar
      val gty = type_of test_body
      val e_test = mk_abs(svar, test_body)
      fun mk_case (labs : expr option list, bilist : block_item list) = let
        val s_r = stmtl (bilist2stmts bilist)
        val lab_t : term = let
          fun foldthis (lab,acc) : term = let
            (* "The constant expression in each case label is converted to the
             * promoted type of the controlling expression." *)
            val e = typecast (sg, testexp_t, expr_term (valOf lab))
            val e_t = rval_of e svar
          in
            mk_insert(e_t,acc)
          end
        in
          if labs = [NONE] then mk_UNIV gty
          else List.foldl foldthis (mk_empty gty) labs
        end
      in
        (lab_t, s_r)
      end
      val case_results0 : (term * stmt_result) list = map mk_case cases
      val (guards, case_results) = ListPair.unzip case_results0
      fun doit tlist = let
        val case_ts0 = split_apply case_results tlist
        val case_ts1 = ListPair.zip(guards, case_ts0)
        val case_ts = map mk_pair case_ts1
      in
        mk_switch (e_test, HOLogic.mk_list (type_of (hd case_ts)) case_ts)
                  |> guard_it (guards_of e)
      end
    in
      (doit, List.concat (map #2 case_results))
    end
  | Chaos expr =>
    let
      (* val _ = writeln "Chaos" *)
      val ei = expr_term expr
      val lv = valOf (lval_of ei)
               handle Option => error ("Value (" ^ expr_string expr ^
                                       ") without l-value passed to Chaos")
      val cty = ctype_of ei
      val v = Free("v", CalculateState.ctype_to_typ(sg,cty))
      val f = list_mk_abs([v,svar], lv v svar)
    in
      noparse (Const(@{const_name "cchaos"}, type_of f --> mk_com_ty styargs) $ f)
    end
  | AsmStmt st =>
    (let
      (* FIXME: is this correct for all arches? *)
     (* val _ = writeln "AsmStmt" *)
      val reg_cty = Unsigned ImplementationNumbers.ptr_t;
      val (nm, vol, ret, args) = ProgramAnalysis.split_asm_stmt (AsmStmt st)
      val _ = if ASM_Ignore_Hooks.ignore_thy (nm, vol, ret, args) sg
        then raise Fail "hook fired" else ()
      val sty = hd styargs
      val ret = case ret of NONE => (fn x => (fn s => s))
        | SOME r => valOf (lval_of (expr_term r))
            handle Option => error ("Value (" ^ expr_string r
                ^ ") without l-value used as asm stmt lval specifier.")
      val x = Free ("x", addr_ty)
      val ret = mk_abs (x, mk_abs (svar, ret x svar))
      fun conv_arg arg = mk_abs (svar, rval_of (typecast
            (sg, reg_cty, expr_term arg)) svar)
        handle Option => error ("Value (" ^ expr_string arg
                ^ ") without r-value used as asm stmt rval specifier.")
      val args = map conv_arg args
    in
      noparse (calc_asm_spec styargs statetype globty sg
            (#volatilep st) nm ret args)
    end handle Fail str => let
      val nm = #head (#asmblock st)
      val ok = calc_asm_semantics_ok_to_ignore styargs statetype globty sg
            (#volatilep st) nm
      val err = unspecified_syntax_error2 str
      val guard = mk_collect_t statetype
            $ mk_abs (svar, HOLogic.mk_disj (ok, err))       
    in noparse (mk_guard guard unspecified_syntax_error1 emptystmt) end)
  | _ => error ("Can not yet handle "^stmt_type stmt^" statement forms")
end

fun lookup_fld alist (s, f) =
    case assoc(alist, s) of
      NONE => error ("No struct information for type "^s)
    | SOME flds => let
      in
        case List.find (fn (fldname, ty, cty) => fldname = f) flds  of
          NONE => error ("No type information for fld "^f^" in struct "^s)
        | SOME (_, ty, _) => ty
      end

fun rcd_accessor sg rcdinfo (sname, fldname) rcdterm = let
  val fullname = Sign.intern_const sg (sname ^ "." ^ fldname)
  val fldty = lookup_fld rcdinfo (sname, fldname)
in
  Const(fullname, type_of rcdterm --> fldty) $ rcdterm
end

fun rcd_updator sg (sname, fldname) newvalue rcdterm = let
  val fullname =
      Sign.intern_const sg (sname ^ "." ^ suffix Record.updateN fldname)
  val valty = type_of newvalue
  val rcdty = type_of rcdterm
  val ty = (valty --> valty) --> (rcdty --> rcdty)
  val Kupd = K_rec valty $ newvalue
in
  Const(fullname, ty) $ Kupd $ rcdterm
end

fun state_vlookup (fname_opt : string option) (s:MString.t) (state:CalculateState.mungedb) = let
in
  case CNameTab.lookup state {varname = s, fnname = fname_opt} of
    NONE => NONE
  | SOME (realnm, ty, cty, vsort) => let
      val realnm' = case fname_opt of
                      NONE => NameGeneration.global_var (MString.dest realnm)
                    | SOME f => HoarePackage.varname (MString.dest realnm)
    in
      SOME(realnm',ty,cty,vsort)
    end
end

fun state_varlookup fname s state =
    (* check to see if it's a normal local variable *)
    case state_vlookup (SOME fname) s state of
      NONE => let
      in
        (* check to see if it's a global variable (one accessed through a
           pointer) *)
        case state_vlookup NONE (NameGeneration.C_global_var s) state of
          NONE => let
          in
            (* check to see if it's a embedded function call return variable *)
            case NameGeneration.dest_embret s of
              SOME _ => state_vlookup (SOME "") s state
            | NONE => NONE
          end
        | x => x
      end
    | x => x


fun strip_invs com statetype =
    case com of
      (c as Const("Language.whileAnno", T)) $ g $ i $ v $ b => let
      in
        c $ g $ mk_empty_INV statetype $ v $ strip_invs b statetype
      end
    | (Const("Language.specAnno", T) $ _ $ (Abs(_, _, bdy)) $ _ $ _) => let
      in
        strip_invs bdy statetype
      end
    | (t $ g) => strip_invs t statetype $ strip_invs g statetype
    | Abs (v, T, b) => Abs (v, T, strip_invs b statetype)
    | t => t

(* called so that parsing of invariants etc can be done in a context where
   Isabelle variables corresponding to global variables (x_addr, for example)
   get the right type *)
fun lookup_addr_vars state = let
  fun foldthis ({varname,fnname}, (realnm,ty,cty,vsort)) acc =
      case fnname of
        NONE => Symtab.update
                    (NameGeneration.global_addr (MString.dest varname), mk_ptr_ty ty)
                    acc
      | SOME _ => acc
in
  CNameTab.fold foldthis state Symtab.empty
end

fun fndefn_term (state : CalculateState.mungedb) cse fninfo rcdinfo ms globty localty styargs ctxt decl = let
  val thy = Proof_Context.theory_of ctxt
  open CalculateState
  val statetype = hd styargs
  val ((_ (* rettype *), fname), _ (* params *), _ (* prepost *), locbodyw) =
      decl
  val fname = node fname
  val bilist = node locbodyw
  val _ = Feedback.informStr (0, "Translating function "^fname)
  val body = bilist2stmts bilist
  fun varinfo s = state_varlookup fname s state  
  val termbuilders : varinfo termbuilder =
      TB { var_updator = var_updator thy globty localty,
           var_accessor = var_accessor thy globty localty,
           rcd_updator = rcd_updator thy,
           rcd_accessor = rcd_accessor thy rcdinfo}
  val (ecenv,senv) = let
    open ProgramAnalysis
  in
    (cse2ecenv cse, get_senv cse)
  end    
  val stmt_trans = stmt_term ctxt cse fname termbuilders
                             varinfo fninfo
                             statetype globty localty styargs ms          
  val (body_f, body_parses) = trans_list stmt_trans styargs body 
 
  val body_parse_terms = let    
    val ctxt = thy2ctxt thy    
    val rawterms = map (apfst (Syntax.parse_term ctxt)) body_parses
    val typetable = lookup_addr_vars state     
    fun foldthis (vnm,ty) acc = (Free(vnm, dummyT), Free(vnm, ty)) :: acc
    val theta = Symtab.fold foldthis typetable []
    fun mapthis (rawterm,ty) = let
      val substterm = subst_free theta rawterm
    in
      Const(@{const_name "HOL.eq"}, dummyT) $ substterm $ mk_arbitrary ty
    end
    val typedterms = map mapthis rawterms
    val checked_terms = Syntax.check_terms ctxt typedterms    
  in
    map (fn (_ $ x $ _) => x) checked_terms
  end  
  
  val body_stmts = body_f body_parse_terms  
  (* a function is translated to a TRY body CATCH SKIP END form;
     the catch is for any return statements in the body.  Other abrupt
     terminations would be of break or continue statements, which would
     be handled by the looping forms.  For this reason the catch doesn't
     check to see if the global exn variable has been set appropriately.

     If the last statement of the function is not a return, the flow of
     control will just fall through the bottom of the function, which is
     fine.
  *)
  val body_stmts' =
      case ProgramAnalysis.get_rettype fname cse of
        NONE => raise Fail ("No return type info for function "^fname)
      | SOME Void => body_stmts
      | _ => list_mk_seq [body_stmts,
                          mk_guard (mk_empty statetype) dont_reach_error
                                   (mk_skip_t styargs)]
  (* val _ = writeln ("bod: "^(@{make_string} body_stmts')) *)
  val body = body_stmts' 
  val body = mk_catch_t styargs $ body_stmts' $ mk_skip_t styargs  
in
  (fname, body, strip_invs body statetype)
end

fun extract_defined_functions ast = let
  fun recurse acc decls =
      case decls of
        [] => List.rev acc
      | FnDefn p :: ds => recurse (p::acc) ds
      | _ :: ds => recurse acc ds
in
  recurse [] ast
end



(* this function is directly called by the Isar loop, and is passed the
   variable state information, as well as the AST of the C program being
   installed
     state :
     ast   : Absyn.ext_decl list
*)
fun define_functions (globty, localty, styargs)
                     (vdecls : CalculateState.mungedb)
                     cse
                     fninfo
                     rcdinfo
                     ms
                     ast
                     ctxt =
let  
  open TermsTypes CalculateState
  val fns = extract_defined_functions ast
  val function_info =
      map (fndefn_term vdecls cse fninfo rcdinfo ms globty localty styargs ctxt) fns
in
  function_info
end

end (* struct *)
