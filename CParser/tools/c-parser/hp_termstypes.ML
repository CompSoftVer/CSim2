(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature HP_TERMS_TYPES =
sig
  (*David Sanan we add the type for events*)
  val Event_ty: typ
  val Option_eventty: typ
  val StrictC_errortype_ty : typ  (* errors are from failed guards *)
  val c_exntype_ty : typ   (* exns are flow-control interrupts:
                                return, break and continue *)
  (* David Sanan we add the type for the id *)
  val c_id_ty : typ
  (* David Sanan mk_com_ty is a list of four elements now, 
     since we add the event type*)
  val mk_com_ty : typ list -> typ (* list of three elements *)
  (* David Sanan mk_scom_ty is the constructor for the Simpl type *)
  val mk_scom_ty : typ list -> typ
  (* David Sanan we add the type for the global state as a product *)
  val mk_statety: typ list -> typ
  (* David Sanan we add a destructor of the state *)
  val dest_statety1: typ ->  typ
  val dest_statety2: typ -> typ

  val div_0_error : term
  val shift_error : term
  val safety_error : term
  val c_guard_error : term
  val arraybound_error : term
  val signed_overflow_error : term
  val dont_reach_error : term
  val side_effect_error : term
  val ownership_error : term
  val unspecified_syntax_error1 : term
  val unspecified_syntax_error2 : string -> term


  val Continue_exn : term
  val Return_exn : term
  val Break_exn : term

  val list_mk_seq : term list -> term
  val mk_VCGfn_name : theory -> string -> term
  val mk_basic_t : typ list -> term
  val mk_sbasic_t : typ list -> term
  val mk_call_t : typ list -> term
  val mk_callreturn : typ -> typ -> term
  val mk_catch_t : typ list -> term
  val mk_cbreak : theory -> typ list -> typ -> term
  val mk_ccatchbrk : theory -> typ list -> typ -> term
  val mk_cond_t : typ list -> term
  val mk_creturn : theory -> typ list -> typ -> term -> term -> term
  val mk_creturn_void : theory -> typ list -> typ -> term
  val mk_dyncall_t : typ list -> term
  val mk_empty_INV : typ -> term
  val mk_guard : term -> term -> term -> term
  val mk_skip_t : typ list -> term
  val mk_Spec : typ list * term -> term
  val mk_specAnno : term -> term -> term -> term
  val mk_switch : term * term -> term
  val mk_throw_t : typ list -> term
  val mk_while_t : typ list -> term
(* David Sanan 
   added signature for await *)
  val mk_await_t : typ list -> term


end

structure HP_TermsTypes : HP_TERMS_TYPES =
struct

open IsabelleTermsTypes
val Event_ty = @{typ "CProof.event_type"}
val Option_eventty = @{typ "CProof.event_type Option.option"}
val StrictC_errortype_ty = @{typ "CProof.strictc_errortype"}
val c_exntype_ty = @{typ "CProof.c_exntype"}
val c_id_ty = @{typ sword32}

fun dest_statety1 stty = hd (snd (dest_Type stty))
fun dest_statety2 stty = hd (tl (snd (dest_Type stty)))

fun mk_statety args = Type(@{type_name "Product_Type.prod"}, args)  

fun update_local stty upd v  =
   let open  NameGeneration
      val globty = dest_statety1 stty
      val localty = dest_statety2 stty
      val glob = Const(@{const_name "fst"} , (stty-->globty)) $ v
      val loc =  Const(@{const_name "snd"} , (stty-->localty)) $ v                  
   in 
       Const(@{const_name "Product_Type.Pair"}, globty --> localty--> stty) $ glob $ (upd $loc)
   end

fun mk_com_ty args = Type("LanguageCon.com", args)
                                            
fun mk_scom_ty (args:typ list) =    
    Type("Language.com", args) 


fun mk_skip_t tyargs = Const("LanguageCon.com.Skip", mk_com_ty tyargs)

val Return_exn = @{const "CProof.c_exntype.Return"}
val Break_exn = @{const "CProof.c_exntype.Break"}
val Continue_exn = @{const "CProof.c_exntype.Continue"}

fun mk_VCGfn_name thy s =
    Const(Sign.intern_const thy (suffix HoarePackage.proc_deco s), int)

fun mk_basic_t tyargs = let
  val statety = hd tyargs
in
  Const(@{const_name "LanguageCon.com.Basic"},
        (statety --> statety) --> Option_eventty --> mk_com_ty tyargs)
end

fun mk_sbasic_t tyargs = let
  val statety = hd tyargs
in
  Const(@{const_name "Language.com.Basic"},
        (statety --> statety) -->  mk_scom_ty tyargs)
end

(*David Sanan I add the event argument *)
fun mk_call_t tyargs = let
  (* val _ = writeln (@{make_string} tyargs) *)
  val sarg = hd tyargs
  val parg = List.nth (tyargs, 1)
  val sarg2 = sarg --> sarg
  val sarg3 = sarg --> sarg2
  val com_ty = mk_com_ty tyargs
  val s2_to_com = sarg --> (sarg --> com_ty)  
  val earg = Option_eventty  
in
  Const(@{const_name "LanguageCon.call"},
        sarg2 --> (earg --> (parg --> (sarg3 --> (earg --> (s2_to_com --> com_ty))))))
end

fun mk_dyncall_t tyargs = let
  val sarg = hd tyargs
  val parg = List.nth(tyargs, 1)
  val earg = Option_eventty
  val s2p_arg = sarg --> parg
  val sarg2 = sarg --> sarg
  val sarg3 = sarg --> sarg2
  val com_ty = mk_com_ty tyargs
  val s2_to_com = sarg --> (sarg --> com_ty)
in
  Const(@{const_name "LanguageCon.dynCall"},
        sarg2 --> (earg --> (s2p_arg --> (sarg3 --> (earg --> (s2_to_com --> com_ty))))))
end



(* fun mk_callreturn globty statety = let  
  val svar = Free("s", statety)
  val tvar = Free("t", statety)
  val gupdate = Const(suffix Record.updateN "StateSpaceProduct.globals",
                      (globty --> globty) --> (statety --> statety))
  val gaccess = Const(@{const_name "fst"},
                      statety --> globty)
  val Kupd = K_rec globty $ (gaccess $ tvar)
in
  mk_abs(svar, mk_abs(tvar, gupdate $ Kupd $ svar))
end *)

(* David Sanan mk_callreturn must return a state with the global variables of the new state
  and the local variables of the old state *)
fun mk_callreturn globty statety = let  
  val svar = Free("s", statety)
  val tvar = Free("t", statety)
  val locty = dest_statety2 statety
  val prod_state = Const(@{const_name "Product_Type.Pair"}, globty --> locty--> statety)
  val gaccess = Const(@{const_name "fst"},
                      statety --> globty)
  val laccess = Const(@{const_name "snd"},
                      statety --> locty)    
in
  mk_abs(svar, mk_abs(tvar, prod_state $ (gaccess $ (Bound 0))$ (laccess $ (Bound 1))))
end


fun mk_while_t tyargs = let
  val statety = hd tyargs
  val stateset_ty = mk_set_type statety
  val state_squared_set_ty = mk_set_type (mk_prod_ty (statety, statety))
  val com = mk_com_ty tyargs
in
  Const(@{const_name "LanguageCon.whileAnno"},
        stateset_ty --> stateset_ty --> state_squared_set_ty  --> com --> com)
end                                            


fun mk_seq_t tyargs = let
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "LanguageCon.com.Seq"}, comty --> (comty --> comty))
end

fun mk_cond_t tyargs = let
  val statety = hd tyargs
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "LanguageCon.com.Cond"},
        mk_set_type statety --> (comty --> (comty --> comty)))
end

(*David Sanan adding function to create await *)

fun mk_await_t tyargs = let
  val statety = hd tyargs
  val comty = mk_com_ty tyargs
  val ty_sargs = (take ((length tyargs)-1) tyargs)
  val scomty = mk_scom_ty ty_sargs
  val earg = Option_eventty
in
  Const(@{const_name "LanguageCon.com.Await"},
        mk_set_type statety --> (scomty --> (earg --> comty)))
end

fun mk_seq(s1, s2) = let
  val ty1 = type_of s1
            handle TYPE (msg, tys, tms) =>
                   raise TYPE ("mk_seq: "^msg, tys, tms)
  val tyargs = case ty1 of
                 Type(_, args) => args
               | _ => raise TYPE ("mk_seq: unexpected type for statement",
                                  [ty1], [s1])
in
  mk_seq_t tyargs $ s1 $ s2
end

fun list_mk_seq stmts =
    case stmts of
      [] => error "list_mk_seq: empty list as argument"
    | s::rest => List.foldl (fn (s', acc) => mk_seq(acc, s')) s rest

fun mk_throw_t tyargs =
    Const(@{const_name "LanguageCon.com.Throw"}, mk_com_ty tyargs)
fun mk_catch_t tyargs = let
  val comty = mk_com_ty tyargs
in                               
  Const(@{const_name "LanguageCon.Catch"}, comty --> (comty --> comty))
end

fun mk_switch (guard, cases) = let
  val cases_ty = type_of cases
  val cty = dest_list_type cases_ty
  val (_, sty) = dest_prod_ty cty
in
  Const(@{const_name "LanguageCon.switch"},
        type_of guard --> cases_ty --> sty) $ guard $ cases
end

fun mk_global_exn_var_update (thy : theory) (statety : Term.typ) : Term.term = let
    val exnvar_ty = (c_exntype_ty --> c_exntype_ty) --> (dest_statety2 statety) --> (dest_statety2 statety)
    val exnvar_name = suffix Record.updateN NameGeneration.global_exn_var    
in
    Const (Sign.intern_const thy exnvar_name, exnvar_ty)
end
(* David Sanan we add a wrap to update the state from the local variable updte*)
fun mk_var_update_state  (statety : Term.typ) upd_local ex_ty : Term.term = let
   val fvar = Free("f", (ex_ty --> ex_ty))
   val svar = Free("s", statety)
   val upd_local' = upd_local $ (Bound 1)
in
  mk_abs(fvar, mk_abs(svar, update_local statety upd_local' (Bound 0))) 
end

(*David Sanan we need to construct the update for the global state from the 
local variable modification *)
fun mk_creturn (thy : theory)
               (tyargs : Term.typ list)
               (statety : Term.typ)
               (updf : Term.term)
               (v : Term.term) : Term.term = let
    val exnvar = mk_global_exn_var_update thy statety 
    val exnvar' = (mk_var_update_state statety exnvar c_exntype_ty)
    val t_updf = (dest_statety1 (dest_statety1 (type_of updf)))
    val updf' = (mk_var_update_state statety updf t_updf)       
in  
    Const (@{const_name "CLanguage.creturn"},
           (type_of exnvar') --> (type_of updf') --> (type_of v) --> mk_com_ty tyargs
          ) $ exnvar' $ updf' $ v
end

(*David Sanan we need to construct the update for the global state from the 
local variable modification *)
fun mk_creturn_void (thy : theory)
                    (tyargs : Term.typ list)
                    (statety : Term.typ) = let
    val exnvar      = mk_global_exn_var_update thy statety
     val exnvar' = (mk_var_update_state statety exnvar c_exntype_ty)
in
    Const (@{const_name "CLanguage.creturn_void"},
           type_of exnvar' --> mk_com_ty tyargs) $ exnvar'
end


(*David Sanan we need to construct the update for the global state from the 
local variable modification *)
fun mk_cbreak_const (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var_update thy statety
    val exnvar' = (mk_var_update_state statety exnvar c_exntype_ty)
(*    val _ = writeln ("break statety:"^(@{make_string} statety)) *)
in
    Const (@{const_name "CLanguage.cbreak"}, (type_of exnvar') --> mk_com_ty tyargs)
end


(*David Sanan we need to construct the update for the global state from the 
local variable modification *)
fun mk_cbreak (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var_update thy statety
    val exnvar' = (mk_var_update_state statety exnvar c_exntype_ty)
in
    mk_cbreak_const thy tyargs statety $ exnvar'
end




fun mk_global_exn_var (thy : theory) (localty : Term.typ) : Term.term = let
    val exnvar_ty = localty --> c_exntype_ty
    val exnvar_name = NameGeneration.global_exn_var
in
    Const (Sign.intern_const thy exnvar_name, exnvar_ty)
end
(* David Sanan we add a wrap to update the state from the local variable updte*)
fun mk_glbal_exn_var_access (thy : theory) (statety : Term.typ) = 
let val localty = dest_statety2 statety
    val exnvar  = mk_global_exn_var thy localty 
    val access_loc = Const(@{const_name "snd"} , (statety--> localty))
    val svar = Free("s", statety)     
in 
  mk_abs(svar, exnvar $ (access_loc $ svar))
end
                               
fun mk_ccatchbrk (thy : theory)
                 (tyargs : Term.typ list)
                 (statety : Term.typ) = let
    val exnvar_access  = mk_glbal_exn_var_access thy statety    
in                                     
    Const (@{const_name "CLanguage.ccatchbrk"}, (type_of exnvar_access) --> mk_com_ty tyargs) $ exnvar_access
end

val div_0_error      = @{const "Div_0"}
val c_guard_error    = @{const "C_Guard"}
val safety_error     = @{const "MemorySafety"}
val shift_error      = @{const "ShiftError"}
val side_effect_error= @{const "SideEffects"}
val arraybound_error = @{const "ArrayBounds"}
val signed_overflow_error = @{const "SignedArithmetic"}
val dont_reach_error = @{const "DontReach"}
val unspecified_syntax_error = @{const "UnspecifiedSyntax"}
val ownership_error = @{const "OwnershipError"}

val unspecified_syntax_error1 = @{const "UnspecifiedSyntax"}
fun unspecified_syntax_error2 s = @{const "unspecified_syntax_error"}
    $ mk_string s



fun mk_guard_t tyargs =
    Const(@{const_name "LanguageCon.com.Guard"},
          List.nth(tyargs,2) --> mk_set_type (hd tyargs) -->
          mk_com_ty tyargs --> mk_com_ty tyargs)

fun mk_guard gdset gdtype com = let
  (* val _ = writeln ("com: "^(@{make_string}(type_of com))) *)
  val tyargs =
      case type_of com of
        Type(@{type_name "LanguageCon.com"}, args) => args
      | _ => raise Fail "mk_guard: command not of type \"LanguageCon.com\""
  
in
  mk_guard_t tyargs $ gdtype $ gdset $ com
end

fun mk_Spec(styargs, reln) =
    Const(@{const_name "LanguageCon.Spec"}, type_of reln --> mk_com_ty styargs) $
    reln


fun mk_specAnno pre body post = let
  val pre_type = type_of pre
  val (bty, stateset_ty) = dom_rng pre_type
  val bvar = case pre of
               Abs(nm, _, _) => nm
             | _ => raise Fail "mk_specAnno: pre not an abstraction"
  val body_type = type_of body
  val specAnno_ty =
      pre_type --> body_type --> pre_type --> pre_type -->
      #2 (dom_rng body_type)
in
  Const(@{const_name "LanguageCon.specAnno"}, specAnno_ty) $ pre $ body $ post $
       Abs(bvar, bty, Const("{}", stateset_ty))
end

fun mk_empty_INV ty = mk_collect_t ty $ Abs("x", ty, mk_arbitrary bool)

end
