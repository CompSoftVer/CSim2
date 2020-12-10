(* check values passed matches the sort of record parameters*)
(* check that the number of parameters is the number of the set of 
   variable types used by the record and its ancestors *)
(* check that every field, after substituting the type is of the required type *)

open Record

val make_conj = @{mk_term "?P \<and> ?Q" (P, Q)}

val make_conj_list = foldr1 make_conj;

fun rec_args_string args full_rec_name = 
let
val rec_args_types = args |> map (fn e => (fst e)^"::"^implode (snd e))
in
 "("^commas rec_args_types^")"^full_rec_name
end

fun record_type ctxt args full_rec_name =
  Proof_Context.read_typ ctxt (rec_args_string args full_rec_name)


fun get_setters_getters recd thy =
 let      
  val heap_fields =
      Record.get_recT_fields thy recd |> fst              
  val getters = map (fn (a,b) => (a, recd --> b)) heap_fields
  val setters = map (fn (a,b) => (a ^ Record.updateN, (b --> b) --> (recd --> recd))) heap_fields  
 in
  (setters,getters)
 end;
 
fun get_setters_getters1 recd thy =
 let      
  val heap_fields =
      Record.get_recT_fields thy recd |> fst              
  val getters = map (fn (a,b) => a) heap_fields
  val setters = map (fn (a,b) => (a ^ Record.updateN, (b --> b) --> (recd --> recd))) heap_fields  
 in
  (setters,getters)
 end;

fun member _ [] = false
    |member x L =
        if x=hd(L) then true
        else member x (tl(L));   
        
fun map_fst l = 
    map fst l  
 
fun add_uniques l1 l2 = 
    fold (fn e => fn l => if (member e l) then l else (e::l)) l1 l2
    
fun get_types_sorts hyer = 
   let 
     val vars_parents = fold 
                         (fn x => fn l => 
                            add_uniques (map_fst (snd x)) l)  
                           (take ((length hyer) - 1) hyer)  []                          
     val vars_rec =  map_fst (snd (List.last hyer))
     val types_ext = filter (fn e => not (member e vars_parents)) vars_rec
   in types_ext   
end;
  (* todo create a TFree using the name and the sort (fst (fst e) and (snd (fst e)) *)
  fun rec_variables_type hyer = 
     nth hyer ((length hyer)-1) |> snd |> map (fn e => (fst e, snd e)) 
  
  fun get_sorts typs_sorts = map (fn e => snd e) 
      (get_types_sorts typs_sorts)
  fun get_typs typs_sorts = map (fn e => fst e) 
      (get_types_sorts typs_sorts)
       
fun fresh_name L =
  let fun fresh_name_acc L acc = if member acc L then (fresh_name_acc L (acc^"a"))
                                 else acc
  in 
    fresh_name_acc L "a"
  end;
  
fun remove_prime L =  map (fn x => String.substring (x,1,(String.size x - 1))) L

fun fresh_type L = "'" ^ fresh_name (remove_prime L)

fun read_types NONE _ = []
   |read_types (SOME types) ctxt = Syntax.read_typs ctxt types  

fun to_map_fun L =   
   (fn t => 
       let 
          val fil= filter (fn a => (fst a) = t) L in 
          if (fil = []) then (TFree t)
          else (hd fil)|> snd
       end
    )
    
fun to_l str sort =   
   (fn t => 
        if (fst t) = str then (TFree (str,sort))
        else (TFree t)         
    )
    
fun to_map_tfree str sort =    
  (fn t =>  map_type_tfree (to_l str sort) t)  

fun change_tfrees pairs typ =
  let fun mod_tfree pairs (str,srt) =
       let val pair_str = (filter (fn e => fst e =  str) pairs)
                       val str' = the_single pair_str |> snd  in                   
                   TFree (str',srt)
       end
  in map_type_tfree (mod_tfree pairs) typ
end
  
fun get_last_sub_string sim str =space_explode sim str |> (fn str => nth str ((length str) -1)) 


fun def_record_zero rec_extension (rec_info:info) ctxt =
let    
    val n_zeros = length (#fields rec_info) + 1
    val zeros = replicate n_zeros (Const(@{const_name zero_class.zero},dummyT))
    val rec_ext =  Syntax.read_term ctxt rec_extension 
    
   val frees = Term.add_tfree_names rec_ext []    
    val new_rec = map_types (to_map_tfree (nth frees 0) @{sort zero}) rec_ext
    val rec_ext_func = list_comb (new_rec,zeros)
    val not_full_name = get_last_sub_string "." rec_extension  
    val checked_term = Syntax.check_term ctxt rec_ext_func    
    val (_,thm, ctxt) = Utils.define_const_args ("zero_"^not_full_name) false checked_term [] ctxt   
in
  (thm, ctxt) 
end 

fun record_type_inst p hier   = 
  let 
    fun parent_types p hier = 
       nth (filter (fn e => fst e = p) hier) 0 |> snd |> map snd
    
  in  Type (p, parent_types p hier)
end

 fun get_new_sort frees sort =  
      frees 
      |> fresh_type 
      |> (fn new_type => (new_type,sort))  

 
fun free_terms ctxt trm =
let 
  val free_types = Term.add_tfree_names trm []
  val types = replicate (length free_types) ["type"]
  val fresh_types = Variable.invent_types types ctxt |> fst |> map fst    
  in 
    Utils.zip free_types fresh_types |> 
      (fn zip => map_types (change_tfrees zip) trm)
end 

fun def_record_plus full_rec_name hier (rec_info:info)  ctxt =
let   

(* args contains the variable types to the record in the format (string*sort) *)    
   val args = #args rec_info   
   val fields = #fields rec_info
   (* get the type of the extension record for variables types *)
   val rec_extension = (get_last_sub_string "." full_rec_name) |> (fn  name => full_rec_name ^ "."  ^ name ^ "_ext")
   (* record type for record_scheme *)
   fun rec_type_scheme ctxt = record_type ctxt (args@[(get_new_sort (map_fst args) @{sort sep_algebra})]) (full_rec_name^"_scheme")
   
   (* record type for record_ext *)
   val type_more = (get_new_sort (map_fst args) @{sort sep_algebra})  
   val free_types =  fold (fn e => fn l => Term.add_tfree_namesT (snd e) l) fields []                     
   val types = (filter (fn x => member (fst x) free_types) args) @ [type_more]   
   fun rec_type ctxt = record_type ctxt types rec_extension
   
   (* get setters/getters of the record *)
   val f_getters = get_setters_getters (rec_type_scheme ctxt) (Proof_Context.theory_of ctxt)
                    |> snd |> (fn getters => drop ((length getters)-(length fields)) getters)
   (* val rec_ext =  Syntax.read_term ctxt rec_extension
  
  val frees = Term.add_tfree_names rec_ext []    
  val new_rec = map_types (to_map_tfree (nth frees 0) @{sort sep_algebra}) rec_ext
  *)
  val rec_ext_type =   (map snd fields)@[(TFree type_more)] ---> (rec_type ctxt)
  val rec_ext = Const(rec_extension, rec_ext_type)
  
  val p1 = Free ("p1",rec_type ctxt);
  val p2 = Free ("p2",rec_type ctxt);
  val not_full_name = get_last_sub_string "." rec_extension  
  val parent = #parent rec_info
  
  fun get_arg pr parent  = 
  let
   fun arg p pr = 
    let 
     val const_parent  = Const ("Hilbert_Choice.Eps", dummyT) $
                       Abs ("y",(record_type_inst p hier), Const ("HOL.True", @{typ "bool"}))
     fun extend_rec pr = Const (p^".extend",dummyT) $ const_parent $ pr
    in (extend_rec pr) end    
  in case parent of NONE => pr
                |SOME (_,l) =>  arg l pr
  end     
  val plus_term =  Const (@{const_name "plus"},dummyT)
  fun get_rec upd pr = Const (fst upd,dummyT) $ (get_arg pr parent)
  fun plus upd = plus_term $ (get_rec upd p1) $(get_rec upd p2)  
  val rec_ext_func = (rec_ext,(map plus (f_getters@[(full_rec_name^".more",dummyT)]))) 
                     |> list_comb
                     |> free_terms ctxt 
                     |> Syntax.check_term ctxt  
  val (_,thm, ctxt) =Utils.define_const_args ("plus_"^not_full_name) false rec_ext_func [("p1",dummyT),("p2",dummyT)] ctxt 
in
  (thm, ctxt)  
end

fun def_record_sep_disj full_rec_name hier (rec_info:info)  ctxt =
let   

(* args contains the variable types to the record in the format (string*sort) *)    
   val args = #args rec_info   
   val fields = #fields rec_info
   (* get the type of the extension record for variables types *)
   val rec_extension = (get_last_sub_string "." full_rec_name) |> (fn  name => full_rec_name ^ "."  ^ name ^ "_ext")
   (* record type for record_scheme *)
   fun rec_type_scheme ctxt = record_type ctxt (args@[(get_new_sort (map_fst args) @{sort sep_algebra})]) (full_rec_name^"_scheme")
   
   (* record type for record_ext *)
   val type_more = (get_new_sort (map_fst args) @{sort sep_algebra})  
   val free_types =  fold (fn e => fn l => Term.add_tfree_namesT (snd e) l) fields []                     
   val types = (filter (fn x => member (fst x) free_types) args) @ [type_more]   
   fun rec_type ctxt = record_type ctxt types rec_extension
   
   (* get setters/getters of the record *)
   val f_getters = get_setters_getters (rec_type_scheme ctxt) (Proof_Context.theory_of ctxt)
                    |> snd |> (fn getters => drop ((length getters)-(length fields)) getters)
   (* val rec_ext =  Syntax.read_term ctxt rec_extension
  
  val frees = Term.add_tfree_names rec_ext []    
  val new_rec = map_types (to_map_tfree (nth frees 0) @{sort sep_algebra}) rec_ext
  *)
  
  
  val p1 = Free ("p1",rec_type ctxt);
  val p2 = Free ("p2",rec_type ctxt);
  val not_full_name = get_last_sub_string "." rec_extension  
  val parent = #parent rec_info
  
  fun get_arg pr parent  = 
  let
   fun arg p pr = 
    let 
     val const_parent  = Const ("Hilbert_Choice.Eps", dummyT) $
                       Abs ("y",(record_type_inst p hier), Const ("HOL.True", @{typ "bool"}))
     fun extend_rec pr = Const (p^".extend",dummyT) $ const_parent $ pr
    in (extend_rec pr) end    
  in case parent of NONE => pr
                |SOME (_,l) =>  arg l pr
  end     

  val disjoint_term =  Const (@{const_name "sep_disj"},dummyT)
  fun get_rec upd pr = Const (fst upd,dummyT) $ (get_arg pr parent)
  fun disjoint upd = disjoint_term $ (get_rec upd p1) $(get_rec upd p2) 
 
  val conj_func = (map disjoint (f_getters@[(full_rec_name^".more",dummyT)]))                  
                  |> Syntax.check_terms ctxt  
                  |> make_conj_list
                  |> free_terms ctxt
  
  val (_,thm, ctxt) =Utils.define_const_args ("sep_disj_"^not_full_name) false conj_func [("p1",dummyT),("p2",dummyT)] ctxt 

in
  (thm, ctxt)  
end

fun tact thmspp thmsp thms ctxt =
  let 
val type_encs =
  ["erased",
   "poly_guards",
   "poly_guards?",
   "poly_guards??",
   "poly_guards@",
   "poly_tags",
   "poly_tags?",
   "poly_tags??",
   "poly_tags@",
   "poly_args",
   "poly_args?",
   "raw_mono_guards",
   "raw_mono_guards?",
   "raw_mono_guards??",
   "raw_mono_guards@",
   "raw_mono_tags",
   "raw_mono_tags?",
   "raw_mono_tags??",
   "raw_mono_tags@",
   "raw_mono_args",
   "raw_mono_args?",
   "mono_guards",
   "mono_guards?",
   "mono_guards??",
   "mono_tags",
   "mono_tags?",
   "mono_tags??",
   "mono_args"]
     val thms = [snd thms]@ [fst (fst thms)] @ [snd (fst thms)]@thmsp   
   val ctxt' = ctxt addsimps thms 
   val ctxt'' = ctxt addsimps (thms @ (@{thms sep_add_left_commute sep_disj_commute sep_add_assoc sep_add_commute 
                                                        sep_disj_addI1 zero_fun_def plus_fun_def sep_disj_fun_def 
                                                         prod_def}))
   val ctxt''' = ctxt addsimps (thms @ (@{thms  sep_disj_commute  sep_add_commute sep_add_assoc prod_def sep_disj_addI1}))
   val ctxt3' = ctxt addsimps (thms @ (@{thms sep_add_assoc }))
   val ctxt4 = ctxt addsimps (thms @ (@{thms prod_def sep_disj_addI1}))
  in
   case thmsp of [] => 
     Class.standard_intro_classes_tac ctxt'' [] 
     THEN asm_full_simp_tac ctxt' 1
     THEN asm_full_simp_tac ctxt'' 1
     THEN asm_full_simp_tac ctxt' 1     
     THEN asm_full_simp_tac ctxt''' 1
     THEN asm_full_simp_tac ctxt3' 1
     THEN asm_full_simp_tac ctxt' 1
     THEN Meson_Tactic.meson_general_tac ctxt' [@{thm sep_disj_addD}] 1 
     THEN asm_full_simp_tac ctxt4 1
   | _ =>
     Class.standard_intro_classes_tac ctxt'' [] 
     THEN asm_full_simp_tac ctxt' 1
     THEN asm_full_simp_tac ctxt'' 1
     THEN asm_full_simp_tac ctxt' 1
     THEN Metis_Tactic.metis_tac type_encs ATP_Problem_Generate.combsN ctxt thmspp 1
     THEN asm_full_simp_tac ctxt''' 1
     THEN asm_full_simp_tac ctxt''' 1
     THEN asm_full_simp_tac ctxt' 1
     THEN Meson_Tactic.meson_general_tac ctxt' [@{thm sep_disj_addD}] 1 
     THEN asm_full_simp_tac ctxt4 1
  
end

fun proof_sep_record rec_name types b thy = 
   let
   val full_rec_name = Sign.full_name thy (Binding.name rec_name)
   val info = (Record.the_info thy full_rec_name)
   val fields = (#fields info)
   val args = (#args info)       
   
   val hier  =                    
     (*this already checks the passed arguments are well-formed wrt 
     the record's variable types' sort*)           
       Record.get_hierarchy thy (full_rec_name,read_types types @{context })   
      
   val check_record_constrains   =
   let   (* record info *)                 
     (* bound record type variables with passed types*)         
     val change_rec_fields = 
       (rec_variables_type hier, 
       fields)
        |-> (fn rec_variable_types => 
               map (fn f => (map_type_tfree (to_map_fun rec_variable_types) (snd f))) )                         
     (* fields that are separation algebra in the extension*)
     val fields_sep_algebra = filter (fn e => Sign.of_sort thy (e, @{sort sep_algebra})) change_rec_fields
     in ( fields_sep_algebra =  change_rec_fields)
   end
   
   val rec_extension = (get_last_sub_string "." full_rec_name) |> (fn  name => full_rec_name ^ "."  ^ name ^ "_ext")
   
   val free_types = fold (fn e => fn l => Term.add_tfree_namesT (snd e) l) fields []
   val parent_thm = case #parent info of NONE => []
                        | SOME v => snd v |> Record.the_info thy |> #defs |> (fn l => nth l 2) |> single
in
   if check_record_constrains   then    
     thy 
     |> Class.instantiation ([rec_extension], (filter (fn x => member (fst x) free_types) args) @[get_new_sort (map_fst args) @{sort sep_algebra}], @{sort sep_algebra})
     |> def_record_zero rec_extension info
     ||>> def_record_plus full_rec_name hier  info 
     ||>> def_record_sep_disj  full_rec_name hier  info  
     |> (fn (thm_tuple,ctxt) => (tact ((#select_convs info)@(single (#ext_surjective info))) 
                                      parent_thm thm_tuple,ctxt) 
          |-> Class.prove_instantiation_instance)     
   else error "not all fields are sep_algebra"
   (*   thy |> Class.instantiation (["rec_name"],[("'a", @{sort sep_algebra})], @{sort sep_algebra})*) 
  end;

val p = Parse.text -- Scan.option (Scan.repeat1 Parse.type_const)
val q = (fn (x,xs) =>  (proof_sep_record x xs true) |> 
                 Toplevel.begin_local_theory false );
                                    
val q1 = (fn (x,xs) =>  (proof_sep_record x xs) )   
val z =  (p >> q)
val z1 =  (p >> q1)
val z2 = Toplevel.theory
val b =
  Outer_Syntax.command @{command_keyword sep_record} "proof separation on a record" 
    (Parse.text -- Scan.option (Scan.repeat1 Parse.type_const) >> 
         (fn (x,xs) =>  (proof_sep_record x xs true) |> Toplevel.begin_local_theory false ))

val a1 = (Toplevel.exit o Toplevel.end_local_theory o Toplevel.close_target o
        Toplevel.end_proof (K Proof.end_notepad))

val c =
  Outer_Syntax.command @{command_keyword kk} "proof separation on a record" 
     (Parse.text -- Scan.option (Scan.repeat1 Parse.type_const) >> 
         (fn (x,xs) =>  (proof_sep_record x xs true) |> 
            Toplevel.begin_local_theory true #> (Toplevel.exit o Toplevel.end_local_theory o Toplevel.close_target o
        Toplevel.end_proof (K Proof.end_notepad)) ))
