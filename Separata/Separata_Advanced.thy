(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory Separata_Advanced
imports Main Separata
begin

declare [[ML_print_depth=1000]] 

ML {*

val h_typ = @{typ "'a::heap_sep_algebra"};;
val sep_typ = @{typ "'a::heap_sep_algebra \<Rightarrow> bool"};;
val tern_typ = @{typ "'a::heap_sep_algebra \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"};;
val quant_typ = @{typ "('a::heap_sep_algebra \<Rightarrow> bool) \<Rightarrow> bool"};;
val disj_typ = @{typ "'a::heap_sep_algebra \<Rightarrow> 'a \<Rightarrow> bool"}
val bin_bool_typ = @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"};;
val prop_typ = @{typ "bool \<Rightarrow> prop"};;
val pureimp_typ = @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"};;
val ulo_typ = @{typ "bool \<Rightarrow> bool"};;
val bso_typ = @{typ "('a::heap_sep_algebra \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"};;

val true_term = @{term "True"};;
val emp_heap = @{term "0"};;
val null_heap = @{term "hnull"};;

(* Break the goal as a term of "Pure.imp" props into a list of terms. 
   That is, assume the goal is of the form A \<Longrightarrow> B \<Longrightarrow> ... \<Longrightarrow> C,
   break it into a list of terms [A,B,...,C]. *)
fun terms_of_prem (Const ("Pure.all", _) $ t) = terms_of_prem t
|terms_of_prem (Abs (_, _, t)) = terms_of_prem t
|terms_of_prem (Const ("Pure.imp", _) $ t1 $ t2) = (terms_of_prem t1)@(terms_of_prem t2)
|terms_of_prem (Const ("HOL.Trueprop", _) $ t) = terms_of_prem t
|terms_of_prem t = [t];; 

(* Print a list of terms. *)
fun print_term_list (t::tx) = (writeln (@{make_string} t);writeln "\n";print_term_list tx)
|print_term_list [] = writeln "";

(* Test if a term is a ternary relational atom. *)
fun is_tern (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  _) $ _ $ _ $ _) = true
|is_tern _ = false;;

(* Get the root of a ternary relational atom. *)
fun root_of_tern (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  _) $ _ $ _ $ r) = r
| root_of_tern _ = null_heap;;

(* Get the left child of a ternary relational atom. *)
fun lchd_of_tern (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  _) $ c $ _ $ _) = c
| lchd_of_tern _ = null_heap;;

(* Get the right child of a ternary relational atom. *)
fun rchd_of_tern (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  _) $ _ $ c $ _) = c
| rchd_of_tern _ = null_heap;;

(* Test if a ternary relational atom has the specified root. *)
fun root_tern root tern = 
  case tern of (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  _) $ _ $ _ $ r) => (
    case (r,root) of ((Free (str1,_)),(Free (str2,_))) => if str1 = str2 then true else false
    |((Const (str1,_)),(Free (str2,_))) => if str1 = str2 then true else false
    |((Free (str1,_)),(Const (str2,_))) => if str1 = str2 then true else false
    |((Const (str1,_)),(Const (str2,_))) => if str1 = str2 then true else false
    |_ => false) 
  |_ => false;;

(* Given three heaps (terms of type "'a"), return a ternary relational atom. *)
fun mk_tern h1 h2 h0 = (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  tern_typ) $ h1 $ h2 $ h0)

(* Get the children of a ternary relational atom. *)
fun get_chd tern = 
  case tern of (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  _) $ c1 $ c2 $ _) => [c1,c2]
  |_ => [];;

(* Get the root of the ternary relational atom if it has the specified children. 
If this relational atom doesn't have the specified children, return null_heap. 
Note that we take commutativity into consideration there. *)
fun root_of_children (Free (str1', _)) (Free (str2', _)) 
  (Const ("Separata.heap_sep_algebra_class.tern_rel", 
  _) $ Free (str1, _) $ Free (str2, _) $ hp) = 
  if str1 = str1' andalso str2 = str2' then hp
  else if str1 = str2' andalso str2 = str1' then hp
  else null_heap
|root_of_children _ _ _ = null_heap;;

(* Given a root and a list of terms (the assumptions), find the maximal
list of leaves of the specified root. *)
fun get_maximal_leaves root terms = 
  let fun get_maximal_leaves_internal root terms all_terms =
    case terms of (t::ts) => (
      if root_tern root t then 
        let val children = get_chd t in
        (* The if part shouldn't happen because root_tern is true means 
           t is proper a ternary relational atom and children should be 
           a list of length 2. *)
        if List.length children = 0 then [] 
        else (get_maximal_leaves_internal (List.hd children) all_terms all_terms)@
             (get_maximal_leaves_internal (List.hd (List.tl children)) all_terms all_terms)
        end    
      else get_maximal_leaves_internal root ts all_terms
    )
    |_ => [root]
  in
  get_maximal_leaves_internal root terms terms
  end;;

(* Given a root and a list of terms (the assumptions), find the maximal tree
of the specified root. *)
fun get_maximal_tree root terms = 
  let fun get_maximal_tree_internal root terms all_terms =
    case terms of (t::ts) => (
      if root_tern root t then 
        let val children = get_chd t in
        (* The if part shouldn't happen because root_tern is true means 
           t is proper a ternary relational atom and children should be 
           a list of length 2. *)
        if List.length children = 0 then []
        else [t]@(get_maximal_tree_internal (List.hd children) all_terms all_terms)@
             (get_maximal_tree_internal (List.hd (List.tl children)) all_terms all_terms)
        end
      else get_maximal_tree_internal root ts all_terms 
    )
    |_ => []
  in
  get_maximal_tree_internal root terms terms
  end;;

(* Delete the Bound 0 at the end of abstractions. *)
fun del_bound tm =
  case tm of t1 $ t2 => (
    case t2 of (Bound _) => del_bound t1
    |_ => (del_bound t1) $ (del_bound t2)
  )
  |_ => tm;;

(* Delete the free variables of type "'a" in a term. 
This variable only occurs at the end of a composed term. *)
fun del_heaps tm =
  case tm of t1 $ t2 => (
    case t2 of Free (_,(TFree ("'a",_))) => del_heaps t1
    |Free (_,(TFree ("'b",_))) => del_heaps t1 (* This case is not needed if the formula is well formed. *)
    |_ => (del_heaps t1) $ (del_heaps t2)      
  )    
  |_ => tm;;

(* Delete the abstractions in a term. *)
fun del_abs tm = 
  case tm of t1 $ t2 =>
    (del_abs t1) $ (del_abs t2)
  |Abs (_,_,t) => (del_abs t)
  |_ => tm;;

(* Test if two formulae are a match. 
Note that the two input formulae should already been processed 
by del_abs -> del_bound -> del_heaps. *)
fun match_form lform form = 
  case (lform,form) of 
   (Const ("HOL.True", _),Const ("HOL.True", _)) => true
  |(Const ("HOL.False", _),Const ("HOL.False", _)) => true
  |(Const ("Separation_Algebra.sep_algebra_class.sep_empty", _),
    Const ("Separation_Algebra.sep_algebra_class.sep_empty", _)) => true
  |(Free (str1, _), Free (str2, _)) => 
    if str1 = str2 then true else false
  |(Const ("HOL.Not", _) $ lf, Const ("HOL.Not", _) $ f) =>
    match_form lf f
  |(Const ("HOL.conj", _) $ lf1 $ lf2, Const ("HOL.conj", _) $ f1 $ f2) =>
    (match_form lf1 f1) andalso (match_form lf2 f2)
  |(Const ("HOL.disj", _) $ lf1 $ lf2, Const ("HOL.disj", _) $ f1 $ f2) =>
    (match_form lf1 f1) andalso (match_form lf2 f2)
  |(Const ("HOL.implies", _) $ lf1 $ lf2, Const ("HOL.implies", _) $ f1 $ f2) =>
    (match_form lf1 f1) andalso (match_form lf2 f2)
  |(Const ("HOL.Ex", _) $ lf, Const ("HOL.Ex", _) $ f) =>
    (match_form lf f)
  |(Const ("HOL.All", _) $ lf, Const ("HOL.All", _) $ f) =>
    (match_form lf f)
  |(Const ("Separation_Algebra.sep_algebra_class.sep_conj", _) $ f1 $ f2,
    Const ("Separation_Algebra.sep_algebra_class.sep_conj", _) $ f3 $ f4) =>
    (match_form f1 f3) andalso (match_form f2 f4)
  |(Const ("Separation_Algebra.sep_algebra_class.sep_impl", _) $ f1 $ f2,
    Const ("Separation_Algebra.sep_algebra_class.sep_impl", _) $ f3 $ f4) =>
    (match_form f1 f3) andalso (match_form f2 f4)
  |_ => false;;

(* Normalise a formula by removing abstractions, bounds, and heaps. 
Note that applying norm_form a second time on a term doesn't change anything. *)
fun norm_form form = del_heaps (del_bound (del_abs form));;

(* Given a labelled formula (F l) and a formula F' (both as terms, the former
is of type bool, the latter is of type 'a \<Rightarrow> bool), check if F = F'. *)
fun is_form lform form = match_form (del_heaps (del_bound (del_abs lform))) 
  (del_bound (del_abs form));;

(* Given a formula and a list of assumptions (labelled formula), return
a labelled formula if it's a match of the input formula.*)
fun has_form (t::tx) form = if is_form t form then t else has_form tx form
|has_form [] _ = null_heap;;

(* Given a term of free variable that represents a label/heap, return the 
corresponding string. *)
fun str_of_fvar (Free (str, _)) = str
|str_of_fvar _ = "";; 

(* Given two labels (terms) for children, generate a ternary relational
atom with the root numbered with n. The root will be called evn 
where n is the number input. *)
fun gen_tern_root c1 c2 n = Const ("HOL.Ex", quant_typ) $
  Abs (("ev"^(string_of_int n)), h_typ,
    Const ("Separata.heap_sep_algebra_class.tern_rel", tern_typ) $
      Free ((str_of_fvar c1), h_typ) $ Free ((str_of_fvar c2), h_typ) $ Bound 0);;

(* Given two heaps (terms of type "'a"), and a list a assumptions (terms of type "bool"),
find the parent of the two heaps. Return null_heap if can't find any. *)
fun get_root_tl c1 c2 (t::tx) =
  let val h = root_of_children c1 c2 t in
  if h = null_heap then get_root_tl c1 c2 tx
  else h
  end
|get_root_tl _ _ [] = null_heap;;

(* Given a term representing a labelled formula (A h), return the
label. If fails, return null_heap. 
Note that we assume this formula is not negated. That is, it's not 
of the form (\<not> A h). *)
fun heap_of_lform lf = 
  case lf of _ $ t2 => heap_of_lform t2
  |Abs (_, _, t) => heap_of_lform t
  |Free (_,(TFree ("'a",_))) => lf
  |Free (_,(TFree ("'b",_))) => lf (* This case is not needed if the formula is well formed. *)
  |Bound _ => lf 
  |_ => null_heap;;

(* Given a formula (as a term) and a list of terms (assumptions)
find the heap where the formula is true. Also return the involved 
ternary relational atoms. Return (h,terns,n) if h is the heap, terns
is the list of relational atoms, and n is the number of created 
quantified variables. When fail, return (null_heap,[],0). 
The last parameter n is the number of previsouly generated 
quantified variables. 
Note that form should already been processed 
by del_abs -> del_bound -> del_heaps.
Also note that this algorithm doesn't consider magic wand and truth. *)
fun findheap form terms n = 
  let val lf = has_form terms form in (* form is in terms. *)
  if lf <> null_heap then ((heap_of_lform lf),[],n)
  else (* form isn't in terms. Break form down. *)
    case form of 
      Const ("Separation_Algebra.sep_algebra_class.sep_empty", _) => (emp_heap,[],0)
    |Const ("HOL.Not", _) $ f => findheap f terms n
    |Const ("HOL.Ex", _) $ f => findheap f terms n
    |Const ("HOL.All", _) $ f => findheap f terms n
    |Const ("HOL.conj", _) $ f1 $ f2 => 
      let val (h,tl,n) = findheap f1 terms n in
      if h = null_heap then findheap f2 terms n 
      else (h,tl,n)
      end
    |Const ("HOL.disj", _) $ f1 $ f2 => 
      let val (h,tl,n) = findheap f1 terms n in
      if h = null_heap then findheap f2 terms n 
      else (h,tl,n)
      end
    |Const ("HOL.implies", _) $ f1 $ f2 => 
      let val (h,tl,n) = findheap f1 terms n in
      if h = null_heap then findheap f2 terms n  
      else (h,tl,n)
      end
    |Const ("Separation_Algebra.sep_algebra_class.sep_conj", _) $ f1 $ f2 =>
      let val (h1,tl1,n1) = findheap f1 terms n in
      if h1 <> null_heap then
        let val (h2,tl2,n2) = findheap f2 terms n1 in
        if h2 <> null_heap then
          let val hp = get_root_tl h1 h2 terms in
          if hp <> null_heap then (hp,tl1@tl2@[mk_tern h1 h2 hp],n2+1)
          else (Bound n2,tl1@tl2@[Const ("Separata.heap_sep_algebra_class.tern_rel", 
            tern_typ) $ h1 $ h2 $ Bound n2],n2+1)  
          end
        else (null_heap,[],0)
        end
      else (null_heap,[],0) 
      end
    |_ => (null_heap,[],0)
  end;;

(* Given a list of terms, make conjunctions of them. 
Return null_heap if the list is empty. *)
fun mk_conj terms = 
  let fun mk_conj_internal terms = 
    if (List.tl terms) = [] then List.hd terms
    else Const ("HOL.conj", bin_bool_typ) $ (List.hd terms) $
     (mk_conj_internal (List.tl terms))
  in
  if (List.length terms) = 0 then null_heap
  else mk_conj_internal terms
  end;;

(* Given a term, and a number of quantifiers to be generated,
return a term with the specified quantifiers around the term. 
The term should already contain the Bound n sub-terms. *)
fun mk_quant term pn n = 
  if n > 1 then Const ("HOL.Ex", quant_typ) $
     Abs ("ev"^(string_of_int (pn+n)), h_typ, (mk_quant term pn (n-1)))
  else if n = 1 then Const ("HOL.Ex", quant_typ) $
     Abs ("ev"^(string_of_int (pn+1)), h_typ, term)
  else term;;

(* Given a term representing a labelled negated star formula (\<not>(A ** B) h0)
and a list of terms as assumptions, return a term that represents the ternary 
relational atoms that are required to prove the labelled negated star formula. 
If the algorithm fails, return terms. *)
fun starr_interm_gen fvg fm terms = (
  case fm of Const ("HOL.Not", _) $
    (Const ("Separation_Algebra.sep_algebra_class.sep_conj", _) $
    f1 $ f2 $ h) => 
    let val (h1,tl1,n1) = findheap (del_heaps (del_bound (del_abs f1))) terms (List.length fvg);
        val (h2,tl2,n2) = findheap (del_heaps (del_bound (del_abs f2))) terms n1;
    in
    if h1 <> null_heap andalso h2 <> null_heap then   
      (mk_quant (mk_conj (tl1@tl2@[Const ("Separata.heap_sep_algebra_class.tern_rel", 
      tern_typ) $ h1 $ h2 $ h])) (List.length fvg) (n2-(List.length fvg)))
    else null_heap
    end
  |_ => null_heap);;        

(* Given a string representing a term 
   and a list of terms. Return a term that matches the string. *)
fun match_term_str str ctxt (t::tx) = 
  if Syntax.string_of_term ctxt t = str then t
  else match_term_str str ctxt tx
|match_term_str _ _ [] = @{term False};;

fun string_of_term_conv (Const (s,_)) _ = s
|string_of_term_conv (Free (s,_)) _ = s
|string_of_term_conv (Var ((s,_),_)) _ = s (* We don't use Var *)
|string_of_term_conv (Bound i) fvs = 
  if ((List.length fvs) - i - 1) < 0 then (* In rare cases, this may generate a "wrong" intermediate step, but the proof is still valid. The "wrong" intermediate step doesn't help proof search though. *)
   "" (* This shouldn't happen. But in case this happens, it will cause a type match error message for the created string. *)
  else List.nth (fvs,((List.length fvs) - i - 1))
|string_of_term_conv (Abs (s,_,t)) fvs = "(\<lambda> "^s^". ("^(string_of_term_conv t fvs)^"))"
|string_of_term_conv (t1 $ t2) fvs = case (t1,t2) of 
   ((Const ("HOL.Ex",_)),_) => (string_of_term_conv t1 fvs)^" "^(string_of_term_conv t2 fvs)^""
  |((Const ("HOL.All",_)),_) => (string_of_term_conv t1 fvs)^" "^(string_of_term_conv t2 fvs)^""
  |_ => 
    let val str1 = case t1 of (Const _) => (string_of_term_conv t1 fvs)
                          |(Free _) => (string_of_term_conv t1 fvs)
                          |(Bound _) => (string_of_term_conv t1 fvs)
                          |_ => "("^(string_of_term_conv t1 fvs)^")";
        val str2 = case t2 of (Const _) => (string_of_term_conv t2 fvs)
                          |(Free _) => (string_of_term_conv t2 fvs)
                          |(Bound _) => (string_of_term_conv t2 fvs)
                          |_ => "("^(string_of_term_conv t2 fvs)^")"
    in
    str1^" "^str2
    end;;

(* Input a term of a quantified formula of conjunctions of 
  ternary relational atoms. Output the list of quantified 
  variables. The last quantified variable in the list corresponds 
  to Bound 0, the first quantified variable corresponds to Bound n if 
  there are n+1 quantified variables. *)
fun get_bvl (Const ("HOL.Ex", _) $ Abs (s,_,t)) = s::(get_bvl t) 
|get_bvl (Const ("HOL.All", _) $ Abs (s,_,t)) = s::(get_bvl t)
|get_bvl (Const ("Pure.all", _) $ Abs (s,_,t)) = s::(get_bvl t)
|get_bvl (Const _) = []
|get_bvl (Free _) = []
|get_bvl (Var ((s,_),_)) = [s]
|get_bvl (Bound _) = []
|get_bvl (Abs (_,_,t)) = get_bvl t
|get_bvl (t1 $ t2) = (get_bvl t1)@(get_bvl t2);;

fun str_of_term fvg t = string_of_term_conv t ((get_bvl t)@fvg);;

(* An intermediate tactic for *R. 
  The inputs are a term representing a *R formula and 
  a thm representing the current subgoal. 
  Return a tactic. *)
fun starr_interm_tac fm ctxt fvg sg = 
  let val prems = Thm.prems_of sg;
      val ts = if prems = [] then [] else terms_of_prem (List.hd prems);
  in
  if fm = @{term False} then no_tac sg
  else     
    let val interm = starr_interm_gen fvg fm ts; 
        val interm_str = str_of_term fvg interm;        
    in
    if interm = null_heap orelse interm_str = "" then no_tac sg
    else (Rule_Insts.subgoal_tac ctxt interm_str [] 1) sg
    end
  end;;

(* Take a subgoal of type term as input, find a *R formula (F h) for the 
starr_interm_tac. Return the labelled formula as a term. 
Return null_heap if can't find any. *)
fun find_starr_int_fm sg = 
  let val ts = terms_of_prem sg;
      val tnum = List.length ts;
      val penult_term = if tnum > 2 then List.nth (ts,(tnum - 2)) else null_heap;
      val fm = (case penult_term of (Const ("Separata_Advanced.starr_int_applied", _) $ h $
            (Const ("Separation_Algebra.sep_algebra_class.sep_conj",_) $
            a $ b)) => (Const ("HOL.Not", ulo_typ) $
          (Const ("Separation_Algebra.sep_algebra_class.sep_conj",bso_typ) $
          a $ b $ h))
          |_ => null_heap);                
  in
  fm
  end;;

(* Wrapping things up. *)
fun starr_interm_tac_wrapper ctxt sg = 
  let val prems = Thm.prems_of sg;
      val this_goal = if prems = [] then null_heap else List.hd (Thm.prems_of sg);      
      val f = find_starr_int_fm this_goal;
      val fvg = get_bvl this_goal;
  in
  if f = null_heap then no_tac sg
  else starr_interm_tac f ctxt fvg sg
  end;;

*}

method_setup starr_interm = {*
  (*concrete syntax like "clarsimp", "auto" etc.*)
  Method.sections Clasimp.clasimp_modifiers >>
    (*Isar method boilerplate*)
    (fn _ => fn ctxt => SIMPLE_METHOD (CHANGED (starr_interm_tac_wrapper ctxt))) 
*}

definition starr_int_applied:: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"starr_int_applied h F \<equiv> \<not>(F h)"

lemma lspasl_starr_gen_int_applied:
"\<not> ((A ** B) h0) \<Longrightarrow> 
  (\<not> ((A ** B) h0) \<and> (starr_int_applied h0 (A ** B)))"
by (simp add: starr_int_applied_def)

lemma starr_int_der: "\<not>((A ** B) h) \<Longrightarrow> \<not>((A ** B) h) \<and> starr_int_applied h (A ** B)"
unfolding starr_int_applied_def by auto

lemma disj_distri_tern: "w ## z \<and> (x,y\<triangleright>z) \<Longrightarrow> w ## x"
by (metis sep_disj_addD1 tern_rel_def)

lemma disj_distri_tern2: "w ## z \<and> (x,y\<triangleright>z) \<Longrightarrow> w ## y"
using disj_distri_tern lspasl_e_der by blast 

lemma disj_distri_tern_rev: "x ## y \<and> x ## z \<and> (y,z\<triangleright>w) \<Longrightarrow> x ## w"
using disj_comb sep_disj_commuteI by blast

ML {*

(* Why do I have to do this? Shouldn't this be in the library? *)
fun list_mem m (x::xs) = if m = x then true else list_mem m xs
|list_mem _ [] = false;;

(* Remove duplicate elements in a list. *)
fun rm_dup_list (x::xs) = if list_mem x xs then rm_dup_list xs else x::(rm_dup_list xs)
|rm_dup_list [] = [];;

(* Get the bound variable name. *)
fun get_bvname bvs i = List.nth (bvs,((List.length bvs) - i - 1));;

(* Input a term of a quantified formula of conjunctions of 
  ternary relational atoms. Output the list of ternary relational
  atoms without the quantifiers. *)
fun get_trs (Const ("HOL.Ex", _) $ t) = get_trs t
|get_trs (Abs (_,_,t)) = get_trs t
|get_trs (Const ("HOL.conj", _) $ t1 $ t2) = (get_trs t1)@(get_trs t2)
(*|get_trs (t1 $ t2) = (get_trs t1)@(get_trs t2)*)
|get_trs ((Const ("Separata.heap_sep_algebra_class.tern_rel", tp) $
 t1 $ t2 $ t3) $ tl) = (Const ("Separata.heap_sep_algebra_class.tern_rel", tp) $
 t1 $ t2 $ t3)::(get_trs tl)
|get_trs (Const ("Separata.heap_sep_algebra_class.tern_rel", tp) $
 t1 $ t2 $ t3) = [(Const ("Separata.heap_sep_algebra_class.tern_rel", tp) $
 t1 $ t2 $ t3)]
|get_trs _ = [];;

(* Input a term of the current subgoal. Output the list of labels (strings)
  occurring in the assumptions. *)
fun get_ex_labels (Const ("Pure.all", _) $ t) = get_ex_labels t
|get_ex_labels (Abs (e, _,t)) = e::(get_ex_labels t)
|get_ex_labels (Const ("Pure.imp", _) $ t1 $ t2) = (get_ex_labels t1)@(get_ex_labels t2)
|get_ex_labels (Const ("HOL.Trueprop", _) $ t) = get_ex_labels t
|get_ex_labels ((Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ t1 $ t2 $ t3)) =
  (get_ex_labels t1)@(get_ex_labels t2)@(get_ex_labels t3)
|get_ex_labels (Free (s,_)) = [s]
|get_ex_labels _ = [];;

(* Input a list of existing labels (strings), a list of bound variables (terms),  
and a list of not quantified ternary relational atoms (terms), output a 
ternary relational atom (term) (h1,h2|>h3) in which h1 and h2 are existing 
labels and h3 is not an existing label. *)
fun get_tern ls bvs (t::tx) = (case t of 
  (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Free (s2,_) $ Bound i) => 
    if (list_mem s1 ls) andalso (list_mem s2 ls) andalso 
      not (list_mem (get_bvname bvs i) ls) then t 
    else get_tern ls bvs tx
  |(Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Free (s2,_) $ Bound i) => 
    if (list_mem (get_bvname bvs x) ls) andalso (list_mem s2 ls) andalso 
      not (list_mem (get_bvname bvs i) ls) then t 
    else get_tern ls bvs tx
  |(Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Bound y $ Bound i) => 
    if (list_mem s1 ls) andalso (list_mem (get_bvname bvs y) ls) andalso 
      not (list_mem (get_bvname bvs i) ls) then t 
    else get_tern ls bvs tx
  |(Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Bound y $ Bound i) => 
    if (list_mem (get_bvname bvs x) ls) andalso (list_mem (get_bvname bvs y) ls) andalso 
      not (list_mem (get_bvname bvs i) ls) then t 
    else get_tern ls bvs tx
  |(Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Free (s2,_) $ _) => (* The last label should is the root label. *) 
    if (list_mem s1 ls) andalso (list_mem s2 ls) then t 
    else get_tern ls bvs tx
  |(Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Free (s2,_) $ _) => (* The last label should be the root label. *) 
    if (list_mem (get_bvname bvs x) ls) andalso (list_mem s2 ls) then t 
    else get_tern ls bvs tx
  |(Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Bound y $ _) => (* The last label should be the root label. *) 
    if (list_mem s1 ls) andalso (list_mem (get_bvname bvs y) ls) then t 
    else get_tern ls bvs tx
  |(Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Bound y $ _) => (* The last label should be the root label. *) 
    if (list_mem (get_bvname bvs x) ls) andalso (list_mem (get_bvname bvs y) ls) then t 
    else get_tern ls bvs tx 
  |_ => get_tern ls bvs tx)
|get_tern _ _ [] = null_heap;;   

(* Input a ternary relational atom (term), create two terms
for two new subgoals. The first subgoal is of the form h1 ## h2,
the second subgoal is of the form \exist ev. (h1,h2|>ev).
For the last step of the tactics, there'll be a third subgoal
of the form s3 = ev0. *)
fun get_subgoals cbvs bvs (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Free (s2,_) $ Bound i) = 
  if i < (List.length cbvs) then (* Bound i is created in this tactic. *)
    [s1^" ## "^s2, "\<exists>"^(get_bvname bvs i)^". ("^s1^","^s2^"\<triangleright>"^(get_bvname bvs i)^")"]
  else (* Bound i was created before. *)
    [s1^" ## "^s2, "\<exists>ev0. ("^s1^","^s2^"\<triangleright> ev0) \<and> ev0 = "^(get_bvname bvs i)]
|get_subgoals cbvs bvs (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Free (s2,_) $ Bound i) = 
  if i < (List.length cbvs) then (* Bound i is created in this tactic. *)
    [(get_bvname bvs x)^" ## "^s2, 
      "\<exists>"^(get_bvname bvs i)^". ("^(get_bvname bvs x)^","^s2^"\<triangleright>"^(get_bvname bvs i)^")"]
  else (* Bound i was created before. *)
    [(get_bvname bvs x)^" ## "^s2, 
      "\<exists>ev0. ("^(get_bvname bvs x)^","^s2^"\<triangleright>ev0) \<and> ev0 = "^(get_bvname bvs i)]
|get_subgoals cbvs bvs (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Bound y $ Bound i) = 
  if i < (List.length cbvs) then (* Bound i is created in this tactic. *)
    [s1^" ## "^(get_bvname bvs y), 
      "\<exists>"^(get_bvname bvs i)^". ("^s1^","^(get_bvname bvs y)^"\<triangleright>"^(get_bvname bvs i)^")"]
  else (* Bound i was created before. *)
    [s1^" ## "^(get_bvname bvs y), 
      "\<exists>ev0. ("^s1^","^(get_bvname bvs y)^"\<triangleright>ev0) \<and> ev0 = "^(get_bvname bvs i)]
|get_subgoals cbvs bvs (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Bound y $ Bound i) = 
  if i < (List.length cbvs) then (* Bound i is created in this tactic. *)
    [(get_bvname bvs x)^" ## "^(get_bvname bvs y), 
      "\<exists>"^(get_bvname bvs i)^". ("^(get_bvname bvs x)^","^(get_bvname bvs y)^"\<triangleright>"^(get_bvname bvs i)^")"]
  else (* Bound i was created before. *)
    [(get_bvname bvs x)^" ## "^(get_bvname bvs y), 
      "\<exists>ev0. ("^(get_bvname bvs x)^","^(get_bvname bvs y)^"\<triangleright>ev0) \<and> ev0 = "^(get_bvname bvs i)]
|get_subgoals _ _ (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Free (s2,_) $ Free (s3,_)) = 
  [s1^" ## "^s2,"\<exists>ev0. ("^s1^","^s2^"\<triangleright>"^"ev0"^") \<and> ev0 = "^s3]
|get_subgoals _ bvs (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Free (s2,_) $ Free (s3,_)) = 
  [(get_bvname bvs x)^" ## "^s2,
    "\<exists>ev0. ("^(get_bvname bvs x)^","^s2^"\<triangleright>"^"ev0"^") \<and> ev0 = "^s3]
|get_subgoals _ bvs (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Free (s1,_) $ Bound y $ Free (s3,_)) = 
  [s1^" ## "^(get_bvname bvs y),
    "\<exists>ev0. ("^s1^","^(get_bvname bvs y)^"\<triangleright>"^"ev0"^") \<and> ev0 = "^s3]
|get_subgoals _ bvs (Const ("Separata.heap_sep_algebra_class.tern_rel", _) $ 
  Bound x $ Bound y $ Free (s3,_)) = 
  [(get_bvname bvs x)^" ## "^(get_bvname bvs y),
    "\<exists>ev0. ("^(get_bvname bvs x)^","^(get_bvname bvs y)^"\<triangleright>"^"ev0"^") \<and> ev0 = "^s3]
|get_subgoals _ _ _ = [];;

(* A tactic that continues the intermediate tactic of *R. *)
fun starr_final_tac ctxt sg = 
  let val prems = Thm.prems_of sg;          
      val ts = if prems = [] then [] else terms_of_prem (List.hd prems);    
  in
  if ts = [] then no_tac sg
  else 
    let val actual_goal = List.hd prems;  
        val conc = List.last ts;
        val bvs = get_bvl conc;
        val all_bvs = get_bvl actual_goal
    in
    if bvs = [] then no_tac sg
    else 
      let val trs = get_trs conc;
          val ls = rm_dup_list (get_ex_labels actual_goal);
          val this_tern = get_tern ls all_bvs trs;
          val new_subgoals = get_subgoals bvs all_bvs this_tern        
      in
      if (List.length new_subgoals) < 2 then no_tac sg
      else 
        let val tac1 = (Rule_Insts.subgoal_tac ctxt (List.hd new_subgoals) [] 1);
            val tac2 = (Rule_Insts.subgoal_tac ctxt (List.nth (new_subgoals,1)) [] 1)
        in
        (tac1 THEN tac2) sg
        end
      end
    end        
  end;;

*}

method_setup starr_final = {*
  (*concrete syntax like "clarsimp", "auto" etc.*)
  Method.sections Clasimp.clasimp_modifiers >>
    (*Isar method boilerplate*)
    (fn _ => fn ctxt => SIMPLE_METHOD (CHANGED (starr_final_tac ctxt))) 
*}

(* This version doesn't work in certain cases. 
method starr_solve_terns = (
(starr_final,auto,blast?)+,  
(*(metis (no_types, lifting) disj_distri_tern2 lspasl_e_der sep_add_assoc sep_add_commute tern_rel_def),*)
(smt lspasl_a_der lspasl_e_der tern_rel_def),
((metis (full_types) disj_comb disj_distri_tern disj_distri_tern_rev lspasl_e_eq tern_rel_def),
 (simp add: exist_comb))+,
(metis (full_types) disj_comb disj_distri_tern disj_distri_tern_rev lspasl_e_eq tern_rel_def)
)
*)
  
method starr_solve_terns = (
(starr_final,auto,blast?)+,  
(smt lspasl_a_der lspasl_e_der tern_rel_def),
((metis (full_types) disj_comb disj_distri_tern disj_distri_tern_rev lspasl_e_eq tern_rel_def),
 (simp add: exist_comb)?)+,
(metis (full_types) disj_comb disj_distri_tern disj_distri_tern_rev lspasl_e_eq tern_rel_def)?
)

method try_lspasl_starr_smart = (
simp?,
match premises in P:"\<not>(A ** B) (h::'a::heap_sep_algebra)" for h A B \<Rightarrow> 
  \<open>match premises in "starr_int_applied h (A ** B)" \<Rightarrow> \<open>fail\<close> 
   \<bar>_ \<Rightarrow> \<open>insert lspasl_starr_gen_int_applied[OF P], auto\<close>\<close>,
starr_interm,
auto?
)

lemma magic_mp: "(A ** C ** (C \<longrightarrow>* B)) h \<Longrightarrow> (A ** B) h"
proof -
  assume a1: "(A \<and>* C \<and>* (C \<longrightarrow>* B)) h"
  have f2: "\<forall>p pa a pb. (\<not> (p \<and>* pa) (a::'a) \<or> (\<exists>a. p a \<and> \<not> (pa \<longrightarrow>* pb) a)) \<or> pb a"
    by (metis sep_conj_sep_impl2)
  obtain aa :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
    "\<forall>x0 x2 x3. (\<exists>v4. x3 v4 \<and> \<not> (x2 \<longrightarrow>* x0) v4) = (x3 (aa x0 x2 x3) \<and> \<not> (x2 \<longrightarrow>* x0) (aa x0 x2 x3))"
    by moura
  then have f3: "\<forall>p pa a pb. (\<not> (p \<and>* pa) a \<or> p (aa pb pa p) \<and> \<not> (pa \<longrightarrow>* pb) (aa pb pa p)) \<or> pb a"
    using f2 by presburger
  have "\<forall>p pa a pb pc. ((pc \<and>* pb) (a::'a) \<and> (\<forall>a. pc a \<longrightarrow> pa a) \<and> (\<forall>a. pb a \<longrightarrow> p a) \<longrightarrow> (pa \<and>* p) a) = ((\<not> (pc \<and>* pb) a \<or> (\<exists>a. pc a \<and> \<not> pa a) \<or> (\<exists>a. pb a \<and> \<not> p a)) \<or> (pa \<and>* p) a)"
    by blast
  then have f4: "\<forall>p pa a pb pc. (\<not> (p \<and>* pa) (a::'a) \<or> (\<exists>a. p a \<and> \<not> pb a) \<or> (\<exists>a. pa a \<and> \<not> pc a)) \<or> (pb \<and>* pc) a"
    by (metis sep_conj_impl) 
  obtain aaa :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
    "\<forall>x0 x3. (\<exists>v5. x3 v5 \<and> \<not> x0 v5) = (x3 (aaa x0 x3) \<and> \<not> x0 (aaa x0 x3))"
    by moura
  then obtain aab :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
    f5: "\<forall>p pa a pb pc. (\<not> (p \<and>* pa) a \<or> p (aab pb p) \<and> \<not> pb (aab pb p) \<or> pa (aaa pc pa) \<and> \<not> pc (aaa pc pa)) \<or> (pb \<and>* pc) a"
    using f4 by moura
  have "(C \<and>* (C \<longrightarrow>* B)) = ((C \<longrightarrow>* B) \<and>* C)"
    by (meson abel_semigroup.commute sep.mult.abel_semigroup_axioms)
  then show ?thesis
    using f5 f3 a1 by (metis (no_types))
qed  

ML {*

(* Test if the formula is a star formula with a magic wand conjunct. *)
fun magic_in_star fm =
  case fm of (Const ("Separation_Algebra.sep_algebra_class.sep_conj",_) $
    fa $ fb) =>
    (case fa of (Const ("Separation_Algebra.sep_algebra_class.sep_impl",_) $ _ $ _) => true
    |_ => (case fb of (Const ("Separation_Algebra.sep_algebra_class.sep_impl",_) $ _ $ _) => true
           |_ => ((magic_in_star fa) orelse (magic_in_star fb))))
  |_ => false;;

(* Iterate through a list of terms and find a labelled star formula 
   which has a magic wand conjunct. Return the list of 
   terms (labelled star formula) that satisfy this form. *)
fun find_star_magic_fm ts =
  case ts of h::t => (
    case h of (Const ("Separation_Algebra.sep_algebra_class.sep_conj",tp) $
     fa $ fb $ _) => (if magic_in_star (Const ("Separation_Algebra.sep_algebra_class.sep_conj",tp) $
     fa $ fb) then (h::(find_star_magic_fm t)) else find_star_magic_fm t)
    |_ => find_star_magic_fm t
  )  
  |_ => [];;

(* Given a star formula (without label), return a list of conjuncts. *)
fun get_conjuncts fm = 
  case fm of (Const ("Separation_Algebra.sep_algebra_class.sep_conj",_) $
       fa $ fb) => (get_conjuncts fa)@(get_conjuncts fb)
  |_ => [fm];;

(* Given a labelled star formula, return a list of conjuncts (without labels). *)
(*fun conjuncts_of_star fm = 
  case fm of (Const ("Separation_Algebra.sep_algebra_class.sep_conj",t) $ fa $ fb $ _) => 
    get_conjuncts (Const ("Separation_Algebra.sep_algebra_class.sep_conj",t) $ fa $ fb)
  |_ => [];;*)

(* Given a list l and a member m in l. Return l-m. *)
fun rm_from_list m l =
  case l of h::t => (if h = m then t else (h::(rm_from_list m t)))
  |_ => l;;

(* Given two lists l1, l2, test if l1 is a sublist of l2, and
   return l2-l1. Return [null_heap] if l1 is not a sublist of l2. *)
fun get_reminder l1 l2 =
  case l1 of h::t => (if list_mem h l2 then get_reminder t (rm_from_list h l2) else [null_heap])
  |_ => l2;;

(* Given a list of terms, return a list of magic wand formulae in the terms. *)
fun get_magics ts = 
  case ts of h::t => 
    (case h of (Const ("Separation_Algebra.sep_algebra_class.sep_impl",_) $ _ $ _) =>
        (h::(get_magics t))
     |_ => get_magics t)
  |_ => [];;

(* Given a list of terms, make stars of them. 
Return null_heap if the list is empty. *)
fun mk_star terms = 
  let fun mk_star_internal terms = 
    if (List.tl terms) = [] then List.hd terms
    else Const ("Separation_Algebra.sep_algebra_class.sep_conj",bso_typ) $ (List.hd terms) $
     (mk_star_internal (List.tl terms))
  in
  if (List.length terms) = 0 then null_heap
  else mk_star_internal terms
  end;;

(* Given a list l of conjucts, and a list of magic wand formulae which occur
   in the conjuncts. 
   For each magic wand formula m = (A \<longrightarrow>* B), assume D = l - m. 
   Try to find a R such that D = R ** A. 
   Return R ** A ** (A \<longrightarrow>* B) if possible. Otherwise return null_heap. *)
fun get_subgoal ts ms =
  case ms of (Const ("Separation_Algebra.sep_algebra_class.sep_impl",tp) $ a $ b)::t => (
    let val ds = rm_from_list (Const ("Separation_Algebra.sep_algebra_class.sep_impl",tp) $ a $ b) ts;
        val subas = get_conjuncts a;
        val rs = get_reminder subas ds;
        val r = mk_star rs;
    in
    if rs = [null_heap] orelse r = null_heap then get_subgoal ts t
    else (Const ("Separation_Algebra.sep_algebra_class.sep_conj",
          bso_typ) $ r $ (Const ("Separation_Algebra.sep_algebra_class.sep_conj",
             bso_typ) $ a $ (Const ("Separation_Algebra.sep_algebra_class.sep_impl",
               bso_typ) $ a $ b)))
    end
  )
  |_ => null_heap;;

(* Given a labelled star formula with a magic wand conjunct. 
   Transform it to the form D ** (A \<longrightarrow>* B). 
   Try to find some R such that D = R ** A.
   If successful, return a new subgoal.  
   Return null_heap if the tac fails for all magic wand subformulae. *)
fun try_magic_tac fm = 
  case fm of (Const ("Separation_Algebra.sep_algebra_class.sep_conj",tp) $
    fa $ fb $ h) => (
    let val conjs = get_conjuncts (Const ("Separation_Algebra.sep_algebra_class.sep_conj",tp) $
                    fa $ fb);
        val magics = get_magics conjs;
        val nsg = (get_subgoal conjs magics) $ h;
    in
    if nsg = (null_heap $ h) then (null_heap,null_heap)
    else (nsg,fm)
    end
  ) 
  |_ => (null_heap,null_heap);;

(* Get the intermediate subgoal of the magic_tac.  *)
fun magic_tac_subgoal fml =
  case fml of h::t => (
    let val (nsg,fm) = try_magic_tac h in
    if nsg = null_heap orelse fm = null_heap then magic_tac_subgoal t
    else (nsg,fm)
    end
  )
  |_ => (null_heap,null_heap);;

(* Take a list of labelled formula of form (A \<longrightarrow>* B) ** D h or D ** (A \<longrightarrow>* B) h,
   create a subgoal tac. *)
fun magic_tac fml ctxt sg = 
  let val (nsg,fm) = magic_tac_subgoal fml;
      val nsg_str = str_of_term [] nsg;
      val fm_str = str_of_term [] fm; 
  in
  if nsg = null_heap orelse nsg_str = "" orelse fm = null_heap orelse fm_str = "" then no_tac sg
  else 
    let val tac1 = (Rule_Insts.subgoal_tac ctxt nsg_str [] 1);
        val tac2 = (Rule_Insts.thin_tac ctxt fm_str [] 1)
    in
    (tac1 THEN tac2) sg
    end
  end;;

fun magic_tac_wrapper ctxt sg =
  let val prems = Thm.prems_of sg;
      val this_goal = if prems = [] then null_heap else List.hd (Thm.prems_of sg);
      val ts = terms_of_prem this_goal;
      val fml = find_star_magic_fm ts;
  in
  if fml = [] then no_tac sg
  else magic_tac fml ctxt sg
  end;;

*}

method_setup magic_mp_tac = {*
  (*concrete syntax like "clarsimp", "auto" etc.*)
  Method.sections Clasimp.clasimp_modifiers >>
    (*Isar method boilerplate*)
    (fn _ => fn ctxt => SIMPLE_METHOD (CHANGED (magic_tac_wrapper ctxt))) 
*}  
  
method invert_magic = (
(try_lspasl_empl 
|try_lspasl_iu
|try_lspasl_d
|try_lspasl_eq     
|try_lspasl_p
|try_lspasl_c
|(magic_mp_tac,(drule magic_mp),prep?)  
|try_lspasl_starl
|try_lspasl_magicr  
|try_lspasl_starr_guided
|try_lspasl_magicl_guided)+,
auto?)     
      
method starforce =
(prep
 |(invert_magic            
  |(try_lspasl_starr_smart,(try_lspasl_starr,starr_solve_terns?)+) (* Tactics for solving *R formulae. *)   
  |try_lsfasl_boxl
  |struct
  |noninvert          
 )+ 
 |rare
)+

end
