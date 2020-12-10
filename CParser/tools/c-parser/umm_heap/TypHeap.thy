(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* License: BSD, terms see file ./LICENSE *)

theory TypHeap
imports
  Vanilla32
  "$L4V_ARCH/ArchArraysMemInstance"
  HeapRawState
  MapExtraTrans
begin

declare map_add_assoc [simp del]

definition wf_heap_val :: "heap_state \<Rightarrow> bool" where
  "wf_heap_val s \<equiv>
     \<forall>x t n v. s (x,SIndexVal) \<noteq> Some (STyp t) \<and> s (x,SIndexTyp n) \<noteq> Some (SValue v)"

type_synonym typ_slice_list = "(typ_uinfo \<times> typ_base) list"

primrec
  typ_slice_t :: "typ_uinfo \<Rightarrow> nat \<Rightarrow> typ_slice_list" and
  typ_slice_struct :: "typ_uinfo_struct \<Rightarrow> nat \<Rightarrow> typ_slice_list" and
  typ_slice_list :: "(typ_uinfo,field_name) dt_pair list \<Rightarrow> nat \<Rightarrow> typ_slice_list" and
  typ_slice_pair :: "(typ_uinfo,field_name) dt_pair \<Rightarrow> nat \<Rightarrow> typ_slice_list"
where
  tl0: "typ_slice_t (TypDesc st nm) m = typ_slice_struct st m @
        [(if m = 0 then ((TypDesc st nm),True) else
        ((TypDesc st nm),False))]"

| tl1: "typ_slice_struct (TypScalar n algn d) m = []"
| tl2: "typ_slice_struct (TypAggregate xs) m = typ_slice_list xs m"

| tl3: "typ_slice_list [] m = []"
| tl4: "typ_slice_list (x#xs) m = (if m < size_td (dt_fst x) \<or> xs = [] then
        typ_slice_pair x m else typ_slice_list xs (m - size_td (dt_fst x)))"

| tl5: "typ_slice_pair (DTPair t n) m = typ_slice_t t m"

definition list_map :: "'a list \<Rightarrow> (nat \<rightharpoonup> 'a)" where
  "list_map xs \<equiv> map_of (zip [0..<length xs] xs)"

definition s_footprint_untyped :: "addr \<Rightarrow> typ_uinfo \<Rightarrow> (addr \<times> s_heap_index) set" where
  "s_footprint_untyped p t \<equiv>
     {(p + of_nat x,k) | x k. x < size_td t \<and>
                              (k=SIndexVal \<or> (\<exists>n. k=SIndexTyp n \<and> n < length (typ_slice_t t x)))}"

definition s_footprint :: "'a::c_type ptr \<Rightarrow> (addr \<times> s_heap_index) set" where
  "s_footprint p \<equiv> s_footprint_untyped (ptr_val p) (typ_uinfo_t TYPE('a))"

definition empty_htd :: "heap_typ_desc" where
  "empty_htd \<equiv> \<lambda>x. (False,Map.empty)"

definition dom_s :: "heap_typ_desc \<Rightarrow> s_addr set" where
  "dom_s d \<equiv> {(x,SIndexVal) | x. fst (d x)} \<union>
      {(x,SIndexTyp n) | x n. snd (d x) n \<noteq> None}"

definition restrict_s :: "heap_typ_desc \<Rightarrow> s_addr set \<Rightarrow> heap_typ_desc" where
  "restrict_s d X \<equiv>
     \<lambda>x. ((x,SIndexVal) \<in> X \<and> fst (d x), (\<lambda>y. if (x,SIndexTyp y) \<in> X then snd (d x) y else None))"

definition valid_footprint :: "heap_typ_desc \<Rightarrow> addr \<Rightarrow> typ_uinfo \<Rightarrow> bool" where
  "valid_footprint d x t  \<equiv>
     let n = size_td t in
       0 < n \<and> (\<forall>y. y < n \<longrightarrow>
                    list_map (typ_slice_t t y) \<subseteq>\<^sub>m snd (d (x + of_nat y)) \<and> fst (d (x + of_nat y)))"

type_synonym 'a ptr_guard = "'a ptr \<Rightarrow> bool"

definition h_t_valid ::
  "heap_typ_desc \<Rightarrow> 'a ptr_guard \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool" ("_,_ \<Turnstile>\<^sub>t _" [99,0,99] 100) where
  "d,g \<Turnstile>\<^sub>t p \<equiv> valid_footprint d (ptr_val (p::'a ptr)) (typ_uinfo_t TYPE('a)) \<and> g p"


type_synonym 'a typ_heap = "'a ptr \<rightharpoonup> 'a"

definition proj_h :: "heap_state \<Rightarrow> heap_mem" where
  "proj_h s \<equiv> \<lambda>x. case_option undefined (case_s_heap_value id undefined) (s (x,SIndexVal))"

definition lift_state :: "heap_raw_state \<Rightarrow> heap_state" where
  "lift_state \<equiv> \<lambda>(h,d) (x,y).
     case y of
       SIndexVal \<Rightarrow> if fst (d x)then Some (SValue (h x)) else None
     | SIndexTyp n \<Rightarrow> case_option None (Some \<circ> STyp) (snd (d x) n)"


definition fun2list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "fun2list f n \<equiv> if n=0 then [] else map f [0..<n]"

definition null_d :: "heap_state \<Rightarrow> addr \<Rightarrow> nat \<Rightarrow> bool" where
  "null_d s x y \<equiv> s (x,SIndexTyp y) = None"

definition max_d :: "heap_state \<Rightarrow> addr \<Rightarrow> nat" where
  "max_d s x \<equiv> 1 + (GREATEST y. \<not> null_d s x y)"

definition proj_d :: "heap_state \<Rightarrow> heap_typ_desc" where
  "proj_d s \<equiv> \<lambda>x. (s (x,SIndexVal) \<noteq> None,
      \<lambda>n. case_option None (Some \<circ> s_heap_tag) (s (x,SIndexTyp n)))"

definition s_valid ::
  "heap_state \<Rightarrow> 'a ptr_guard \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool" ("_,_ \<Turnstile>\<^sub>s _" [100,0,100] 100) where
  "s,g \<Turnstile>\<^sub>s p \<equiv> proj_d s,g \<Turnstile>\<^sub>t p"

definition heap_list_s :: "heap_state \<Rightarrow> nat \<Rightarrow> addr \<Rightarrow>  byte list" where
  "heap_list_s s n p \<equiv> heap_list (proj_h s) n p"

definition lift_typ_heap :: "'a ptr_guard \<Rightarrow> heap_state \<Rightarrow> 'a::c_type typ_heap" where
  "lift_typ_heap g s \<equiv>
     (Some \<circ> from_bytes \<circ> heap_list_s s (size_of TYPE('a)) \<circ> ptr_val) |` {p. s,g \<Turnstile>\<^sub>s p}"

definition heap_update_s :: "'a ptr \<Rightarrow> 'a::c_type \<Rightarrow> heap_state \<Rightarrow> heap_state" where
  "heap_update_s n p s \<equiv> lift_state (heap_update n p (proj_h s), proj_d s)"

definition lift_t :: "'a::c_type ptr_guard \<Rightarrow> heap_raw_state \<Rightarrow> 'a typ_heap" where
  "lift_t g \<equiv> lift_typ_heap g \<circ> lift_state"

definition tag_disj :: "'a typ_desc \<Rightarrow> 'a typ_desc \<Rightarrow> bool" ("_ \<bottom>\<^sub>t _" [90,90] 90) where
  "f \<bottom>\<^sub>t g \<equiv> \<not> (f \<le> g \<or> g \<le> f)"

definition ladder_set :: "typ_uinfo \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (typ_uinfo \<times> nat) set" where
  "ladder_set s n p \<equiv> {(t,n+p) | t. \<exists>k. (t,k) \<in> set (typ_slice_t s n)}"


(* case where 'b is a field type of 'a *)

primrec
  field_names :: "'a typ_info \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list" and
  field_names_struct :: "'a field_desc typ_struct \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list" and
  field_names_list :: "('a typ_info,field_name) dt_pair list \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list" and
  field_names_pair :: "('a typ_info,field_name) dt_pair \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list"
where
  tfs0: "field_names (TypDesc st nm) t = (if t=export_uinfo (TypDesc st nm) then
         [[]] else field_names_struct st t)"

| tfs1: "field_names_struct (TypScalar m algn d) t = []"
| tfs2: "field_names_struct (TypAggregate xs) t = field_names_list xs t"

| tfs3: "field_names_list [] t = []"
| tfs4: "field_names_list (x#xs) t = field_names_pair x t@field_names_list xs t"

| tfs5: "field_names_pair (DTPair s f) t = map (\<lambda>fs. f#fs) (field_names s t)"


definition fin ::
  "typ_uinfo \<Rightarrow> typ_name \<Rightarrow> (('a typ_info \<times> qualified_field_name list) \<times> field_name) list \<Rightarrow>
          ('a typ_info \<times> qualified_field_name list)" where
  "fin r \<equiv> \<lambda>tn ts.
     let t = TypDesc (TypAggregate (map (\<lambda>((t,fs),f). DTPair t f) ts)) tn in
       (t,if r = export_uinfo t then [[]] else concat (map (\<lambda>((t,fs),f). map ((#) f) fs) ts))"

definition field_typ_untyped :: "'a typ_desc \<Rightarrow> qualified_field_name \<Rightarrow> 'a typ_desc" where
  "field_typ_untyped t n \<equiv> (fst (the (field_lookup t n 0)))"

definition field_typ :: "'a::c_type itself \<Rightarrow> qualified_field_name \<Rightarrow> 'a typ_info" where
  "field_typ t n \<equiv> field_typ_untyped (typ_info_t TYPE('a)) n"

definition fs_consistent ::
  "qualified_field_name list \<Rightarrow> 'a::c_type itself \<Rightarrow> 'b::c_type itself \<Rightarrow> bool" where
  "fs_consistent fs a b \<equiv> set fs \<subseteq> set (field_names (typ_info_t TYPE('a)) (typ_uinfo_t TYPE('b)))"

definition field_offset_footprint :: "'a::c_type ptr \<Rightarrow> (qualified_field_name) list \<Rightarrow> 'b ptr set"
  where
  "field_offset_footprint p fs \<equiv> {Ptr &(p\<rightarrow>k) | k. k \<in> set fs}"


definition sub_typ :: "'a::c_type itself \<Rightarrow> 'b::c_type itself \<Rightarrow> bool" ("_ \<le>\<^sub>\<tau> _" [51, 51] 50) where
  "s \<le>\<^sub>\<tau> t \<equiv> typ_uinfo_t s \<le> typ_uinfo_t t"

definition sub_typ_proper :: "'a::c_type itself \<Rightarrow> 'b::c_type itself \<Rightarrow> bool" ("_ <\<^sub>\<tau> _" [51, 51] 50)
  where
  "s <\<^sub>\<tau> t \<equiv> typ_uinfo_t s < typ_uinfo_t t"

definition peer_typ :: "'a::c_type itself \<Rightarrow> 'b :: c_type itself \<Rightarrow> bool"
  where
  "peer_typ a b \<equiv> typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE('b) \<or>
                   typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"

definition guard_mono :: "'a::c_type ptr_guard \<Rightarrow> 'b::c_type ptr_guard \<Rightarrow> bool" where
  "guard_mono g g' \<equiv>
     \<forall>n f p. g p \<and>
        field_lookup  (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b),n)  \<longrightarrow>
        g' (Ptr (ptr_val p + of_nat n))"

primrec sub_field_update_t ::
  "qualified_field_name list \<Rightarrow> 'a ptr \<Rightarrow> 'a::c_type \<Rightarrow> 'b::c_type typ_heap \<Rightarrow> 'b typ_heap"
where
  sft0: "sub_field_update_t [] p v s = s"
| sft1: "sub_field_update_t (f#fs) p (v::'a::c_type) s =
           (let s' = sub_field_update_t fs p v s in
              s'(Ptr &(p\<rightarrow>f) \<mapsto> from_bytes (access_ti\<^sub>0 (field_typ TYPE('a) f) v))) |`
                dom (s::'b::c_type typ_heap)"

(* case where 'b contains a field of type of 'a *)

primrec update_value_t :: "(qualified_field_name) list \<Rightarrow> 'a::c_type \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'b::c_type"
where
  uvt0:  "update_value_t [] v w x = w"
| uvt1:  "update_value_t (f#fs) v (w::'b) x = (if x=field_offset TYPE('b) f then
      field_update (field_desc (field_typ TYPE('b) f)) (to_bytes_p (v::'a::c_type)) (w::'b::c_type) else update_value_t fs v w x)"

definition super_field_update_t :: "'a ptr \<Rightarrow> 'a::c_type \<Rightarrow> 'b::c_type typ_heap \<Rightarrow> 'b typ_heap" where
  "super_field_update_t p v s \<equiv> \<lambda>q.
     if field_of_t p q
     then
       case_option None
                   (\<lambda>w. Some (update_value_t (field_names (typ_info_t TYPE('b)) (typ_uinfo_t TYPE('a)))
                                             v w (unat (ptr_val p - ptr_val q))))
                   (s q)
     else s q"

definition heap_footprint :: "heap_typ_desc \<Rightarrow> typ_uinfo \<Rightarrow> addr set" where
  "heap_footprint d t \<equiv> {x. \<exists>y. valid_footprint d y t \<and> x \<in> {y} \<union> {y..+size_td t}}"

definition ptr_safe :: "'a::c_type ptr \<Rightarrow> heap_typ_desc \<Rightarrow> bool" where
  "ptr_safe p d \<equiv> s_footprint p \<subseteq> dom_s d"

(* Retyping *)

primrec
  htd_update_list :: "addr \<Rightarrow> typ_slice list \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  hul0:  "htd_update_list p [] d = d"
| hul1:  "htd_update_list p (x#xs) d = htd_update_list (p+1) xs (d(p := (True,snd (d p) ++ x)))"

definition dom_tll :: "addr \<Rightarrow> typ_slice list \<Rightarrow> s_addr set" where
  "dom_tll p xs \<equiv> {(p + of_nat x,SIndexVal) | x. x < length xs} \<union>
                   {(p + of_nat x,SIndexTyp n) | x n. x < length xs \<and> (xs ! x) n \<noteq> None}"

definition typ_slices :: "'a::c_type itself \<Rightarrow> typ_slice list" where
  "typ_slices t \<equiv> map (\<lambda>n. list_map (typ_slice_t (typ_uinfo_t TYPE('a)) n)) [0..<size_of TYPE('a)]"

definition ptr_retyp :: "'a::c_type ptr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc" where
  "ptr_retyp p \<equiv> htd_update_list (ptr_val p) (typ_slices TYPE('a))"

definition field_fd :: "'a::c_type itself \<Rightarrow> qualified_field_name \<Rightarrow> 'a field_desc" where
  "field_fd t n \<equiv> field_desc (field_typ t n)"

definition tag_disj_typ :: "'a::c_type itself \<Rightarrow> 'b::c_type itself \<Rightarrow> bool" ("_ \<bottom>\<^sub>\<tau> _") where
  "s \<bottom>\<^sub>\<tau> t \<equiv> typ_uinfo_t s \<bottom>\<^sub>t typ_uinfo_t t"

text \<open>----\<close>

lemma wf_heap_val_SIndexVal_STyp_simp [simp]:
  "wf_heap_val s \<Longrightarrow> s (x,SIndexVal) \<noteq> Some (STyp t)"
  apply(clarsimp simp: wf_heap_val_def)
  apply(drule_tac x=x in spec)
  apply clarsimp
  apply(case_tac t, simp)
  apply fast
  done

lemma wf_heap_val_SIndexTyp_SValue_simp [simp]:
  "wf_heap_val s \<Longrightarrow> s (x,SIndexTyp n) \<noteq> Some (SValue v)"
  apply(unfold wf_heap_val_def)
  apply clarify
  apply(drule_tac x=x in spec)
  apply clarsimp
  done

lemma field_tag_sub:
  "field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (t,n) \<Longrightarrow>
      {&(p\<rightarrow>f)..+size_td t} \<subseteq> {ptr_val (p::'a ptr)..+size_of TYPE('a)}"
  apply(clarsimp simp: field_ti_def split: option.splits)
  apply(drule intvlD, clarsimp simp: field_lvalue_def field_offset_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(subst add.assoc)
  apply(subst Abs_fnat_homs)
  apply(rule intvlI)
  apply(simp add: size_of_def typ_uinfo_t_def)
  apply(drule td_set_field_lookupD)
  apply(drule td_set_offset_size)
  apply(simp)
  done

lemma typ_slice_t_not_empty [simp]:
  "typ_slice_t t n \<noteq> []"
  by (case_tac t, simp)

lemma list_map_typ_slice_t_not_empty [simp]:
  "list_map (typ_slice_t t n) \<noteq> Map.empty"
  apply(simp add: list_map_def)
  apply(case_tac "typ_slice_t t n", fastforce)
  by (simp add: upt_rec)

lemma s_footprint:
  "s_footprint (p::'a::c_type ptr) =
     {(ptr_val p + of_nat x,k) | x k.
        x < size_of TYPE('a) \<and>
        (k=SIndexVal \<or> (\<exists>n. k=SIndexTyp n \<and> n < length (typ_slice_t (typ_uinfo_t TYPE('a)) x)))}"
  by (auto simp: s_footprint_def s_footprint_untyped_def size_of_def )

lemma ptr_val_SIndexVal_in_s_footprint [simp]:
  "(ptr_val p, SIndexVal) \<in> s_footprint (p::'a::mem_type ptr)"
  apply(simp add: s_footprint)
  apply(rule_tac x=0 in exI)
  by auto

lemma s_footprintI:
  "\<lbrakk> n < length (typ_slice_t (typ_uinfo_t TYPE('a)) x); x < size_of TYPE('a) \<rbrakk> \<Longrightarrow>
      (ptr_val p + of_nat x, SIndexTyp n) \<in> s_footprint (p::'a::c_type ptr)"
  apply(simp add: s_footprint)
  apply(rule_tac x=x in exI)
  apply auto
  done

lemma s_footprintI2:
  "x < size_of TYPE('a) \<Longrightarrow> (ptr_val p + of_nat x, SIndexVal) \<in> s_footprint (p::'a::c_type ptr)"
  apply(simp add: s_footprint)
  apply(rule_tac x=x in exI)
  apply auto
  done

lemma s_footprintD:
  "(x,k) \<in> s_footprint p \<Longrightarrow> x \<in> {ptr_val (p::'a::c_type ptr)..+size_of TYPE('a)}"
  by (auto simp: s_footprint elim: intvlI)

lemma s_footprintD2:
  "(x,SIndexTyp n) \<in> s_footprint (p::'a::mem_type ptr) \<Longrightarrow>
      n < length (typ_slice_t (typ_uinfo_t TYPE('a)) (unat (x - ptr_val p)))"
  apply(clarsimp simp: s_footprint)
  apply(subst word_unat.eq_norm)
  apply(subst mod_less)
   apply(subst len_of_addr_card)
   apply(erule less_trans)
   apply(rule max_size)
  apply simp
  done

lemma s_footprint_restrict:
  "x \<in> s_footprint p \<Longrightarrow> (s |` s_footprint p) x = s x"
  by (rule restrict_in)

lemma restrict_s_fst:
  "fst (restrict_s d X x) \<Longrightarrow> fst (d x)"
  by (clarsimp simp: restrict_s_def)

lemma restrict_s_map_le [simp]:
  "snd (restrict_s d X x) \<subseteq>\<^sub>m snd (d x)"
  by (auto simp: restrict_s_def map_le_def)

lemma dom_list_map [simp]:
  "dom (list_map xs) = {0..<length xs}"
  by (auto simp: list_map_def)

lemma list_map [simp]:
  "n < length xs \<Longrightarrow> list_map xs n = Some (xs ! n)"
  by (force simp: list_map_def set_zip)

lemma list_map_eq:
  "list_map xs n = (if n < length xs then Some (xs ! n) else None)"
  by (force simp: list_map_def set_zip)

lemma valid_footprintI:
  "\<lbrakk> 0 < size_td t; \<And>y. y < size_td t \<Longrightarrow> list_map (typ_slice_t t y) \<subseteq>\<^sub>m snd (d (x + of_nat y)) \<and>
      fst (d (x + of_nat y)) \<rbrakk> \<Longrightarrow>
      valid_footprint d x t"
  by (simp add: valid_footprint_def)

lemma valid_footprintD:
  "\<lbrakk> valid_footprint d x t; y < size_td t \<rbrakk> \<Longrightarrow>
      list_map (typ_slice_t t y) \<subseteq>\<^sub>m snd (d (x + of_nat y)) \<and>
          fst (d (x + of_nat y))"
 by (simp add: valid_footprint_def Let_def)

lemma h_t_valid_taut:
  "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> d,(\<lambda>x. True) \<Turnstile>\<^sub>t p"
  by (simp add: h_t_valid_def)

lemma h_t_valid_restrict:
  "restrict_s d (s_footprint p),g \<Turnstile>\<^sub>t p = d,g \<Turnstile>\<^sub>t p"
  apply (simp add: h_t_valid_def valid_footprint_def Let_def)
  apply (fastforce simp: restrict_s_def map_le_def size_of_def intro: s_footprintI s_footprintI2)
  done

lemma h_t_valid_restrict2:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t p; restrict_s d (s_footprint p) = restrict_s d' (s_footprint p)
       \<rbrakk> \<Longrightarrow> d',g \<Turnstile>\<^sub>t (p::'a::c_type ptr)"
  apply(clarsimp simp: h_t_valid_def valid_footprint_def Let_def)
  apply(rule conjI; clarsimp?)
   apply(clarsimp simp: map_le_def)
   apply(drule_tac x="(ptr_val p + of_nat y)" in fun_cong)
   apply(clarsimp simp: restrict_s_def)
   apply(drule_tac x=a in fun_cong)
   apply(fastforce simp: size_of_def intro: s_footprintI split: if_split_asm)
  apply(drule_tac x="(ptr_val p + of_nat y)" in fun_cong)
  apply(fastforce simp: size_of_def restrict_s_def intro: s_footprintI2)
  done

lemma lift_state_wf_heap_val [simp]:
  "wf_heap_val (lift_state (h,d))"
  unfolding wf_heap_val_def
  by (auto simp: lift_state_def split: option.splits)

lemma wf_hs_proj_d:
  "fst (proj_d s x) \<Longrightarrow> s (x,SIndexVal) \<noteq> None"
  by (auto simp: proj_d_def)


lemma s_valid_g:
  "s,g \<Turnstile>\<^sub>s p \<Longrightarrow> g p"
  by (simp add: s_valid_def h_t_valid_def)

lemma lift_typ_heap_if:
  "lift_typ_heap g s = (\<lambda>(p::'a::c_type ptr). if s,g \<Turnstile>\<^sub>s p then Some (from_bytes
      (heap_list_s s (size_of TYPE('a)) (ptr_val p))) else None)"
  by (force simp: lift_typ_heap_def)

lemma lift_typ_heap_s_valid:
  "lift_typ_heap g s p = Some x \<Longrightarrow> s,g \<Turnstile>\<^sub>s p"
  by (simp add: lift_typ_heap_if split: if_split_asm)

lemma lift_typ_heap_g:
  "lift_typ_heap g s p = Some x \<Longrightarrow> g p"
  by (fast dest: lift_typ_heap_s_valid s_valid_g)

lemma lift_state_empty [simp]:
  "lift_state (h,empty_htd) = Map.empty"
 by (auto simp: lift_state_def empty_htd_def split: s_heap_index.splits)

lemma lift_state_eqI:
  "\<lbrakk> h x = h' x; d x = d' x \<rbrakk> \<Longrightarrow> lift_state (h,d) (x,k) = lift_state (h',d') (x,k)"
  by (clarsimp simp: lift_state_def split: s_heap_index.splits)

lemma proj_h_lift_state:
  "fst (d x) \<Longrightarrow>  proj_h (lift_state (h,d)) x = h x"
  by (clarsimp simp: proj_h_def lift_state_def)

lemma lift_state_proj_simp [simp]:
  "lift_state (proj_h (lift_state (h, d)), d) = lift_state (h, d)"
  by (auto simp: lift_state_def proj_h_def split: s_heap_index.splits option.splits)

lemma f2l_length [simp]:
  "length (fun2list f n) = n"
  by (simp add: fun2list_def)

lemma GREATEST_lt [simp]:
  "0 < n \<Longrightarrow> (GREATEST x. x < n) = n - (1::nat)"
  by (rule Greatest_equality; simp)

lemma fun2list_nth [simp]:
  "x < n \<Longrightarrow> fun2list f n ! x = f x"
  by (clarsimp simp: fun2list_def)

lemma proj_d_lift_state:
  "proj_d (lift_state (h,d)) = d"
  apply(rule ext)
  apply(case_tac "d x")
  apply(auto simp: proj_d_def lift_state_def Let_def split: option.splits)
  done

lemma lift_state_proj [simp]:
  "wf_heap_val s \<Longrightarrow> lift_state (proj_h s,proj_d s) = s"
  apply (clarsimp simp: proj_h_def proj_d_def lift_state_def fun_eq_iff
                 split: if_split_asm s_heap_index.splits option.splits)
  apply safe
    apply (metis s_heap_tag.simps s_heap_value.exhaust wf_heap_val_SIndexTyp_SValue_simp)
   apply (metis id_apply s_heap_value.exhaust s_heap_value.simps(5) wf_heap_val_SIndexVal_STyp_simp)
  apply (metis s_heap_tag.simps s_heap_value.exhaust wf_heap_val_SIndexTyp_SValue_simp)
  done

lemma lift_state_Some:
  "lift_state (h,d) (p,SIndexTyp n) = Some t \<Longrightarrow> snd (d p) n = Some (s_heap_tag t)"
  apply (simp add: lift_state_def split: option.splits split: if_split_asm)
  apply (case_tac t; simp)
  done

lemma lift_state_Some2:
  "snd (d p) n = Some t \<Longrightarrow>
      \<exists>v. lift_state (h,d) (p,SIndexTyp n) = Some (STyp t)"
  by (simp add: lift_state_def split: option.split)

lemma h_t_s_valid:
  "lift_state (h,d),g \<Turnstile>\<^sub>s p = d,g \<Turnstile>\<^sub>t p"
  by (simp add: s_valid_def proj_d_lift_state)

lemma lift_t:
  "lift_typ_heap g (lift_state s) = lift_t g s"
  by (simp add: lift_t_def)

lemma lift_t_h_t_valid:
  "lift_t g (h,d) p = Some x \<Longrightarrow> d,g \<Turnstile>\<^sub>t p"
  by (force simp: lift_t_def h_t_s_valid dest: lift_typ_heap_s_valid)

lemma lift_t_g:
  "lift_t g s p = Some x \<Longrightarrow> g p"
  by (force simp: lift_t_def dest: lift_typ_heap_g)

lemma lift_t_proj [simp]:
  "wf_heap_val s \<Longrightarrow> lift_t g (proj_h s, proj_d s) = lift_typ_heap g s"
  by (simp add: lift_t_def)

lemma valid_footprint_Some:
  assumes valid: "valid_footprint d p t" and size: "x < size_td t"
  shows "fst (d (p + of_nat x))"
proof (cases "of_nat x=(0::addr)")
  case True
  with valid show ?thesis by (force simp add: valid_footprint_def Let_def)
next
  case False
  with size valid show ?thesis by (force simp: valid_footprint_def Let_def)
qed

lemma h_t_valid_Some:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a::c_type ptr); x < size_of TYPE('a) \<rbrakk> \<Longrightarrow>
    fst (d (ptr_val p + of_nat x))"
  by (force simp: h_t_valid_def size_of_def   dest: valid_footprint_Some)

lemma h_t_valid_ptr_safe:
  "d,g \<Turnstile>\<^sub>t (p::'a::c_type ptr) \<Longrightarrow> ptr_safe p d"
  apply(clarsimp simp: ptr_safe_def h_t_valid_def valid_footprint_def s_footprint_def
                       s_footprint_untyped_def dom_s_def size_of_def Let_def)
  by (metis (mono_tags, hide_lams) domIff list_map map_le_def option.simps(3) surj_pair)

lemma lift_t_ptr_safe:
  "lift_t g (h,d) (p::'a::c_type ptr) = Some x \<Longrightarrow> ptr_safe p d"
  by (fast dest: lift_t_h_t_valid h_t_valid_ptr_safe)

lemma s_valid_Some:
  "\<lbrakk> d,g \<Turnstile>\<^sub>s (p::'a::c_type ptr); x < size_of TYPE('a) \<rbrakk> \<Longrightarrow>
       d (ptr_val p + of_nat x,SIndexVal) \<noteq> None"
  by (auto simp: s_valid_def dest!: h_t_valid_Some wf_hs_proj_d split: option.splits)

lemma heap_list_s_heap_list_dom:
  "\<And>n. (\<lambda>x. (x,SIndexVal)) ` {n..+k} \<subseteq> dom_s d \<Longrightarrow>
        heap_list_s (lift_state (h,d)) k n = heap_list h k n"
proof (induct k)
  case 0 show ?case by (simp add: heap_list_s_def)
next
  case (Suc k)
  hence "(\<lambda>x. (x,SIndexVal)) ` {n + 1..+k} \<subseteq> dom_s d"
    by (force intro: intvl_plus_sub_Suc subset_trans simp: image_def)
  with Suc have "heap_list_s (lift_state (h, d)) k (n + 1) =
      heap_list h k (n + 1)" by simp
  moreover from this Suc have "(n,SIndexVal) \<in> dom_s d"
    by (force simp: dom_s_def image_def intro: intvl_self)
  ultimately show ?case
    by (auto simp add: heap_list_s_def proj_h_lift_state dom_s_def)
qed

lemma heap_list_s_heap_list:
  "d,(\<lambda>x. True) \<Turnstile>\<^sub>t (p::'a::c_type ptr) \<Longrightarrow>
          heap_list_s (lift_state (h,d)) (size_of TYPE('a)) (ptr_val p)
              = heap_list h (size_of TYPE('a)) (ptr_val p)"
  apply(drule h_t_valid_ptr_safe)
  apply(clarsimp simp: ptr_safe_def)
  apply(subst heap_list_s_heap_list_dom)
   apply(clarsimp simp: dom_s_def)
   apply(drule_tac c="(x,SIndexVal)" in subsetD)
    apply(clarsimp simp: intvl_def)
    apply(erule s_footprintI2)
   apply clarsimp+
  done

lemma lift_t_if:
  "lift_t g (h,d) = (\<lambda>p. if d,g \<Turnstile>\<^sub>t p then Some (h_val h (p::'a::c_type ptr)) else None)"
  by (force simp: lift_t_def lift_typ_heap_if h_t_s_valid h_val_def
                  heap_list_s_heap_list h_t_valid_taut)

lemma lift_lift_t:
  "d,g \<Turnstile>\<^sub>t (p::'a::c_type ptr) \<Longrightarrow> lift h p = the (lift_t g (h,d) p)"
  by (simp add: lift_t_if lift_def)

lemma lift_t_lift:
  "lift_t g (h,d) (p::'a::c_type ptr) = Some v \<Longrightarrow> lift h p = v"
  by (simp add: lift_t_if lift_def split: if_split_asm)

lemma heap_update_list_same:
  "\<And>h p k. \<lbrakk> 0 < k; k \<le> addr_card - length v \<rbrakk> \<Longrightarrow> heap_update_list (p + of_nat k) v h p = h p"
proof (induct v)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have "heap_update_list (p + of_nat k) (x # xs) h p =
        heap_update_list (p + of_nat (k + 1)) xs (h(p + of_nat k := x)) p"
    by (simp add: ac_simps)
  also have "\<dots> = (h(p + of_nat k := x)) p"
  proof -
    from Cons have "k + 1 \<le> addr_card - length xs" by simp
    with Cons show ?thesis by (simp only:)
  qed
  also have "\<dots> = h p"
  proof -
    from Cons have "of_nat k \<noteq> (0::addr)"
      by - (erule of_nat_neq_0, simp add: addr_card)
    thus ?thesis by clarsimp
  qed
  finally show ?case .
qed

lemma heap_list_update:
  "\<And>h p. length v \<le> addr_card \<Longrightarrow>
          heap_list (heap_update_list p v h) (length v) p = v"
proof (induct v)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  hence "heap_update_list (p + of_nat 1) xs (h(p := x)) p = (h(p := x)) p"
    by - (rule heap_update_list_same, auto)
  with Cons show ?case by simp
qed

lemma heap_list_update_to_bytes:
  "heap_list (heap_update_list p (to_bytes (v::'a::mem_type) (heap_list h (size_of TYPE('a)) p)) h)
             (size_of TYPE('a)) p = to_bytes v (heap_list h (size_of TYPE('a)) p)"
  by (metis (mono_tags) heap_list_length heap_list_update len less_imp_le max_size)

lemma h_val_heap_update:
  "h_val (heap_update p v h) p = (v::'a::mem_type)"
  by (simp add: h_val_def heap_update_def heap_list_update_to_bytes)

lemma heap_list_update_disjoint_same:
  shows "\<And>q. {p..+length v} \<inter> {q..+k} = {} \<Longrightarrow>
             heap_list (heap_update_list p v h) k q = heap_list h k q"
proof (induct k)
  case 0 show ?case by simp
next
  case (Suc n)
  hence "{p..+length v} \<inter> {q + 1..+n} = {}"
    by (force intro: intvl_plus_sub_Suc)
  with Suc have "heap_list (heap_update_list p v h) n (q + 1) =
      heap_list h n (q + 1)" by simp
  moreover have "heap_update_list (q + of_nat (unat (p - q))) v h q = h q"
  proof (cases v)
    case Nil thus ?thesis by simp
  next
    case (Cons y ys)
    with Suc have "0 < unat (p - q)"
      by (case_tac "p=q")
         (simp add: intvl_start_inter unat_gt_0)+
    moreover have "unat (p - q) \<le> addr_card - length v" (is ?G)
    proof (rule ccontr)
      assume "\<not> ?G"
      moreover from Suc have "q \<notin> {p..+length v}"
        by (fast intro: intvl_self)
      ultimately show False
        by (simp only: linorder_not_le len_of_addr_card [symmetric])
           (frule_tac p=q in intvl_self_offset, force+)
    qed
    ultimately show ?thesis by (rule heap_update_list_same)
  qed
  ultimately show ?case by simp
qed

lemma heap_update_nmem_same:
  assumes nmem: "q \<notin> {p..+length v}"
  shows "heap_update_list p v h q = h q"
proof -
  from nmem have "heap_list (heap_update_list p v h) 1 q = heap_list h 1 q"
    by - (rule heap_list_update_disjoint_same, force dest: intvl_Suc)
  thus ?thesis by simp
qed

lemma heap_update_mem_same [rule_format]:
  "\<lbrakk> q \<in> {p..+length v}; length v < addr_card \<rbrakk> \<Longrightarrow>
      heap_update_list p v h q = heap_update_list p v h' q"
  by (induct v arbitrary: p h h'; simp)
     (fastforce dest: intvl_neq_start simp: heap_update_list_same [where k=1, simplified])

lemma sub_tag_proper_TypScalar [simp]:
  "\<not> t < TypDesc (TypScalar n algn d) nm"
  by (simp add: typ_tag_lt_def typ_tag_le_def)

lemma tag_disj_com [simp]:
  "f \<bottom>\<^sub>t g = g \<bottom>\<^sub>t f"
  by (force simp: tag_disj_def)

lemma typ_slice_set':
  "\<forall>m n. fst ` set (typ_slice_t s n)  \<subseteq> fst ` td_set s m"
  "\<forall>m n. fst ` set (typ_slice_struct st n) \<subseteq> fst ` td_set_struct st m"
  "\<forall>m n. fst ` set (typ_slice_list xs n) \<subseteq> fst ` td_set_list xs m"
  "\<forall>m n. fst ` set (typ_slice_pair x n) \<subseteq> fst ` td_set_pair x m"
  apply(induct s and st and xs and x, all \<open>clarsimp simp: ladder_set_def\<close>)
   apply auto[1]
  apply (rule conjI; clarsimp)
   apply force
  apply(thin_tac "All P" for P)
  apply force
  done

lemma typ_slice_set:
  "fst ` set (typ_slice_t s n) \<subseteq> fst ` td_set s m"
  using typ_slice_set'(1) [of s] by clarsimp

lemma typ_slice_struct_set:
  "(s,t) \<in> set (typ_slice_struct st n) \<Longrightarrow> \<exists>k. (s,k) \<in> td_set_struct st m"
  using typ_slice_set'(2) [of st] by force

lemma typ_slice_set_sub:
  "typ_slice_t s m \<le> typ_slice_t t n \<Longrightarrow>
      fst ` set (typ_slice_t s m) \<subseteq> fst ` set (typ_slice_t t n)"
  by (force simp: image_def prefix_def less_eq_list_def)

lemma ladder_set_self:
  "s \<in> fst ` set (typ_slice_t s n)"
  by (cases s) (auto simp: ladder_set_def)

lemma typ_slice_sub:
  "typ_slice_t s m \<le> typ_slice_t t n \<Longrightarrow> s \<le> t"
  apply(drule typ_slice_set_sub)
  using ladder_set_self [of s m] typ_slice_set [of t n 0]
  apply(force simp: typ_tag_le_def)
  done

lemma typ_slice_self:
  "(s,True) \<in> set (typ_slice_t s 0)"
  by (cases s) simp

lemma typ_slice_struct_nmem:
  "(TypDesc st nm,n) \<notin> set (typ_slice_struct st k)"
  by (fastforce dest: typ_slice_struct_set td_set_struct_size_lte)

lemma typ_slice_0_prefix:
  "0 < n \<Longrightarrow> \<not> typ_slice_t t 0 \<le> typ_slice_t t n \<and> \<not> typ_slice_t t n \<le> typ_slice_t t 0"
  by (cases t) (fastforce simp: less_eq_list_def typ_slice_struct_nmem dest: set_mono_prefix)

lemma prefix_eq_nth:
  "xs \<le> ys = ((\<forall>i. i < length xs \<longrightarrow> xs ! i = ys ! i) \<and> length xs \<le> length ys)"
  apply(rule iffI; clarsimp simp: less_eq_list_def prefix_def nth_append)
  by (metis append_take_drop_id nth_take_lemma order_refl take_all)

lemma map_prefix_same_cases:
  "\<lbrakk> list_map xs \<subseteq>\<^sub>m f; list_map ys \<subseteq>\<^sub>m f \<rbrakk> \<Longrightarrow> xs \<le> ys \<or> ys \<le> xs"
  using linorder_linear[where x="length xs" and y="length ys"]
  apply(clarsimp simp: prefix_eq_nth map_le_def prefix_def)
  apply(erule disjE; clarsimp, ((drule_tac x=i in bspec, simp)+, force dest: sym))
  done

lemma list_map_mono:
  "xs \<le> ys \<Longrightarrow> list_map xs \<subseteq>\<^sub>m list_map ys"
  by (auto simp: map_le_def prefix_def nth_append less_eq_list_def)

lemma map_list_map_trans:
  "\<lbrakk> xs \<le> ys; list_map ys \<subseteq>\<^sub>m f \<rbrakk> \<Longrightarrow> list_map xs \<subseteq>\<^sub>m f"
  apply(drule list_map_mono)
  apply(erule (1) map_le_trans)
  done

lemma valid_footprint_le:
  "valid_footprint d x t \<Longrightarrow> size_td t \<le> addr_card"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply(rule ccontr)
  apply(frule_tac x=addr_card in spec)
  apply(drule_tac x=0 in spec)
  apply clarsimp
  apply(drule (1) map_prefix_same_cases)
  apply(simp add: typ_slice_0_prefix addr_card)
  done

lemma typ_slice_True_set':
  "\<forall>s k m. (s,True) \<in> set (typ_slice_t t k) \<longrightarrow> (s,k+m) \<in> td_set t m"
  "\<forall>s k m. (s,True) \<in> set (typ_slice_struct st k) \<longrightarrow> (s,k+m) \<in> td_set_struct st m"
  "\<forall>s k m. (s,True) \<in> set (typ_slice_list xs k) \<longrightarrow> (s,k+m) \<in> td_set_list xs m"
  "\<forall>s k m. (s,True) \<in> set (typ_slice_pair x k) \<longrightarrow> (s,k+m) \<in> td_set_pair x m"
  apply(induct t and st and xs and x)
       apply auto[4]
   apply clarsimp
   apply(case_tac dt_pair, clarsimp)
   apply(rename_tac a)
   apply(thin_tac "All P" for P)
   apply(drule_tac x=s in spec)
   apply(drule_tac x="k - size_td a" in spec)
   apply clarsimp
   apply(drule_tac x="m + size_td a" in spec)
   apply simp
  apply auto
  done

lemma typ_slice_True_set:
  "(s,True) \<in> set (typ_slice_t t k) \<Longrightarrow> (s,k+m) \<in> td_set t m"
  by (simp add: typ_slice_True_set')

lemma typ_slice_True_prefix:
  "typ_slice_t s 0 \<le> typ_slice_t t k \<Longrightarrow> (s,k) \<in> td_set t 0"
  using typ_slice_self [of s] typ_slice_True_set [of s t k 0]
  by (force simp: less_eq_list_def dest: set_mono_prefix)

lemma tag_sub_prefix [simp]:
  "t < s \<Longrightarrow> \<not> typ_slice_t s m \<le> typ_slice_t t n"
  by (fastforce dest: typ_slice_sub)

lemma tag_disj_prefix [simp]:
  "s \<bottom>\<^sub>t t \<Longrightarrow> \<not> typ_slice_t s m \<le> typ_slice_t t n"
  by (auto dest: typ_slice_sub simp: tag_disj_def typ_slice_sub)

lemma typ_slice_0_True':
  "\<forall>x. x \<in> set (typ_slice_t t 0) \<longrightarrow> snd x = True"
  "\<forall>x. x \<in> set (typ_slice_struct st 0) \<longrightarrow> snd x = True"
  "\<forall>x. x \<in> set (typ_slice_list xs 0) \<longrightarrow> snd x = True"
  "\<forall>x. x \<in> set (typ_slice_pair y 0) \<longrightarrow> snd x = True"
  by (induct t and st and xs and y)  auto

lemma typ_slice_0_True:
  "x \<in> set (typ_slice_t t 0) \<Longrightarrow> snd x = True"
  by (simp add: typ_slice_0_True')

lemma typ_slice_False_self:
  "k \<noteq> 0 \<Longrightarrow> (t,False) \<in> set (typ_slice_t t k)"
  by (cases t) simp

lemma tag_prefix_True:
  "typ_slice_t s k \<le> typ_slice_t t 0 \<Longrightarrow> k = 0"
  using typ_slice_0_True [of "(s,False)" t]
  apply(clarsimp simp: less_eq_list_def dest!: set_mono_prefix)
  apply(rule ccontr)
  apply(fastforce dest!: typ_slice_False_self[where t=s and k=k])
  done

lemma valid_footprint_neq_nmem:
  assumes valid_p: "valid_footprint d p f" and
          valid_q: "valid_footprint d q g" and
              neq: "p \<noteq> q" and
             disj: "f \<bottom>\<^sub>t g \<or> f=g"
  shows "p \<notin> {q..+size_td g}" (is ?G)
proof -
  from assms show ?thesis
    apply(clarsimp simp: valid_footprint_def intvl_def Let_def)
    apply(erule disjE)
     apply(drule_tac x=0 in spec)
     apply (fastforce dest: map_prefix_same_cases)
    apply(drule_tac x=0 in spec)
    apply(drule_tac x=k in spec)
    apply clarsimp
    by (meson of_nat_gt_0 typ_slice_0_prefix map_prefix_same_cases)
qed

lemma valid_footprint_sub:
  assumes valid_p: "valid_footprint d p s"
  assumes valid_q: "valid_footprint d q t"
  assumes sub: "\<not> t < s"
  shows "p \<notin> {q..+size_td t} \<or> field_of (p - q) (s) (t)" (is ?G)
proof -
  from assms show ?thesis
    apply clarsimp
    apply(insert valid_footprint_le[OF valid_q])
    apply(clarsimp simp: valid_footprint_def Let_def)
    apply(drule_tac x=0 in spec)
    apply clarsimp
    apply(drule intvlD)
    apply clarsimp
    apply(drule_tac x=k in spec)
    apply clarsimp
    apply(drule (1) map_prefix_same_cases)
    apply(erule disjE)
     prefer 2
     apply(frule typ_slice_sub)
     apply(subgoal_tac "k = 0")
      prefer 2
      apply(rule ccontr, simp)
      apply(simp add: typ_slice_0_prefix)
     apply simp
    (* given by the fd_tag_consistent condition *)
    apply(drule typ_slice_True_prefix)
    apply(clarsimp simp: field_of_def)
    apply(simp only: unat_simps)
    done
qed

lemma valid_footprint_sub2:
  "\<lbrakk> valid_footprint d p s; valid_footprint d q t; \<not> t < s \<rbrakk> \<Longrightarrow>
      q \<notin> {p..+size_td s} \<or> p=q"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply(drule intvlD)
  apply clarsimp
  apply(drule_tac x=k in spec)
  apply clarsimp
  apply(drule_tac x=0 in spec)
  apply clarsimp
  apply(drule (1) map_prefix_same_cases)
  apply(case_tac "k=0")
   apply simp
  apply(erule disjE)
   prefer 2
   apply(frule typ_slice_sub)
   apply(drule order_le_imp_less_or_eq[where x=t])
   apply clarsimp
   apply(simp add: typ_slice_0_prefix)
  apply(drule tag_prefix_True)
  apply simp
  done

lemma valid_footprint_neq_disjoint:
  "\<lbrakk> valid_footprint d p s; valid_footprint d q t; \<not>  t < s;
      \<not> field_of (p - q) (s) (t) \<rbrakk> \<Longrightarrow> {p..+size_td s} \<inter> {q..+size_td t} = {}"
  apply(rule ccontr)
  apply(drule intvl_inter)
  apply(erule disjE)
   apply(drule (2) valid_footprint_sub)
   apply clarsimp
  apply(frule (1) valid_footprint_sub2, assumption)
  apply(frule (1) valid_footprint_sub2)
   apply simp
  apply simp
  apply(clarsimp simp: field_of_def)
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply(drule_tac x=0 in spec)+
  apply clarsimp
  apply(drule (1) map_prefix_same_cases [where xs="typ_slice_t s 0"])
  apply(erule disjE)
   apply(drule typ_slice_True_prefix)
   apply simp
  apply(drule typ_slice_sub)
  apply(drule order_le_imp_less_or_eq)
  apply simp
  done

lemma sub_typ_proper_not_same [simp]:
  "\<not> t <\<^sub>\<tau> t"
  by (simp add: sub_typ_proper_def)

lemma sub_typ_proper_not_simple [simp]:
  "\<not> TYPE('a::c_type) <\<^sub>\<tau> TYPE('b::simple_mem_type)"
  apply(cases "typ_uinfo_t TYPE('b)", rename_tac typ_struct xs)
  apply(case_tac typ_struct, auto simp: sub_typ_proper_def)
  done

lemma field_of_sub:
  "field_of p s t \<Longrightarrow> s \<le> t"
  by (auto simp: field_of_def typ_tag_lt_def typ_tag_le_def)

lemma h_t_valid_neq_disjoint:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a::c_type ptr); d,g' \<Turnstile>\<^sub>t (q::'b::c_type ptr);
      \<not> TYPE('b) <\<^sub>\<tau> TYPE('a); \<not> field_of_t p q \<rbrakk> \<Longrightarrow> {ptr_val p..+size_of TYPE('a)} \<inter>
          {ptr_val q..+size_of TYPE('b)} = {}"
  by (fastforce dest: valid_footprint_neq_disjoint
                simp: size_of_def h_t_valid_def sub_typ_proper_def field_of_t_def)

lemma field_ti_sub_typ:
  "\<lbrakk> field_ti (TYPE('b::mem_type)) f = Some t; export_uinfo t = (typ_uinfo_t TYPE('a::c_type)) \<rbrakk> \<Longrightarrow>
      TYPE('a) \<le>\<^sub>\<tau> TYPE('b)"
  by (auto simp: field_ti_def sub_typ_def typ_tag_le_def typ_uinfo_t_def
           dest!: td_set_export_uinfoD td_set_field_lookupD
           split: option.splits)

lemma h_t_valid_neq_disjoint_simple:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a::simple_mem_type ptr); d,g' \<Turnstile>\<^sub>t (q::'b::simple_mem_type ptr) \<rbrakk>
      \<Longrightarrow> ptr_val p \<noteq> ptr_val q \<or> typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE('b)"
  apply(clarsimp simp: h_t_valid_def valid_footprint_def Let_def)
  apply(drule_tac x=0 in spec)+
  apply clarsimp
  apply(drule (1) map_prefix_same_cases[where xs="typ_slice_t (typ_uinfo_t TYPE('a)) 0"])
  apply(erule disjE; drule typ_slice_sub)
   apply(case_tac "typ_info_t TYPE('b)", rename_tac typ_struct xs)
   apply(case_tac "typ_struct"; fastforce simp: typ_tag_le_def typ_uinfo_t_def)
  apply(case_tac "typ_info_t TYPE('a)", rename_tac typ_struct xs)
  apply(case_tac "typ_struct"; simp add: typ_tag_le_def typ_uinfo_t_def)
  done

lemma h_val_heap_same:
  fixes p::"'a::mem_type ptr" and q::"'b::c_type ptr"
  assumes val_p: "d,g \<Turnstile>\<^sub>t p" and val_q: "d,g' \<Turnstile>\<^sub>t q" and
          subt: "\<not> TYPE('a) <\<^sub>\<tau> TYPE('b)" and nf: "\<not> field_of_t q p"
  shows "h_val (heap_update p v h) q = h_val h q"
proof -
  from val_p val_q subt nf
  have "{ptr_val p..+length (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p)))} \<inter>
        {ptr_val q..+size_of TYPE('b)} = {}"
    by (force dest: h_t_valid_neq_disjoint)
  hence "heap_list (heap_update_list (ptr_val p) (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p))) h)
                   (size_of TYPE('b)) (ptr_val q) = heap_list h (size_of TYPE('b)) (ptr_val q)"
     by - (erule heap_list_update_disjoint_same)
  thus ?thesis by (simp add: h_val_def heap_update_def)
qed

lemma peer_typI:
  "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b) \<Longrightarrow> peer_typ (a::'a::c_type itself) (b::'b::c_type itself)"
  by (simp add: peer_typ_def)

lemma peer_typD:
  "peer_typ TYPE('a::c_type) TYPE('b::c_type) \<Longrightarrow> \<not> TYPE('a) <\<^sub>\<tau> TYPE('b)"
  by (clarsimp simp: peer_typ_def tag_disj_def sub_typ_proper_def order_less_imp_le)

lemma peer_typ_refl [simp]:
  "peer_typ t t"
  by (simp add: peer_typ_def)

lemma peer_typ_simple [simp]:
  "peer_typ TYPE('a::simple_mem_type) TYPE('b::simple_mem_type)"
  apply(clarsimp simp: peer_typ_def tag_disj_def typ_tag_le_def typ_uinfo_t_def)
  apply(erule disjE)
   apply(case_tac "typ_info_t TYPE('b)", rename_tac typ_struct xs)
   apply(case_tac typ_struct; simp)
  apply(case_tac "typ_info_t TYPE('a)", rename_tac typ_struct xs)
  apply(case_tac typ_struct; simp)
  done

(* FIXME: remove *)
lemmas peer_typ_nlt = peer_typD

lemma peer_typ_not_field_of:
  "\<lbrakk> peer_typ TYPE('a::c_type) TYPE('b::c_type); ptr_val p \<noteq> ptr_val q \<rbrakk> \<Longrightarrow>
      \<not> field_of_t (q::'b ptr) (p::'a ptr)"
  by (fastforce simp: peer_typ_def field_of_t_def field_of_def tag_disj_def typ_tag_le_def
                      unat_eq_zero
                dest: td_set_size_lte)

lemma h_val_heap_same_peer:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a::mem_type ptr); d,g' \<Turnstile>\<^sub>t (q::'b::c_type ptr);
      ptr_val p \<noteq> ptr_val q; peer_typ TYPE('a) TYPE('b) \<rbrakk> \<Longrightarrow>
      h_val (heap_update p v h) q = h_val h q"
  apply(erule (1) h_val_heap_same)
   apply(erule peer_typ_nlt)
  apply(erule (1) peer_typ_not_field_of)
  done

lemma field_offset_footprint_cons_simp [simp]:
  "field_offset_footprint p (x#xs) = {Ptr &(p\<rightarrow>x)} \<union> field_offset_footprint p xs"
  unfolding field_offset_footprint_def by (cases x) auto

lemma heap_list_update_list:
  "\<lbrakk> n + x \<le> length v; length v < addr_card \<rbrakk> \<Longrightarrow>
      heap_list (heap_update_list p v h) n (p + of_nat x) = take n (drop x v)"
  apply(induct v arbitrary: n x p h; clarsimp)
  apply(rename_tac a list n x p h)
  apply(case_tac x; clarsimp)
   apply(case_tac n; clarsimp)
   apply (rule conjI)
    apply(subgoal_tac "heap_update_list (p + of_nat 1) list (h(p := a)) p = a", simp)
    apply(subst heap_update_list_same; simp)
   apply(metis add.right_neutral drop0 semiring_1_class.of_nat_0)
  apply(rename_tac nat)
  apply(drule_tac x=n in meta_spec)
  apply(drule_tac x=nat in meta_spec)
  apply(drule_tac x="p+1" in meta_spec)
  apply (simp add: add.assoc)
  done

lemma typ_slice_td_set':
  "\<forall>s m n k. (s,m + n) \<in> td_set t m \<and> k < size_td s \<longrightarrow>
      typ_slice_t s k \<le> typ_slice_t t (n + k)"
  "\<forall>s m n k. (s,m + n) \<in> td_set_struct st m \<and> k < size_td s \<longrightarrow>
      typ_slice_t s k \<le> typ_slice_struct st (n + k)"
  "\<forall>s m n k. (s,m + n) \<in> td_set_list ts m \<and> k < size_td s \<longrightarrow>
      typ_slice_t s k \<le> typ_slice_list ts (n + k)"
  "\<forall>s m n k. (s,m + n) \<in> td_set_pair x m \<and> k < size_td s \<longrightarrow>
      typ_slice_t s k \<le> typ_slice_pair x (n + k)"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: split_DTPair_all\<close>)
   apply(safe; clarsimp)
   apply(drule_tac x=s in spec)
   apply(drule_tac x=m in spec)
   apply(drule_tac x=0 in spec)
   apply fastforce
  apply (safe; clarsimp?)
    apply(fastforce dest: td_set_list_offset_le)
   apply(fastforce dest: td_set_offset_size_m)
  apply(rotate_tac)
  apply(drule_tac x=s in spec)
  apply(rename_tac a list s m n k)
  apply(drule_tac x="m + size_td a" in spec)
  apply(drule_tac x="n - size_td a" in spec)
  apply(drule_tac x="k" in spec)
  apply(erule impE)
   apply(subgoal_tac "m + size_td a + (n - size_td a) = m + n", simp)
   apply(fastforce dest: td_set_list_offset_le)
  apply(fastforce dest: td_set_list_offset_le)
  done

lemma typ_slice_td_set:
  "\<lbrakk> (s,n) \<in> td_set t 0; k < size_td s \<rbrakk> \<Longrightarrow>
      typ_slice_t s k \<le> typ_slice_t t (n + k)"
  using typ_slice_td_set'(1) [of t]
  apply(drule_tac x=s in spec)
  apply(drule_tac x=0 in spec)
  apply clarsimp
  done

lemma typ_slice_td_set_list:
  "\<lbrakk> (s,n) \<in> td_set_list ts 0; k < size_td s \<rbrakk> \<Longrightarrow>
      typ_slice_t s k \<le> typ_slice_list ts (n + k)"
  using typ_slice_td_set'(3) [of ts]
  apply(drule_tac x=s in spec)
  apply(drule_tac x=0 in spec)
  apply clarsimp
  done

lemma h_t_valid_sub:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'b::mem_type ptr);
      field_ti TYPE('b) f = Some t; export_uinfo t = (typ_uinfo_t TYPE('a)) \<rbrakk> \<Longrightarrow>
      d,(\<lambda>x. True) \<Turnstile>\<^sub>t ((Ptr &(p\<rightarrow>f))::'a::mem_type ptr)"
  apply(clarsimp simp: h_t_valid_def field_ti_def valid_footprint_def Let_def split: option.splits)
  apply(rule conjI)
   apply(simp add: typ_uinfo_t_def export_uinfo_def size_of_def [symmetric, where t="TYPE('a)"])
  apply clarsimp
  apply(drule_tac x="field_offset TYPE('b) f + y" in spec)
  apply(erule impE)
   apply(fastforce simp: field_offset_def field_offset_untyped_def typ_uinfo_t_def size_of_def
                   dest: td_set_offset_size td_set_field_lookupD field_lookup_export_uinfo_Some)
  apply clarsimp
  apply(frule td_set_field_lookupD)
  apply(clarsimp simp: field_lvalue_def ac_simps)
  apply(drule td_set_export_uinfoD)
  apply(drule typ_slice_td_set)
   apply(simp add: size_of_def typ_uinfo_t_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: field_offset_def ac_simps field_offset_untyped_def typ_uinfo_t_def export_uinfo_def)
  apply(erule (1) map_list_map_trans)
  done

lemma size_of_tag:
  "size_td (typ_uinfo_t t) = size_of t"
  by (simp add: size_of_def typ_uinfo_t_def)

lemma size_of_neq_implies_typ_uinfo_t_neq [simp]:
  "size_of TYPE('a::c_type) \<noteq> size_of TYPE('b::c_type) \<Longrightarrow> typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  by (metis size_of_tag)

lemma guard_mono_self[simp]:
  "guard_mono g g"
  by (fastforce dest: td_set_field_lookupD td_set_size_lte simp: guard_mono_def)

lemma field_lookup_offset_size:
  "field_lookup (typ_info_t TYPE('a::c_type)) f 0 = Some (t,n) \<Longrightarrow>
      size_td t + n \<le> size_td (typ_info_t TYPE('a))"
  by (fastforce dest: td_set_field_lookupD td_set_offset_size)

lemma sub_h_t_valid':
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a::mem_type ptr);
     field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b),n);
     guard_mono g (g'::'b::mem_type ptr_guard)  \<rbrakk> \<Longrightarrow>
   d,g' \<Turnstile>\<^sub>t ((Ptr (ptr_val p + of_nat n))::'b::mem_type ptr)"
  apply(clarsimp simp: h_t_valid_def guard_mono_def valid_footprint_def Let_def size_of_tag)
  apply(drule_tac x="n+y" in spec, erule impE;
        fastforce simp: ac_simps size_of_def typ_uinfo_t_def
                  dest: td_set_field_lookupD typ_slice_td_set map_list_map_trans td_set_offset_size)
  done

lemma sub_h_t_valid:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a::mem_type ptr); (typ_uinfo_t TYPE('b),n) \<in> td_set (typ_uinfo_t TYPE('a)) 0 \<rbrakk> \<Longrightarrow>
      d,(\<lambda>x. True) \<Turnstile>\<^sub>t ((Ptr (ptr_val p + of_nat n))::'b::mem_type ptr)"
  apply(subst (asm) td_set_field_lookup)
   apply(simp add: typ_uinfo_t_def export_uinfo_def wf_desc_map)
  apply(fastforce intro: sub_h_t_valid' simp: guard_mono_def)
  done

lemma h_t_valid_mono:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (s,n);
      export_uinfo s = typ_uinfo_t TYPE('b); guard_mono g g' \<rbrakk> \<Longrightarrow>
      d,g \<Turnstile>\<^sub>t (p::'a::mem_type ptr) \<longrightarrow> d,g' \<Turnstile>\<^sub>t (Ptr (&(p\<rightarrow>f))::'b::mem_type ptr)"
  apply(clarsimp simp: field_lvalue_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(clarsimp simp: field_offset_def typ_uinfo_t_def field_offset_untyped_def)
  apply(rule sub_h_t_valid'; fast?)
  apply(fastforce simp: typ_uinfo_t_def)
  done

lemma s_valid_mono:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (s,n);
      export_uinfo s = typ_uinfo_t TYPE('b); guard_mono g g' \<rbrakk> \<Longrightarrow>
      d,g \<Turnstile>\<^sub>s (p::'a::mem_type ptr) \<longrightarrow> d,g' \<Turnstile>\<^sub>s (Ptr (&(p\<rightarrow>f))::'b::mem_type ptr)"
  unfolding s_valid_def by (rule h_t_valid_mono)

lemma take_heap_list_le:
  "k \<le> n \<Longrightarrow> take k (heap_list h n x) = heap_list h k x"
  by (induct n arbitrary: k x; clarsimp) (case_tac k; simp)

lemma drop_heap_list_le:
  "k \<le> n \<Longrightarrow> drop k (heap_list h n x) = heap_list h (n - k) (x + of_nat k)"
  by (induct n arbitrary: k x; clarsimp) (case_tac k; simp add: ac_simps)

lemma h_val_field_from_bytes:
  "\<lbrakk> field_ti TYPE('a::{mem_type}) f = Some t;
     export_uinfo t = export_uinfo (typ_info_t TYPE('b::{mem_type})) \<rbrakk> \<Longrightarrow>
    h_val (hrs_mem h) (Ptr &(pa\<rightarrow>f) :: 'b ptr) = from_bytes (access_ti\<^sub>0 t (h_val (hrs_mem h) pa))"
  apply (clarsimp simp: field_ti_def h_val_def split: option.splits)
  apply (frule field_lookup_export_uinfo_Some)
  apply (frule_tac bs="heap_list (hrs_mem h) (size_of TYPE('a)) (ptr_val pa)" in fi_fa_consistentD)
   apply simp
  apply (clarsimp simp: field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def
                        field_names_def access_ti\<^sub>0_def)
  apply (subst drop_heap_list_le)
   apply(simp add: size_of_def)
   apply(drule td_set_field_lookupD)
   apply(drule td_set_offset_size)
   apply simp
  apply(subst take_heap_list_le)
   apply(simp add: size_of_def)
   apply(drule td_set_field_lookupD)
   apply(drule td_set_offset_size)
   apply simp
  apply (fold norm_bytes_def)
  apply (subgoal_tac "size_td t = size_of TYPE('b)")
   apply (clarsimp simp: norm)
  apply(clarsimp simp: size_of_def)
  apply(subst typ_uinfo_size [symmetric])
  apply(unfold typ_uinfo_t_def)
  apply(drule sym)
  apply simp
  done

lemma lift_typ_heap_mono:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
      lift_typ_heap g s (p::'a::mem_type ptr) = Some v;
      export_uinfo t = typ_uinfo_t TYPE('b); guard_mono g g' \<rbrakk> \<Longrightarrow>
          lift_typ_heap g' s (Ptr (&(p\<rightarrow>f))::'b::mem_type ptr) = Some (from_bytes (access_ti\<^sub>0 t v))"
  apply(clarsimp simp: lift_typ_heap_if split: if_split_asm)
  apply(rule conjI; clarsimp?)
   apply(clarsimp simp: heap_list_s_def)
   apply(frule field_lookup_export_uinfo_Some)
   apply(frule_tac bs="heap_list (proj_h s) (size_of TYPE('a)) (ptr_val p)" in fi_fa_consistentD; simp)
   apply(simp add: field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def
                   field_names_def access_ti\<^sub>0_def)
   apply(subst drop_heap_list_le)
    apply(simp add: size_of_def)
    apply(drule td_set_field_lookupD)
    apply(drule td_set_offset_size)
    apply simp
   apply(subst take_heap_list_le)
    apply(simp add: size_of_def)
    apply(drule td_set_field_lookupD)
    apply(drule td_set_offset_size)
    apply simp
   apply(fold norm_bytes_def)
   apply(subgoal_tac "size_td t = size_of TYPE('b)")
    apply(simp add: norm)
   apply(clarsimp simp: size_of_def)
   apply(subst typ_uinfo_size [symmetric])
   apply(unfold typ_uinfo_t_def)[1]
   apply(drule sym)
   apply simp
  apply (fastforce dest: s_valid_mono)
  done

lemma lift_t_mono:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
      lift_t g s (p::'a::mem_type ptr) = Some v;
      export_uinfo t = typ_uinfo_t TYPE('b); guard_mono g g' \<rbrakk> \<Longrightarrow>
          lift_t g' s (Ptr (&(p\<rightarrow>f))::'b::mem_type ptr) = Some (from_bytes (access_ti\<^sub>0 t v))"
  by (clarsimp simp: lift_t_def lift_typ_heap_mono)

lemma align_td_field_lookupD:
  "field_lookup (t::'a typ_desc) f m = Some (s, n) \<Longrightarrow> align_td s \<le> align_td t"
  by(simp add: align_td_field_lookup)

lemma align_td_uinfo:
  "align_td (typ_uinfo_t TYPE('a)) = align_td (typ_info_t TYPE('a::c_type))"
  by (clarsimp simp: typ_uinfo_t_def)

lemma align_field_uinfo:
  "align_field (typ_uinfo_t TYPE('a)) = align_field (typ_info_t TYPE('a::c_type))"
  by (force simp: align_field_def align_td_uinfo typ_uinfo_t_def
            dest: field_lookup_export_uinfo_Some_rev field_lookup_export_uinfo_Some)

lemma ptr_aligned_mono':
  "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b),n) \<Longrightarrow>
      ptr_aligned (p::'a::mem_type ptr) \<longrightarrow> ptr_aligned (Ptr (&(p\<rightarrow>f))::'b::mem_type ptr)"
  apply(clarsimp simp: ptr_aligned_def align_of_def field_lvalue_def)
  apply(subgoal_tac "align_field (typ_uinfo_t (TYPE('a)))")
   apply(subst (asm) align_field_def)
   apply(drule_tac x=f in spec)
   apply(drule_tac x="typ_uinfo_t TYPE('b)" in spec)
   apply(drule_tac x=n in spec)
   apply clarsimp
   apply(simp add: align_td_uinfo)
   apply(clarsimp simp: field_offset_def field_offset_untyped_def)
   apply(subst unat_word_ariths)
   apply(rule dvd_mod)
    apply(rule dvd_add)
     apply (metis align_td_field_lookup(1) align_td_uinfo power_le_dvd)
    apply(subst unat_of_nat)
    apply(subst mod_less)
     apply(frule td_set_field_lookupD)
     apply(drule td_set_offset_size)
     apply(subst len_of_addr_card)
     apply (metis (full_types) Groups.add_ac(2) add_lessD1 less_trans max_size nat_less_le size_of_tag)
    apply assumption
   apply(subst len_of_addr_card)
   apply(subgoal_tac "align_of TYPE('b) dvd addr_card")
    apply(subst (asm) align_of_def)
    apply simp
   apply simp
  apply(subst align_field_uinfo)
  apply(rule align_field)
  done

lemma ptr_aligned_mono:
  "guard_mono (ptr_aligned::'a::mem_type ptr_guard) (ptr_aligned::'b::mem_type ptr_guard)"
  apply(clarsimp simp: guard_mono_def)
  apply(frule ptr_aligned_mono')
  apply(fastforce simp: field_lvalue_def field_offset_def field_offset_untyped_def)
  done

lemma wf_desc_typ_tag [simp]:
  "wf_desc (typ_uinfo_t TYPE('a::wf_type))"
  by (simp add: typ_uinfo_t_def export_uinfo_def wf_desc_map)

lemma sft1':
  "sub_field_update_t (f#fs) p (v::'a::c_type) s =
     (let s' = sub_field_update_t fs p (v::'a::c_type) s in
        s'(Ptr &(p\<rightarrow>f) \<mapsto> from_bytes (access_ti\<^sub>0 (field_typ TYPE('a) f) v))) |`
        dom (s::'b::c_type typ_heap)"
  by (rule sft1)

lemma size_map_td:
  "size (map_td f t) = size t"
  "size (map_td_struct f st) = size st"
  "size_list (size_dt_pair size (\<lambda>_. 0)) (map_td_list f ts) = size_list (size_dt_pair size (\<lambda>_. 0)) ts"
  "size_dt_pair size (\<lambda>_. 0) (map_td_pair f x) = size_dt_pair size (\<lambda>_. 0) x"
  by (induct t and st and ts and x) auto

(* case where 'b is a field type of 'a *)

lemma field_names_size':
  "field_names t s \<noteq> [] \<longrightarrow> size s \<le> size (t::'a typ_info)"
  "field_names_struct st s \<noteq> [] \<longrightarrow> size s \<le> size (st::'a field_desc typ_struct)"
  "field_names_list ts s \<noteq> [] \<longrightarrow> size s \<le> size_list (size_dt_pair size (\<lambda>_. 0)) (ts::('a typ_info,field_name) dt_pair list)"
  "field_names_pair x s \<noteq> [] \<longrightarrow> size s \<le> size_dt_pair size (\<lambda>_. 0) (x::('a typ_info,field_name) dt_pair)"
  by (induct t and st and ts and x) (auto simp: size_map_td size_char_def)

lemma field_names_size:
  "f \<in> set (field_names t s) \<Longrightarrow> size s \<le> size t"
  by (cases "field_names t s"; simp add: field_names_size')

lemma field_names_size_struct:
  "f \<in> set (field_names_struct st s) \<Longrightarrow> size s \<le> size st"
  by (cases "field_names_struct st s"; simp add: field_names_size')

lemma field_names_Some3:
  "\<forall>f m s n. field_lookup (t::'a typ_info) f m = Some (s,n) \<longrightarrow>
     f \<in> set (field_names t (export_uinfo s))"
  "\<forall>f m s n. field_lookup_struct (st::'a field_desc typ_struct) f m = Some (s,n) \<longrightarrow>
     f \<in> set (field_names_struct  st (export_uinfo s))"
  "\<forall>f m s n. field_lookup_list (ts::('a typ_info,field_name) dt_pair list) f m = Some (s,n) \<longrightarrow>
     f \<in> set (field_names_list ts (export_uinfo s))"
  "\<forall>f m s n. field_lookup_pair (x::('a typ_info,field_name) dt_pair) f m = Some (s,n) \<longrightarrow>
     f \<in> set (field_names_pair x (export_uinfo s))"
  apply(induct t and st and ts and x)
       apply clarsimp
       apply((erule allE)+, erule impE, fast)
       apply simp
       apply(drule field_names_size_struct)
       apply(simp add: size_map_td)
      apply (auto split: option.splits)[4]
  apply clarsimp
  apply(case_tac f; fastforce)
  done

lemma field_names_SomeD3:
  "field_lookup (t::'a typ_info) f m = Some (s,n) \<Longrightarrow> f \<in> set (field_names t (export_uinfo s))"
  by (simp add: field_names_Some3)

lemma empty_not_in_field_names [simp]:
  "[] \<notin> set (field_names_pair x s)"
  by (case_tac x, auto)

lemma empty_not_in_field_names_list [simp]:
  "[] \<notin> set (field_names_list ts s)"
  by (induct_tac ts, auto)

lemma  empty_not_in_field_names_struct [simp]:
  "[] \<notin> set (field_names_struct st s)"
  by (case_tac st, auto)

lemma field_names_Some:
  "\<forall>m f. f \<in> set (field_names (t::'a typ_info) s) \<longrightarrow> (field_lookup t f m \<noteq> None)"
  "\<forall>m f. f \<in> set (field_names_struct (st::'a field_desc typ_struct) s) \<longrightarrow> (field_lookup_struct st f m \<noteq> None)"
  "\<forall>m f. f \<in> set (field_names_list (ts::('a typ_info,field_name) dt_pair list) s) \<longrightarrow> (field_lookup_list ts f m \<noteq> None)"
  "\<forall>m f. f \<in> set (field_names_pair (x::('a typ_info,field_name) dt_pair) s) \<longrightarrow> (field_lookup_pair x f m \<noteq> None)"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
   apply (safe; clarsimp?)
    apply(drule_tac x=m in spec)
    apply(drule_tac x=f in spec)
    apply clarsimp
   apply(clarsimp split: option.splits)
  apply(safe; clarsimp)
  apply(case_tac f; simp)
  done

lemma dt_snd_field_names_list_simp [simp]:
  "f \<notin> dt_snd ` set xs \<Longrightarrow> \<not> f#fs \<in> set (field_names_list xs s)"
  by (induct xs; clarsimp) (auto simp: split_DTPair_all)

lemma field_names_Some2:
  "\<forall>m f. wf_desc t \<longrightarrow> f \<in> set (field_names (t::'a typ_info) s) \<longrightarrow>
     (\<exists>n k. field_lookup t f m = Some (k,n) \<and> export_uinfo k = s)"
  "\<forall>m f. wf_desc_struct st \<longrightarrow> f \<in> set (field_names_struct (st::'a field_desc typ_struct) s) \<longrightarrow>
     (\<exists>n k. field_lookup_struct st f m = Some (k,n) \<and> export_uinfo k = s)"
  "\<forall>m f. wf_desc_list ts \<longrightarrow> f \<in> set (field_names_list (ts::('a typ_info,field_name) dt_pair list) s) \<longrightarrow>
      (\<exists>n k. field_lookup_list ts f m = Some (k,n) \<and> export_uinfo k = s)"
  "\<forall>m f. wf_desc_pair x \<longrightarrow> f \<in> set (field_names_pair (x::('a typ_info,field_name) dt_pair) s) \<longrightarrow>
      (\<exists>n k. field_lookup_pair x f m = Some (k,n) \<and> export_uinfo k = s )"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: export_uinfo_def\<close>)
   apply(safe; clarsimp?)
    apply(drule_tac x=m in spec)
    apply(fastforce simp: split: option.split)
   apply(clarsimp simp: split_DTPair_all)
   apply(case_tac f; fastforce)
  apply(safe; simp)
  apply(case_tac f; simp)
  done

lemma field_names_SomeD2:
  "\<lbrakk> f \<in> set (field_names (t::'a typ_info) s); wf_desc t \<rbrakk> \<Longrightarrow>
      (\<exists>n k. field_lookup t f m = Some (k,n) \<and> export_uinfo k = s)"
  by (simp add: field_names_Some2)

lemma field_names_SomeD:
  "f \<in> set (field_names (t::'a typ_info) s) \<Longrightarrow> (field_lookup t f m \<noteq> None)"
  by (simp add: field_names_Some)

lemma lift_t_sub_field_update' [rule_format]:
  "\<lbrakk> d,g' \<Turnstile>\<^sub>t p; \<not> (TYPE('a) <\<^sub>\<tau> TYPE('b)) \<rbrakk> \<Longrightarrow> fs_consistent fs TYPE('a) TYPE('b) \<longrightarrow>
      (\<forall>K. K = UNIV - (((field_offset_footprint p (field_names (typ_info_t TYPE('a)) (typ_uinfo_t TYPE('b))))) - (field_offset_footprint p fs)) \<longrightarrow>
      lift_t g (heap_update p (v::'a::mem_type) h,d) |` K =
           sub_field_update_t fs p v ((lift_t g (h,d))::'b::mem_type typ_heap) |` K)"
  apply(induct_tac fs)
   apply clarsimp
   apply(rule ext, rename_tac x)
   apply(clarsimp simp: lift_t_if restrict_map_def)
   apply(erule (2) h_val_heap_same)
   apply(clarsimp simp: field_of_t_def field_offset_footprint_def field_of_def)
   apply(case_tac x)
   apply(clarsimp simp: field_lvalue_def td_set_field_lookup field_offset_def field_offset_untyped_def)
   apply(drule_tac x=f in spec)
   apply(fastforce simp: typ_uinfo_t_def dest: field_lookup_export_uinfo_Some_rev field_names_SomeD3)
  apply(rename_tac a list)
  apply clarify
  apply(erule impE)
   apply(clarsimp simp: fs_consistent_def)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply(rule ext, rename_tac x)
   apply(case_tac "x \<noteq> Ptr &(p\<rightarrow>a)")
    apply(clarsimp simp: restrict_map_def)
    apply(drule_tac x=x in fun_cong)
    apply clarsimp
    apply(fastforce simp: lift_t_if split: if_split_asm)
   apply(clarsimp simp: lift_t_if)
   apply (rule conjI)
    apply clarsimp
    apply(clarsimp simp: h_val_def heap_update_def field_lvalue_def)
    apply(subst heap_list_update_list; simp?)
     apply(simp add: size_of_def)
     apply(clarsimp simp: fs_consistent_def)
     apply(subst typ_uinfo_size [symmetric])
     apply(subst typ_uinfo_size [symmetric])
     apply(drule_tac m=0 in field_names_SomeD2; clarsimp)
     apply(frule_tac m=0 in td_set_field_lookupD)
     apply(clarsimp simp: field_offset_def field_offset_untyped_def typ_uinfo_t_def)
     apply(drule field_lookup_export_uinfo_Some)
     apply simp
     apply(drule td_set_export_uinfoD)
     apply(simp add: export_uinfo_def)
     apply(drule td_set_offset_size)
     apply fastforce
    apply(clarsimp simp: fs_consistent_def)
    apply(drule_tac m=0 in field_names_SomeD2, clarsimp+)
    apply(frule_tac bs="to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p))"  in fi_fa_consistentD)
     apply simp
    apply(simp add: size_of_def)
    apply(frule field_lookup_export_uinfo_Some)
    apply(simp add: typ_uinfo_t_def)
    apply(subgoal_tac "size_td k = size_td (typ_info_t TYPE('b))")
     prefer 2
     apply(simp flip: export_uinfo_size)
    apply simp
    apply(rule sym)
    apply(fold norm_bytes_def)
    apply(subst typ_uinfo_size [symmetric])
    apply(drule_tac t="Some (k,n)" in sym)
    apply(simp only: typ_uinfo_t_def)
    apply(simp)
    apply(clarsimp simp: access_ti\<^sub>0_def field_typ_def field_typ_untyped_def)
    apply(drule_tac s="Some (k,n)" in sym)
    apply simp
    apply(rule norm)
    apply(simp add: size_of_def)
    apply(subst typ_uinfo_size [symmetric])+
    apply(drule td_set_field_lookupD, drule td_set_offset_size)
    apply(fastforce simp: min_def split: if_split_asm)
   apply(clarsimp split: if_split_asm)
  apply(rule ccontr, clarsimp)
  apply(erule notE, rule ext)
  apply(case_tac "x \<noteq> Ptr &(p\<rightarrow>a)")
   apply(clarsimp simp: restrict_map_def)
   apply(drule_tac x=x in fun_cong)
   apply clarsimp
   apply(rule ccontr, clarsimp)
   apply(erule_tac P="x \<in> dom (lift_t g (h, d))" in impE)
    apply(clarsimp simp: lift_t_if h_t_valid_def split: if_split_asm)
   apply clarsimp
  apply(clarsimp simp: restrict_map_def)
  apply(rule conjI, clarsimp)
  apply(clarsimp simp: lift_t_if)
  done

lemma lift_t_sub_field_update:
  "\<lbrakk> d,g' \<Turnstile>\<^sub>t p; \<not> (TYPE('a) <\<^sub>\<tau> TYPE('b))\<rbrakk> \<Longrightarrow>
      lift_t g (heap_update p (v::'a::mem_type) h,d) =
          sub_field_update_t (field_names (typ_info_t TYPE('a)) (typ_uinfo_t TYPE('b))) p v
              ((lift_t g (h,d))::'b::mem_type typ_heap)"
  apply(drule_tac fs="(field_names (typ_info_t TYPE('a)) (typ_uinfo_t TYPE('b)))" in lift_t_sub_field_update', assumption+)
    apply(clarsimp simp: fs_consistent_def)
   apply fast
  apply(simp add: restrict_map_def)
  done


(* Bornat-style *)

lemma intvl_disj_offset:
  "{x + a..+c} \<inter> {x + b..+d} = {} = ({a..+c} \<inter> {b..+d} = {})"
  by (force simp: intvl_def)

lemma intvl_sub_offset:
  "unat x+y \<le> z \<Longrightarrow> {k+x..+y} \<subseteq> {k..+z}"
  apply(clarsimp simp: intvl_def)
  apply(rule_tac x="unat x +  k" in exI)
  apply clarsimp
  done

lemma lift_t_field_ind:
  "\<lbrakk> d,g' \<Turnstile>\<^sub>t (p::'b::mem_type ptr); d,ga \<Turnstile>\<^sub>t (q::'b ptr);
      field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (a,ba);
      field_lookup (typ_info_t TYPE('b::mem_type)) z 0 = Some (c,da) ;
      size_td a = size_of TYPE('a); size_td c = size_of TYPE('c);
      \<not> f \<le> z; \<not> z \<le> f \<rbrakk> \<Longrightarrow>
      lift_t g (heap_update (Ptr (&(p\<rightarrow>f))) (v::'a::mem_type) h,d) (Ptr (&(q\<rightarrow>z))) =
          ((lift_t g (h,d) (Ptr (&(q\<rightarrow>z))))::'c::c_type option)"
  apply(clarsimp simp: lift_t_if h_val_def heap_update_def)
  apply(subgoal_tac "(heap_list (heap_update_list &(p\<rightarrow>f) (to_bytes v (heap_list h (size_of TYPE('a)) &(p\<rightarrow>f))) h)
                               (size_of TYPE('c)) &(q\<rightarrow>z)) =
                     (heap_list h (size_of TYPE('c)) &(q\<rightarrow>z))")
   apply(drule_tac f=from_bytes in arg_cong)
   apply simp
  apply(rule heap_list_update_disjoint_same)
  apply simp
  apply(simp add: field_lvalue_def field_offset_def field_offset_untyped_def)
  apply(simp add: typ_uinfo_t_def field_lookup_export_uinfo_Some)
  apply(frule field_lookup_export_uinfo_Some[where s=c])
  apply(case_tac "ptr_val p = ptr_val q")
   apply clarsimp
   apply(subst intvl_disj_offset)
   apply(drule fa_fu_lookup_disj_interD)
       apply fast
      apply(simp add: disj_fn_def)
     apply simp
    apply(subst size_of_def [symmetric, where t="TYPE('b)"])
    apply simp
   apply simp
  apply clarsimp
  apply(drule (1) h_t_valid_neq_disjoint, simp)
   apply(rule peer_typ_not_field_of; clarsimp)
  apply(subgoal_tac "{ptr_val p + of_nat ba..+size_td a} \<subseteq> {ptr_val p..+size_of TYPE('b)}")
   apply(subgoal_tac "{ptr_val q + of_nat da..+size_td c} \<subseteq> {ptr_val q..+size_of TYPE('b)}")
    apply fastforce
   apply(rule intvl_sub_offset)
   apply(simp add: size_of_def)
   apply(drule td_set_field_lookupD[where k="(c,da)"])
   apply(drule td_set_offset_size)
   apply(subst word_unat.eq_norm)
   apply(subst len_of_addr_card)
   apply(subst mod_less)
    apply (metis add_leD2 le_trans max_size not_le size_of_def)
   apply fastforce
  apply(rule intvl_sub_offset)
  apply(simp add: size_of_def)
  apply(drule td_set_field_lookupD)
  apply(drule td_set_offset_size)
  apply(subst word_unat.eq_norm)
  apply(subst len_of_addr_card)
  apply(subst mod_less)
   apply (metis le_Suc_ex le_add2 max_size not_le size_of_def trans_le_add1)
  apply simp
  done



(* case where 'b contains a field of type of 'a *)

lemma uvt1':
  "update_value_t (f#fs) v (w::'b) x = (if x=field_offset TYPE('b) f then
      update_ti_t (field_typ TYPE('b) f) (to_bytes_p (v::'a::c_type)) (w::'b::c_type) else update_value_t fs v w x)"
  by simp

lemma field_typ_self [simp]:
  "field_typ TYPE('a) [] = typ_info_t TYPE('a::c_type)"
  by (simp add: field_typ_def field_typ_untyped_def)

lemma field_of_t_less_size:
  "field_of_t (p::'a::mem_type ptr) (x::'b::c_type ptr) \<Longrightarrow>
    unat (ptr_val p - ptr_val x) < size_of TYPE('b)"
  apply(simp add: field_of_t_def field_of_def)
  apply(drule td_set_offset_size)
  apply(subgoal_tac "0 < size_td (typ_info_t TYPE('a)) ")
   apply(simp add: size_of_def)
  apply(simp add: size_of_def [symmetric, where t="TYPE('a)"])
  done

lemma unat_minus:
  "x \<noteq> 0 \<Longrightarrow> unat (- (x::addr)) = addr_card - unat x"
  apply(simp add: unat_def)
  apply(subst uint_word_ariths)
  apply(subst zmod_zminus1_eq_if)
  apply(simp split: if_split_asm)
  apply(rule conjI; clarsimp)
   apply(fastforce simp: uint_0_iff word_uint.inverse_norm dest: word_uint.Rep_inverse')
  apply(simp add: nat_diff_distrib addr_card)
  apply(subst mod_pos_pos_trivial; simp?)
  apply(rule order_less_le_trans, rule uint_lt2p)
  apply simp
  done

lemma field_of_t_nmem:
  "\<lbrakk> field_of_t p q; ptr_val p \<noteq> ptr_val (q::'b::mem_type ptr) \<rbrakk> \<Longrightarrow>
    ptr_val q \<notin> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)}"
  apply(clarsimp simp: field_of_t_def field_of_def intvl_def)
  apply(drule td_set_offset_size)
  apply(simp add: unat_minus size_of_def)
  apply(subgoal_tac "size_td (typ_info_t TYPE('b)) < addr_card")
   apply(simp only: unat_simps)
   apply(subst (asm) mod_less; simp)
   apply(simp flip: size_of_def [where t="TYPE('a)"])
   apply(erule less_trans)
   apply simp
  apply(simp flip: size_of_def[where t="TYPE('b)"])
  done

lemma field_of_t_init_neq_disjoint:
  "field_of_t p (x::'b::mem_type ptr) \<Longrightarrow>
    {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)} \<inter>
    {ptr_val x..+unat (ptr_val p - ptr_val x)} = {}"
  apply(cases "ptr_val p = ptr_val x", simp)
  apply(rule ccontr)
  apply(drule intvl_inter)
  apply(fastforce simp: field_of_t_nmem le_unat_uoi nat_less_le dest: intvlD)
  done

lemma field_of_t_final_neq_disjoint:
  "field_of_t (p::'a ptr) (x::'b ptr) \<Longrightarrow> {ptr_val p..+size_of TYPE('a::mem_type)} \<inter>
      {ptr_val p + of_nat (size_of TYPE('a))..+size_of TYPE('b::mem_type) -
          (unat (ptr_val p - ptr_val x) + size_of TYPE('a))} = {}"
  apply(rule ccontr)
  apply(drule intvl_inter)
  apply(erule disjE)
   apply(subgoal_tac "ptr_val p \<notin> {ptr_val p + of_nat (size_of TYPE('a)) ..+
                                     size_of TYPE('b) - (unat (ptr_val p - ptr_val x) +
                                     size_of TYPE('a))}")
    apply simp
   apply(rule intvl_offset_nmem)
    apply(rule intvl_self)
    apply(subst unat_of_nat)
    apply(subst mod_less)
     apply(subst len_of_addr_card)
     apply(rule max_size)
    apply(rule sz_nzero)
   apply(subst len_of_addr_card)
   apply(thin_tac "x \<in> S" for x S)
   apply(simp add: field_of_t_def field_of_def)
   apply(drule td_set_offset_size)
   apply(simp add: size_of_def)
   apply(subst unat_of_nat)
   apply(subst mod_less)
    apply(subst size_of_def [symmetric])
    apply(subst len_of_addr_card)
    apply(rule max_size)
   apply(subgoal_tac "size_of TYPE('b) < addr_card")
    apply(simp add: size_of_def)
   apply(rule max_size)
  apply(drule intvlD, clarsimp)
  apply(subst (asm) word_unat.norm_eq_iff [symmetric])
  apply(subst (asm) mod_less)
   apply(subst len_of_addr_card)
   apply(rule max_size)
  apply(subst (asm) mod_less)
   apply(subst len_of_addr_card)
   apply(erule less_trans)
   apply(rule max_size)
  apply simp
  done

lemma h_val_super_update_bs:
  "field_of_t p x \<Longrightarrow> h_val (heap_update p (v::'a::mem_type) h) (x::'b::mem_type ptr) =
      from_bytes (super_update_bs (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p)) ) (heap_list h (size_of TYPE('b)) (ptr_val x)) (unat (ptr_val p - ptr_val x)))"
  apply(simp add: h_val_def)
  apply(rule_tac f=from_bytes in arg_cong)
  apply(simp add: heap_update_def super_update_bs_def)
  apply(subst heap_list_split [of "unat (ptr_val p - ptr_val x)" "size_of TYPE('b)"])
   apply(drule field_of_t_less_size)
   apply simp
  apply simp
  apply(subst heap_list_update_disjoint_same)
   apply(drule field_of_t_init_neq_disjoint)
   apply simp
  apply(subst take_heap_list_le)
   apply(drule field_of_t_less_size)
   apply simp
  apply simp
  apply(subst heap_list_split [of "size_of TYPE('a)"
                                  "size_of TYPE('b) - unat (ptr_val p - ptr_val x)"])
   apply(frule field_of_t_less_size)
   apply(simp add: field_of_t_def field_of_def)
   apply(drule td_set_offset_size)
   apply(simp add: size_of_def)
  apply clarsimp
  apply (rule conjI)
   apply(simp add: heap_list_update_to_bytes)
  apply(subst heap_list_update_disjoint_same)
   apply(drule field_of_t_final_neq_disjoint)
   apply(simp)
  apply(subst drop_heap_list_le)
   apply(simp add: field_of_t_def field_of_def)
   apply(drule td_set_offset_size)
   apply(simp add: size_of_def)
  apply simp
  done

lemma update_field_update':
  "n \<in> (\<lambda>f. field_offset TYPE('b) f) ` set fs \<Longrightarrow>
      (\<exists>f. update_value_t fs (v::'a::c_type) (v'::'b::c_type) n =
          field_update (field_desc (field_typ TYPE('b) f)) (to_bytes_p v) v' \<and> f \<in> set fs \<and> n = field_offset TYPE('b) f)"
  by (induct fs) auto

lemma update_field_update:
  "field_of_t (p::'a ptr) (x::'b ptr) \<Longrightarrow>
      \<exists>f. update_value_t (field_names (typ_info_t TYPE('b)) (typ_uinfo_t TYPE('a))) (v::'a::c_type)
          (v'::'b::mem_type) (unat (ptr_val p - ptr_val x)) =
              field_update (field_desc (field_typ TYPE('b) f)) (to_bytes_p v) v' \<and>
      f \<in> set (field_names (typ_info_t TYPE('b)) (typ_uinfo_t TYPE('a))) \<and>
      unat (ptr_val p - ptr_val x) = field_offset TYPE('b) f"
  apply(rule update_field_update')
  apply(clarsimp simp: image_def field_offset_def field_of_t_def field_of_def field_offset_untyped_def)
  apply(simp add: td_set_field_lookup)
  apply clarsimp
  apply(simp add: typ_uinfo_t_def)
  apply(rule_tac x="f" in bexI, simp)
  apply(drule field_lookup_export_uinfo_Some_rev)
  apply clarsimp
  apply(drule field_names_SomeD3)
  apply clarsimp
  done

lemma length_fa_ti:
  "\<lbrakk> wf_fd s; length bs = size_td s \<rbrakk> \<Longrightarrow> length (access_ti s w bs) = size_td s"
  apply(drule wf_fd_consD)
  apply(clarsimp simp: fd_cons_def fd_cons_length_def fd_cons_desc_def)
  done

lemma fa_fu_v:
  "\<lbrakk> wf_fd s; length bs = size_td s; length bs' = size_td s \<rbrakk> \<Longrightarrow>
      access_ti s (update_ti_t s bs v) bs' = access_ti s (update_ti_t s bs w) bs'"
  apply(drule wf_fd_consD)
  apply(clarsimp simp: fd_cons_def fd_cons_access_update_def fd_cons_desc_def)
  done

lemma fu_fa:
  "\<lbrakk> wf_fd s; length bs = size_td s \<rbrakk> \<Longrightarrow>
      update_ti_t s (access_ti s v bs) v = v"
  apply(drule wf_fd_consD)
  apply(clarsimp simp: fd_cons_def fd_cons_update_access_def fd_cons_desc_def)
  done

lemma fu_fu:
  "\<lbrakk> wf_fd s; length bs = length bs' \<rbrakk> \<Longrightarrow>
        update_ti_t s bs (update_ti_t s bs' v) = update_ti_t s bs v"
  apply(drule wf_fd_consD)
  apply(clarsimp simp: fd_cons_def fd_cons_double_update_def fd_cons_desc_def)
  done


lemma fu_fa'_rpbs:
  "\<lbrakk> export_uinfo s = export_uinfo t; length bs = size_td s; wf_fd s; wf_fd t \<rbrakk> \<Longrightarrow>
       update_ti_t s (access_ti t v bs) w = update_ti_t s (access_ti\<^sub>0 t v) w"
  apply(clarsimp simp: access_ti\<^sub>0_def)
  apply(subgoal_tac "size_td s = size_td t")
   apply(frule_tac bs="access_ti t v bs" in wf_fd_norm_tuD[where t=t])
    apply(subst length_fa_ti; simp)
   apply(frule_tac bs="access_ti t v bs" in wf_fd_norm_tuD)
    apply(subst length_fa_ti; simp)
   apply(clarsimp simp: access_ti\<^sub>0_def)
   apply(thin_tac "norm_tu X Y = Z" for X Y Z)+
   apply(subst (asm) fa_fu_v [where w=v]; simp?)
    apply(simp add: length_fa_ti)
   apply(subst (asm) fa_fu_v [where w=w]; simp?)
    apply(simp add: length_fa_ti; simp)
   apply(subst (asm) fu_fa; (solves \<open>simp\<close>)?)
   apply(drule_tac f="update_ti_t s" in arg_cong)
   apply(drule_tac x="update_ti_t s (access_ti t v bs) w" in fun_cong)
   apply(subst (asm) fu_fa; (solves \<open>simp\<close>)?)
   apply(fastforce simp: fu_fu length_fa_ti)
  apply(drule_tac f=size_td in arg_cong)
  apply(simp add: export_uinfo_def)
  done

lemma lift_t_super_field_update:
  "\<lbrakk> d,g' \<Turnstile>\<^sub>t p; TYPE('a) \<le>\<^sub>\<tau> TYPE('b) \<rbrakk> \<Longrightarrow>
      lift_t g (heap_update p (v::'a::mem_type) h,d) =
      super_field_update_t p v ((lift_t g (h,d))::'b::mem_type typ_heap)"
  apply(rule ext)
  apply(clarsimp simp: super_field_update_t_def split: option.splits)
  apply(rule conjI; clarsimp)
   apply(simp add: lift_t_if split: if_split_asm)
  apply(rule conjI; clarsimp)
   apply(simp add: lift_t_if  h_val_super_update_bs split: if_split_asm)
   apply(drule sym)
   apply(rename_tac x1 x2)
   apply(drule_tac v=v and v'=x2 in update_field_update)
   apply(clarsimp simp: h_val_def)
   apply(frule_tac m=0 in field_names_SomeD)
   apply clarsimp
   apply(subgoal_tac "export_uinfo a = typ_uinfo_t TYPE('a)")
    prefer  2
    apply(drule_tac m=0 in field_names_SomeD2; clarsimp)
   apply(simp add: from_bytes_def)
   apply(frule_tac bs="heap_list h (size_of TYPE('b)) (ptr_val x1)" and
                   v="to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p))" and
                   w=undefined in fi_fu_consistentD)
      apply simp
     apply(simp add: size_of_def)
    apply(clarsimp simp: size_of_def sub_typ_def typ_tag_le_def simp flip: export_uinfo_size)
   apply(simp add: field_offset_def field_offset_untyped_def typ_uinfo_t_def)
   apply(frule field_lookup_export_uinfo_Some)
   apply(simp add: to_bytes_def to_bytes_p_def)
   apply(subst fu_fa'_rpbs; simp?)
     apply(simp add: size_of_def flip: export_uinfo_size)
    apply(fastforce intro: wf_fd_field_lookupD)
   apply(unfold access_ti\<^sub>0_def)[1]
   apply(simp flip: export_uinfo_size)
   apply(simp add: size_of_def access_ti\<^sub>0_def field_typ_def field_typ_untyped_def)
  apply(frule lift_t_h_t_valid)
  apply(simp add: lift_t_if)
  apply(cases "typ_uinfo_t TYPE('a) = typ_uinfo_t TYPE('b)")
   apply(subst h_val_heap_same_peer; assumption?)
    apply(clarsimp simp: field_of_t_def)
   apply(simp add: peer_typ_def)
  apply(drule (1) h_t_valid_neq_disjoint)
    apply(simp add: sub_typ_proper_def)
    apply(rule order_less_not_sym)
    apply(simp add: sub_typ_def)
   apply assumption
  apply(simp add: h_val_def heap_update_def heap_list_update_disjoint_same)
  done

lemma field_names_same:
  "k = export_uinfo ti \<Longrightarrow> field_names ti k = [[]]"
  by (case_tac ti, clarsimp)

lemma lift_t_heap_update:
  "d,g \<Turnstile>\<^sub>t p \<Longrightarrow> lift_t g (heap_update p v h,d) =
      (lift_t g (h,d) (p \<mapsto> (v::'a::mem_type)))"
  apply(subst lift_t_sub_field_update)
    apply fast
   apply(simp add: sub_typ_proper_def)
  apply(simp add: typ_uinfo_t_def Let_def)
  apply(subgoal_tac "access_ti\<^sub>0 (typ_info_t TYPE('a)) = to_bytes_p")
   apply(simp add: field_names_same)
   apply(clarsimp simp: Let_def to_bytes_p_def)
   apply(rule conjI, clarsimp)
    apply(rule ext, clarsimp simp: restrict_self_UNIV)
   apply clarsimp
   apply(clarsimp simp: h_t_valid_def lift_t_if)
  apply(rule ext)
  apply(simp add: to_bytes_p_def to_bytes_def size_of_def access_ti\<^sub>0_def)
  done

lemma field_names_disj:
  "typ_uinfo_t TYPE('a::c_type) \<bottom>\<^sub>t typ_uinfo_t TYPE('b::mem_type) \<Longrightarrow>
   field_names (typ_info_t TYPE('b)) (typ_uinfo_t TYPE('a)) = []"
  apply(rule ccontr)
  apply(subgoal_tac "(\<exists>k. k \<in> set (field_names (typ_info_t TYPE('b)) (typ_uinfo_t TYPE('a))))")
   apply clarsimp
   apply(frule_tac m=0 in field_names_SomeD2, clarsimp+)
   apply(drule field_lookup_export_uinfo_Some)
   apply(drule td_set_field_lookupD)
   apply(fastforce simp: tag_disj_def typ_tag_le_def typ_uinfo_t_def)
  apply(case_tac "field_names (typ_info_t TYPE('b)) (typ_uinfo_t TYPE('a))"; simp)
  apply fast
  done

lemma lift_t_heap_update_same:
  "\<lbrakk> d,g' \<Turnstile>\<^sub>t (p::'b::mem_type ptr); typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      lift_t g (heap_update p v h,d) = (lift_t g (h,d)::'a::mem_type typ_heap)"
  apply(subst lift_t_sub_field_update, simp)
   apply(fastforce dest: order_less_imp_le simp: sub_typ_proper_def tag_disj_def)
  apply(simp add: field_names_disj)
  done

lemma lift_heap_update:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a ptr); d,g' \<Turnstile>\<^sub>t q \<rbrakk> \<Longrightarrow> lift (heap_update p v h) q =
      ((lift h)(p := (v::'a::mem_type))) q"
  by (simp add: lift_def h_val_heap_update h_val_heap_same_peer)

lemma lift_heap_update_p [simp]:
  "lift (heap_update p v h) p = (v::'a::mem_type)"
  by (simp add: lift_def heap_update_def h_val_def heap_list_update_to_bytes)

lemma lift_heap_update_same:
  "\<lbrakk> ptr_val p \<noteq> ptr_val q; d,g \<Turnstile>\<^sub>t (p::'a::mem_type ptr);
      d,g' \<Turnstile>\<^sub>t (q::'b::mem_type ptr); peer_typ TYPE('a) TYPE('b) \<rbrakk>  \<Longrightarrow>
      lift (heap_update p v h) q = lift h q"
  by (simp add: lift_def h_val_heap_same_peer)

lemma lift_heap_update_same_type:
  fixes p::"'a::mem_type ptr" and q::"'b::mem_type ptr"
  assumes valid: "d,g \<Turnstile>\<^sub>t p" "d,g' \<Turnstile>\<^sub>t q"
  assumes type: "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
  shows "lift (heap_update p v h) q = lift h q"
proof -
  from valid type have "ptr_val p \<noteq> ptr_val q"
    apply(clarsimp simp: h_t_valid_def)
    apply(drule (1) valid_footprint_sub)
     apply(clarsimp simp: tag_disj_def order_less_imp_le)
    apply(fastforce intro: intvl_self
                    simp: field_of_def tag_disj_def typ_tag_le_def
                    simp flip: size_of_def [where t="TYPE('b)"])
    done
  thus ?thesis using valid type
    by (fastforce elim: lift_heap_update_same peer_typI)
qed

lemma lift_heap_update_same_ptr_coerce:
  "\<lbrakk> ptr_val q \<noteq> ptr_val p;
      d,g \<Turnstile>\<^sub>t (ptr_coerce (q::'b::mem_type ptr)::'c::mem_type ptr);
      d,g' \<Turnstile>\<^sub>t (p::'a::mem_type ptr);
      size_of TYPE('b) = size_of TYPE('c); peer_typ TYPE('a) TYPE('c) \<rbrakk>  \<Longrightarrow>
     lift (heap_update q v h) p = lift h p"
  apply(clarsimp simp: lift_def h_val_def heap_update_def size_of_def)
  apply(subst heap_list_update_disjoint_same)
   apply(drule (1) h_t_valid_neq_disjoint)
     apply(erule peer_typD)
    apply(erule peer_typ_not_field_of, simp)
   apply(simp add: size_of_def)
  apply simp
  done

lemma heap_footprintI:
  "\<lbrakk> valid_footprint d y t; x \<in> {y..+size_td t} \<rbrakk> \<Longrightarrow> x \<in> heap_footprint d t"
  by (force simp: heap_footprint_def)

lemma valid_heap_footprint:
  "valid_footprint d x t \<Longrightarrow> x \<in> heap_footprint d t"
  by (force simp: heap_footprint_def)

lemma heap_valid_footprint:
  "x \<in> heap_footprint d t \<Longrightarrow> \<exists>y. valid_footprint d y t \<and> x \<in> {y} \<union> {y..+size_td t}"
  by (simp add: heap_footprint_def)

lemma heap_footprint_Some:
  "x \<in> heap_footprint d t \<Longrightarrow> d x \<noteq> (False,Map.empty)"
  by (auto simp: heap_footprint_def intvl_def valid_footprint_def Let_def)


(* Retyping *)

lemma dom_tll_empty [simp]:
  "dom_tll p [] = {}"
  by (clarsimp simp: dom_tll_def)

lemma dom_s_upd [simp]:
  "dom_s (\<lambda>b. if b = p then (True,a) else d b) =
      (dom_s d - {(p,y) | y. True}) \<union> {(p,SIndexVal)} \<union> {(p,SIndexTyp n) | n. a n \<noteq> None}"
  unfolding dom_s_def by (cases "d p") auto

lemma dom_tll_cons [simp]:
  "dom_tll p (x#xs) = dom_tll (p + 1) xs \<union> {(p,SIndexVal)} \<union> {(p,SIndexTyp n) | n. x n \<noteq> None}"
  unfolding dom_tll_def
  apply (rule equalityI; clarsimp)
   apply (rule conjI; clarsimp)
    apply (metis (no_types) One_nat_def Suc_pred add_cancel_right_right less_Suc_eq less_trans
                            neq0_conv of_nat_1 of_nat_Suc)
   apply (metis (no_types) One_nat_def Suc_less_eq Suc_pred not_gr_zero nth_Cons_0 nth_Cons_pos
                           of_nat_Suc semiring_1_class.of_nat_0 surj_pair)
  apply (rule conjI, force)+
  apply force
  done

lemma one_plus_x_zero:
  "(1::addr) + of_nat x = 0 \<Longrightarrow> x \<ge> addr_card - 1"
  apply(simp add: addr_card)
  apply(subst (asm) of_nat_1 [symmetric])
  apply(subst (asm) Abs_fnat_homs)
  apply(subst (asm) Word.of_nat_0)
  apply(erule exE, rename_tac q)
  apply(case_tac q; simp)
  done

lemma htd_update_list_dom [rule_format, simp]:
  "length xs < addr_card \<longrightarrow> (\<forall>p d. dom_s (htd_update_list p xs d) = dom_s d \<union> dom_tll p xs)"
  by (induct xs; clarsimp) (auto simp: dom_s_def)

(* FIXME: this is clag from heap_update_list_same - should be able to prove
   this once for these kinds of update functions *)
lemma htd_update_list_same:
  shows "\<And>h p k. \<lbrakk> 0 < k; k \<le> addr_card - length v \<rbrakk> \<Longrightarrow>
      (htd_update_list (p + of_nat k) v) h p = h p"
proof (induct v)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have "htd_update_list (p + of_nat k) (x # xs) h p =
      htd_update_list (p + of_nat (k + 1)) xs (h(p + of_nat k := (True,snd (h (p + of_nat k)) ++ x))) p"
    by (simp add: ac_simps)
  also have "\<dots> = (h(p + of_nat k := (True,snd (h (p + of_nat k)) ++ x))) p"
  proof -
    from Cons have "k + 1 \<le> addr_card - length xs" by simp
    with Cons show ?thesis by (simp only:)
  qed
  also have "\<dots> = h p"
  proof -
    from Cons have "of_nat k \<noteq> (0::addr)"
      by - (erule of_nat_neq_0, simp add: addr_card)
    thus ?thesis by clarsimp
  qed
  finally show ?case .
qed

lemma htd_update_list_index [rule_format]:
  "\<forall>p d. length xs < addr_card \<longrightarrow> x \<in> {p..+length xs} \<longrightarrow>
         htd_update_list p xs d x = (True, snd (d x) ++ (xs ! (unat (x - p))))"
  apply(induct xs; clarsimp)
  apply(case_tac "p=x")
   apply simp
   apply(subst of_nat_1 [symmetric])
   apply(subst htd_update_list_same; simp)
  apply(drule_tac x="p+1" in spec)
  apply(erule impE)
   apply(drule intvl_neq_start; simp)
  apply(subgoal_tac "unat (x - p) = unat (x - (p + 1)) + 1")
   apply simp
  apply (clarsimp simp: unatSuc[symmetric] field_simps)
  done

lemma typ_slices_length [simp]:
  "length (typ_slices TYPE('a::c_type)) = size_of TYPE('a)"
  by (simp add: typ_slices_def)

lemma typ_slices_index [simp]:
  "n < size_of TYPE('a::c_type) \<Longrightarrow> typ_slices TYPE('a) ! n =
     list_map (typ_slice_t (typ_uinfo_t TYPE('a)) n)"
  by (simp add: typ_slices_def)

lemma empty_not_in_typ_slices [simp]:
  "Map.empty \<notin> set (typ_slices TYPE('a::c_type))"
  by (auto simp: typ_slices_def dest: sym)

lemma dom_tll_s_footprint [simp]:
  "dom_tll (ptr_val p) (typ_slices TYPE('a)) = s_footprint (p::'a::c_type ptr)"
  by (fastforce simp: list_map_eq typ_slices_def s_footprint_def s_footprint_untyped_def
                      dom_tll_def size_of_def
                split: if_split_asm)

lemma ptr_retyp_dom [simp]:
  "dom_s (ptr_retyp (p::'a::mem_type ptr) d) = dom_s d \<union> s_footprint p"
  by (simp add: ptr_retyp_def)

lemma dom_s_empty_htd [simp]:
  "dom_s empty_htd = {}"
  by (clarsimp simp: empty_htd_def dom_s_def)

lemma dom_s_nempty:
  "d x \<noteq> (False, Map.empty) \<Longrightarrow> \<exists>k. (x,k) \<in> dom_s d"
  apply(clarsimp simp: dom_s_def)
  apply(cases "d x", clarsimp)
  using None_not_eq by fastforce

lemma ptr_retyp_None:
  "x \<notin> {ptr_val p..+size_of TYPE('a)} \<Longrightarrow>
    ptr_retyp (p::'a::mem_type ptr) empty_htd x = (False,Map.empty)"
  using ptr_retyp_dom [of p empty_htd]
  by (fastforce dest: dom_s_nempty s_footprintD)

lemma ptr_retyp_footprint:
  "x \<in> {ptr_val p..+size_of TYPE('a)} \<Longrightarrow>
      ptr_retyp (p::'a::mem_type ptr) d x =
        (True,snd (d x) ++ list_map (typ_slice_t (typ_uinfo_t TYPE('a)) (unat (x - ptr_val p))))"
  apply(clarsimp simp: ptr_retyp_def)
  apply(subst htd_update_list_index; simp)
  apply(subst typ_slices_index; simp?)
  apply(drule intvlD, clarsimp)
  apply(subst unat_simps)
  apply(subst mod_less)
   apply(subst len_of_addr_card)
   apply(erule less_trans)
   apply(rule max_size)
  apply simp
  done

lemma ptr_retyp_Some:
  "ptr_retyp (p::'a::mem_type ptr) d (ptr_val p) =
     (True,snd (d (ptr_val p)) ++ list_map (typ_slice_t (typ_uinfo_t TYPE('a)) 0))"
  by (simp add: ptr_retyp_footprint)

lemma ptr_retyp_Some2:
  "x \<in> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)} \<Longrightarrow> ptr_retyp p d x \<noteq> (False,Map.empty)"
  by (auto simp: ptr_retyp_Some ptr_retyp_footprint dest: intvl_neq_start)

lemma snd_empty_htd [simp]:
  "snd (empty_htd x) = Map.empty"
  by (auto simp: empty_htd_def)

lemma ptr_retyp_d_empty:
  "x \<in> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)} \<Longrightarrow>
      (\<forall>d. fst (ptr_retyp p d x)) \<and>
      snd (ptr_retyp p d x) = snd (d x) ++ snd (ptr_retyp p empty_htd x)"
 by (auto simp: ptr_retyp_Some ptr_retyp_footprint dest: intvl_neq_start)

lemma unat_minus_abs:
  "x \<noteq> y \<Longrightarrow> unat ((x::addr) - y) = addr_card - unat (y - x)"
  by (clarsimp simp: unat_sub_if_size)
     (metis (no_types) Nat.diff_cancel Nat.diff_diff_right add.commute len_of_addr_card
                       nat_le_linear not_le trans_le_add1 unat_lt2p wsst_TYs(3))

lemma ptr_retyp_d:
  "x \<notin> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)} \<Longrightarrow>
      ptr_retyp p d x = d x"
  apply(simp add: ptr_retyp_def)
  apply(subgoal_tac "\<exists>k. ptr_val p = x + of_nat k \<and> 0 < k \<and> k \<le> addr_card - size_of TYPE('a)")
   apply clarsimp
   apply(subst htd_update_list_same; simp)
  apply(rule_tac x="unat (ptr_val p - x)" in exI)
  apply clarsimp
  apply(cases "ptr_val p = x")
   apply simp
   apply(erule notE)
   apply(rule intvl_self)
   apply simp
  apply(rule conjI)
   apply(subst unat_gt_0)
   apply clarsimp
  apply(rule ccontr)
  apply(erule notE)
  apply(clarsimp simp: intvl_def)
  apply(rule_tac x="unat (x - ptr_val p)" in exI)
  apply simp
  apply(subst (asm) unat_minus_abs; simp)
  done

lemma ptr_retyp_valid_footprint_disjoint:
  "\<lbrakk> valid_footprint d p s; {p..+size_td s} \<inter> {ptr_val q..+size_of TYPE('b)} = {} \<rbrakk>
     \<Longrightarrow> valid_footprint (ptr_retyp (q::'b::mem_type ptr) d) p s"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply((subst ptr_retyp_d; clarsimp), fastforce intro: intvlI)+
  done

lemma ptr_retyp_disjoint:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (q::'b::mem_type ptr); {ptr_val p..+size_of TYPE('a)} \<inter>
      {ptr_val q..+size_of TYPE('b)} = {} \<rbrakk> \<Longrightarrow>
      ptr_retyp (p::'a::mem_type ptr) d,g \<Turnstile>\<^sub>t q"
  apply(clarsimp simp: h_t_valid_def)
  apply(erule ptr_retyp_valid_footprint_disjoint)
  apply(fastforce simp: size_of_def)
  done

lemma ptr_retyp_d_fst:
  "(x,SIndexVal) \<notin> s_footprint (p::'a::mem_type ptr) \<Longrightarrow> fst (ptr_retyp p d x) = fst (d x)"
  apply(simp add: ptr_retyp_def)
  apply(subgoal_tac "\<exists>k. ptr_val p = x + of_nat k \<and> 0 < k \<and> k \<le> addr_card - size_of TYPE('a)")
   apply(fastforce simp: htd_update_list_same)
  apply(rule_tac x="unat (ptr_val p - x)" in exI)
  apply clarsimp
  apply(cases "ptr_val p = x")
   apply(fastforce dest: sym)
  apply(rule conjI)
   apply(subst unat_gt_0, clarsimp)
  apply(rule ccontr)
  apply(erule notE)
  apply(subst (asm) unat_minus_abs, simp)
  apply(clarsimp simp: s_footprint_def s_footprint_untyped_def)
  apply(rule_tac x="unat (x - ptr_val p)" in exI)
  apply(simp add: size_of_def)
  done

lemma ptr_retyp_d_eq_fst:
  "fst (ptr_retyp p d x) =
     (if x \<in> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)} then True else fst (d x))"
  by (auto dest!: ptr_retyp_d_empty[where d=d] ptr_retyp_d[where d=d])

lemma ptr_retyp_d_eq_snd:
  "snd (ptr_retyp p d x) =
     (if x \<in> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)}
      then snd (d x) ++ snd (ptr_retyp p empty_htd x)
      else snd (d x))"
  by (auto dest!: ptr_retyp_d_empty[where d=d] ptr_retyp_d[where d=d])

lemma lift_state_ptr_retyp_d_empty:
  "x \<in> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)} \<Longrightarrow>
      lift_state (h,ptr_retyp p d) (x,k) =
      (lift_state (h,d) ++ lift_state (h,ptr_retyp p empty_htd)) (x,k)"
  apply(clarsimp simp: lift_state_def map_add_def split: s_heap_index.splits)
  apply safe
     apply(subst ptr_retyp_d_empty; simp)
    apply(subst ptr_retyp_d_empty; simp)
   apply(subst (asm) ptr_retyp_d_empty; simp)
  apply(subst ptr_retyp_d_empty, simp)
  apply(auto split: option.splits)
  done

lemma lift_state_ptr_retyp_d:
  "x \<notin> {ptr_val (p::'a::mem_type ptr)..+size_of TYPE('a)} \<Longrightarrow>
      lift_state (h,ptr_retyp p d) (x,k) = lift_state (h,d) (x,k)"
  by (clarsimp simp: lift_state_def ptr_retyp_d split: s_heap_index.splits)

lemma ptr_retyp_valid_footprint:
  "valid_footprint (ptr_retyp p d) (ptr_val (p::'a::mem_type ptr)) (typ_uinfo_t TYPE('a))"
  apply(clarsimp simp: valid_footprint_def Let_def)
  apply(subst size_of_def [symmetric, where t="TYPE('a)"])
  apply clarsimp
  apply(subst ptr_retyp_footprint)
   apply(rule intvlI)
   apply(simp add: size_of_def)
  apply(subst ptr_retyp_footprint)
   apply(rule intvlI)
   apply(simp add: size_of_def)
  apply clarsimp
  apply(subst unat_of_nat)
  apply(subst mod_less)
   apply(subst len_of_addr_card)
   apply(erule less_trans)
   apply(subst size_of_def [symmetric, where t="TYPE('a)"])
   apply(rule max_size)
  apply simp
  done

lemma ptr_retyp_h_t_valid:
  "g p \<Longrightarrow> ptr_retyp p d,g \<Turnstile>\<^sub>t (p::'a::mem_type ptr)"
  by (simp add: h_t_valid_def ptr_retyp_valid_footprint)

lemma ptr_retyp_s_valid:
  "g p \<Longrightarrow> lift_state (h,ptr_retyp p d),g \<Turnstile>\<^sub>s (p::'a::mem_type ptr)"
  by (simp add: s_valid_def proj_d_lift_state ptr_retyp_h_t_valid)

lemma lt_size_of_unat_simps:
  "k < size_of TYPE('a) \<Longrightarrow> unat ((of_nat k)::addr) < size_of TYPE('a::mem_type)"
  by (metis le_def le_unat_uoi less_trans)

lemma ptr_retyp_h_t_valid_same:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t (p::'a::mem_type ptr); x \<in> {ptr_val p..+size_of TYPE('a)} \<rbrakk> \<Longrightarrow>
       snd (ptr_retyp p d x) \<subseteq>\<^sub>m snd (d x)"
  apply(clarsimp simp: h_t_valid_def valid_footprint_def Let_def)
  apply(subst ptr_retyp_footprint)
   apply simp
  apply clarsimp
  apply(drule_tac x="unat (x - ptr_val p)" in spec)
  apply clarsimp
  apply(erule impE)
   apply(simp only: size_of_def [symmetric, where t="TYPE('a)"])
   apply(drule intvlD, clarsimp)
   apply(simp only: lt_size_of_unat_simps)
  apply(fastforce intro: map_add_le_mapI)
  done

lemma ptr_retyp_ptr_safe [simp]:
  "ptr_safe p (ptr_retyp (p::'a::mem_type ptr) d)"
  by (force intro: h_t_valid_ptr_safe ptr_retyp_h_t_valid)


lemma lift_state_ptr_retyp_restrict:
  "(lift_state (h, ptr_retyp p d) |` {(x,k). x \<in> {ptr_val p..+size_of TYPE('a)}}) =
      (lift_state (h,d) |` {(x,k). x \<in> {ptr_val p..+size_of TYPE('a)}}) ++
      lift_state (h, ptr_retyp (p::'a::mem_type ptr) empty_htd)" (is "?x = ?y")
proof (rule ext, cases)
  fix x::"addr \<times> s_heap_index"
  assume "fst x \<in> {ptr_val p..+size_of TYPE('a)}"
  thus "?x x = ?y x"
    apply(cases x)
    apply(clarsimp simp: lift_state_def map_add_def split: s_heap_index.splits)
    apply(safe; clarsimp)
        apply(drule ptr_retyp_d_empty, fast)
       apply(frule_tac d=d in ptr_retyp_d_empty, clarsimp simp: map_add_def)
       apply(clarsimp simp: restrict_map_def split: option.splits)
      apply(drule ptr_retyp_d_empty, fast)
     apply(drule ptr_retyp_d_empty, fast)
    apply(frule_tac d=d in ptr_retyp_d_empty, clarsimp simp: map_add_def)
    apply(clarsimp simp: restrict_map_def split: option.splits)
    done
next
  fix x::"addr \<times> s_heap_index"
  assume "fst x \<notin> {ptr_val p..+size_of TYPE('a)}"
  thus "?x x = ?y x"
    by (cases x) (auto simp: lift_state_def ptr_retyp_None map_add_def split: s_heap_index.splits)
qed

(* Old set of simps, not all that useful in general, below specialised
   simp sets are given *)
lemmas typ_simps = lift_t_heap_update lift_t_heap_update_same lift_heap_update
                   lift_t_h_t_valid h_t_valid_ptr_safe lift_t_ptr_safe lift_lift_t lift_t_lift
                   tag_disj_def typ_tag_le_def  typ_uinfo_t_def

declare field_desc_def [simp del]

lemma field_fd:
  "field_fd (t::'a::c_type itself) n =
     (case field_lookup (typ_info_t TYPE('a)) n 0 of
        None \<Rightarrow> field_desc (fst (the (None::('a typ_info \<times> nat) option)))
      | Some x \<Rightarrow> field_desc (fst x))"
  by (auto simp: field_fd_def field_typ_def field_typ_untyped_def split: option.splits)

declare field_desc_def [simp add]

lemma super_field_update_lookup:
  assumes "field_lookup (typ_info_t TYPE('b)) f 0 = Some (s,n)"
    and "typ_uinfo_t TYPE('a) = export_uinfo s"
    and "lift_t g h p = Some v'"
  shows "super_field_update_t (Ptr (&(p\<rightarrow>f))) (v::'a::mem_type) (lift_t g h::'b::mem_type typ_heap) =
           (lift_t g h)(p \<mapsto> field_update (field_desc s) (to_bytes_p v) v')"
proof -
  from assms have "size_of TYPE('b) < addr_card" by simp
  with assms have [simp]: "unat (of_nat n :: addr_bitsize word) = n"
    apply(subst unat_of_nat)
    apply(subst mod_less)
     apply(drule td_set_field_lookupD)+
     apply(drule td_set_offset_size)+
     apply(subst len_of_addr_card)
     apply(subst (asm) size_of_def [symmetric, where t="TYPE('b)"])+
     apply arith
    apply simp
    done
  from assms show ?thesis
    apply(clarsimp simp: super_field_update_t_def)
    apply(rule ext)
    apply(clarsimp simp: field_lvalue_def split: option.splits)
    apply(safe; clarsimp?)
       apply(frule_tac v=v and v'=v' in update_field_update)
       apply clarsimp
       apply(thin_tac "P = update_ti_t x y z" for P x y z)
       apply(clarsimp simp: field_of_t_def field_of_def typ_uinfo_t_def)
       apply(frule_tac m=0 in field_names_SomeD2; clarsimp)
       apply(simp add: field_typ_def field_typ_untyped_def)
       apply(frule field_lookup_export_uinfo_Some)
       apply(frule_tac s=k in field_lookup_export_uinfo_Some)
       apply simp
       apply(drule (1) field_lookup_inject)
        apply(subst typ_uinfo_t_def [symmetric, where t="TYPE('b)"])
        apply simp
       apply simp
      apply(drule field_of_t_mem)+
      apply(cases h)
      apply(clarsimp simp: lift_t_if split: if_split_asm)
      apply(drule (1) h_t_valid_neq_disjoint)
        apply simp
       apply(fastforce simp: unat_eq_zero field_of_t_def field_of_def dest!: td_set_size_lte)
      apply fast
     apply(clarsimp simp: field_of_t_def field_of_def td_set_field_lookup)
     apply(fastforce simp: typ_uinfo_t_def dest: field_lookup_export_uinfo_Some)
    apply(clarsimp simp: field_of_t_def field_of_def td_set_field_lookup)
    apply(fastforce simp: typ_uinfo_t_def dest: field_lookup_export_uinfo_Some)
    done
qed


(* Should use these in lift/heap_update reductions *)
lemmas typ_rewrs =
  lift_lift_t
  lift_t_heap_update
  lift_t_heap_update_same
  lift_t_heap_update [OF lift_t_h_t_valid]
  lift_t_heap_update_same [OF lift_t_h_t_valid]
  lift_lift_t [OF lift_t_h_t_valid]

end
