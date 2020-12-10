theory ComputationConGlob imports "ComputationCon"
begin
section \<open>Auxiliary lemmas\<close>

lemma eq_list_i:
  assumes a0:"length ba = length b" and a1:"\<forall>j. j \<noteq> i \<longrightarrow> ba ! j = b ! j" and 
          a3:"i < length b" 
        shows " take i b @ drop (Suc i) b = take i ba @ drop (Suc i) ba"
proof-
  have "b=  take i b @ b!i # drop (Suc i) b" and "ba =  take i ba @ ba!i # drop (Suc i) ba"
    using  a0 a3 by (auto simp add: id_take_nth_drop) 
  then have  "\<forall>j<i. take i b = take i ba" using a0 a1 a3
    by (metis less_imp_le_nat less_irrefl_nat nth_take_lemma)
  moreover have  "\<forall>j< length ( drop (Suc i) ba).  drop (Suc i) b!j = drop (Suc i) ba!j"
    using a0 a1 a3
    by simp
  ultimately show ?thesis using a0 a3
    by (metis append_Nil append_eq_conv_conj length_drop linorder_neqE_nat list.size(3) not_less_zero nth_equalityI)
qed   

section \<open>Computation: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sub>i\<^sub>c\<^sub>e  (c', s')"}\<close>

type_synonym ('g,'l) par_state = "('g \<times> 'l list)"
type_synonym ('g,'l,'p,'f,'e) gconf = "('g \<times> 'l,'p,'f,'e)com  \<times> ((('g,'l)par_state,'f) xstate)"
type_synonym ('g,'l,'p,'f,'e) gconfs = "('g\<times>'l,'p,'f,'e) body \<times> (('g,'l,'p,'f,'e) gconf) list"
type_synonym ('s,'f) tran = "('s,'f) xstate \<times> ('s,'f) xstate"


definition toParState::"nat \<Rightarrow> ('g\<times>'l)\<times>('l list) \<Rightarrow>   ('g,'l)par_state"
  where "toParState i s \<equiv> let ((g,l),ls) = s in
             (g, (take i ls)@ (l#(drop i ls)))"

lemma toPar_li:"i \<le> length ls  \<Longrightarrow>
       (g',ls') = toParState i ((g,l),ls) \<Longrightarrow>
       ls' ! i = l"
  unfolding toParState_def 
  by (auto, metis (no_types) length_take min.absorb2 nth_append_length)

lemma toPar_gi:"
       (g',ls') = toParState i ((g,l),ls) \<Longrightarrow>
       g' = g"
  unfolding toParState_def Let_def by auto

lemma toPar_ljlti:assumes a0:"i \<le> length ls" and a1:"j< i" and
       a2:"(g',ls') = toParState i ((g,l),ls)"
     shows" ls' ! j = ls!j"
proof -
  have "\<forall>as. take i as = take i ls \<or> ls' \<noteq> as"
    using a2 a0 
    unfolding toParState_def by (simp add: append_eq_conv_conj min.absorb2)
  then show ?thesis
    using a2
    by (metis a1 nth_take)
qed 


lemma toPar_ljgti:assumes a0:"i \<le> length ls" and a1:"j > i" and a1': "j< length ls'" and
       a2:"(g',ls') = toParState i ((g,l),ls)"
     shows" ls' ! j = ls!(j-1)" 
proof-  
  have ls':"ls' = take i ls @ l # drop i ls" using a2 unfolding toParState_def by auto
  then have "length ls' = length ls+1"
    by auto
  have j:"j < Suc (min (length ls) i + length ls - i)"
    using a0 a1 a1' a2 unfolding toParState_def by auto  
  moreover { assume "(length ls) \<le> i + length ls - i"    
    then have ?thesis using ls' a0 a1 ls'
      by (auto simp add: min.absorb2 nth_append)
  }
  moreover
  {assume "(length ls) > i + length ls - i"    
    then have ?thesis using ls' a0 a1 ls'
      using diff_add_inverse min.strict_order_iff by auto
  }
  ultimately show ?thesis by auto
qed 

lemma len_toParState:"length (snd (toParState i s )) = length (snd s) +1"
  unfolding toParState_def Let_def split_beta
  by simp

definition toSeqState::"nat \<Rightarrow>  ('g,'l)par_state \<Rightarrow> ('g\<times>'l)\<times>('l list)"
  where "toSeqState i s \<equiv> let (g,ls) = s in ((g,ls!i), take i ls @ drop (i+1) ls)"

lemma len_toSeqState:"i<length (snd s) \<Longrightarrow> length (snd (toSeqState i s)) = length (snd s) -1"
  unfolding toSeqState_def Let_def split_beta
  by simp

lemma i_less_toSeq:"i<length (snd (toSeqState i s)) \<Longrightarrow> i<length (snd s)"
  unfolding toSeqState_def Let_def split_beta
  by (metis Suc_eq_plus1 append_Nil2 drop_all 
       less_imp_le_nat not_le_imp_less not_less_eq snd_conv take_all)

lemma Par2Seq0:"i\<le>length ls \<Longrightarrow> toSeqState i (toParState i (g,ls)) = (g,ls)"
proof (induct  rule: rev_induct)
  case Nil
  then show ?case  unfolding toSeqState_def toParState_def
    by (simp add: split_beta)
next
  case (snoc x xs)
  then show ?case unfolding toSeqState_def toParState_def Let_def
  proof(auto simp add: split_beta)
    assume "i \<le> Suc (length xs)"    
    then show "(fst g,
         (take i xs @ take (i - length xs) [x] @ snd g # drop i xs @ drop (i - length xs) [x]) ! i) =
        g"
      by (metis append_assoc eq_snd_iff fst_conv length_append_singleton 
          length_take min.absorb2 nth_append_length take_append)
  next
    assume a0:"i \<le> length xs \<Longrightarrow>
     (fst g, (take i xs @ snd g # drop i xs) ! i) = g \<and>
     take i xs @ drop (Suc i - min (length xs) i) (snd g # drop i xs) = xs" and
        a1:"i \<le> Suc (length xs)"
    show "take i xs @
        take (min (i - min (length xs) i) (i - length xs)) [x] @
        drop (Suc i - (min (length xs) i + min (Suc 0) (i - length xs)))
         (snd g # drop i xs @ drop (i - length xs) [x]) =
        xs @ [x]"
      using a0 a1
      by (simp add: Suc_diff_le drop_Cons' min_def not_less_eq_eq)       
  qed
qed

lemma Par2Seq1:"i=length ls \<Longrightarrow> toSeqState i (toParState i (g,ls)) = (g,ls)"
  unfolding toSeqState_def toParState_def Let_def split_beta
  by auto

lemma Par2Seq:"i\<le>length ls \<Longrightarrow> toSeqState i (toParState i (g,ls)) = (g,ls)"
  using Par2Seq0 Par2Seq1
  by (metis le_neq_implies_less)

lemma len_toParState_list:"(g',ls') = toParState i ((g,l),ls) \<Longrightarrow> length ls' = length ls +1"
  unfolding toParState_def by auto

lemma len_toSeqState_list:"i<length ls \<Longrightarrow> ((g',l),ls') = toSeqState i (g,ls) \<Longrightarrow> length ls = length ls' +1"
  unfolding toSeqState_def
  by auto

lemma Seq2Par:"i<length ls \<Longrightarrow> toParState i (toSeqState i (g,ls)) = (g,ls)"
proof (induct  rule: rev_induct)
  case Nil
  then show ?case unfolding toSeqState_def toParState_def Let_def
    by auto    
next
  case (snoc x xs)
  then show ?case unfolding toSeqState_def toParState_def Let_def 
    apply (auto simp add: split_beta)
    by (metis butlast_snoc drop_append id_take_nth_drop snoc.prems take_butlast)    
qed

(* lemma assumes a0:"i<length sl" and
       a1:"length (snd (toParState (toSeqState i (sg, sl)) i)) =
       length (snd (toParState (toSeqState i (sg', sl')) i))"
     shows "length sl = length sl'"
proof-
  have "toParState (toSeqState i (sg, sl)) i = (sg, sl)"
    using a0
    by (simp add: Seq2Par)
qed *)
 
(* typedef ('g,'l) global_s = "{(i,g::('g\<times>'l)\<times>('l list)).  i \<le> length (snd g)  \<and> (\<exists>g'. g' = toParState i g)}"
  unfolding toParState_def
  by auto *)

typedef ('g,'l) global_s = "{(i,g::('g\<times>'l)\<times>('l list)).  i \<le> length (snd g)  \<and> (\<exists>g'. g' = toParState i g)}"
  unfolding toParState_def
  by auto
print_theorems
term Rep_global_s
term Abs_global_s

typedef ('g,'l) global_s1 = "{(g'::('g\<times>'l list)).  (\<exists>i g. i \<le> length (snd g')  \<and> (g' = toParState i g))}"
  unfolding toParState_def
  by auto
print_theorems
term Rep_global_s
term Abs_global_s

setup_lifting type_definition_global_s 

lift_definition global_s_of_local::"(nat\<times>('g\<times>'l)\<times>('l list)) \<Rightarrow> ('g,'l) global_s"
  is "\<lambda>l. (((fst l) mod (length (snd (snd l)) +1), snd l))"
  by auto


(*
definition global_s_of_local::"(nat\<times>('g\<times>'l)\<times>('l list)) \<Rightarrow> ('g,'l) global_s"
  where "global_s_of_local l \<equiv> Abs_global_s (((fst l) mod length (snd (snd l)), snd l))"
 *)
definition transfer_global_s ::"(nat\<times>('g\<times>'l)\<times>('l list)) \<Rightarrow>('g,'l) global_s \<Rightarrow> bool"
  where "transfer_global_s l g \<equiv> g = global_s_of_local l"

print_theorems


typedef ('g,'l) type_global = "{g::('g,'l)par_state. \<forall>i<length (snd g). (\<exists>g'. g = toParState i g')}"
  unfolding toParState_def Let_def split_beta 
  by fastforce

print_theorems 

thm Abs_type_global_inject Rep_type_global Abs_type_global_inverse Rep_type_global_inverse

term Rep_type_global 
term Abs_type_global

primrec toPar_xstate::"nat \<Rightarrow> (('g\<times>'l)\<times>('l list),'f) xstate \<Rightarrow> ((('g,'l)par_state,'f) xstate)"
  where "toPar_xstate i (Normal s) = Normal (toParState i s)"
  |"toPar_xstate i (Abrupt s)  = Abrupt (toParState i s)"
  |"toPar_xstate i (Fault f)  = Fault f"
  |"toPar_xstate i Stuck  = Stuck"

primrec toSeq_xstate::"nat \<Rightarrow> ((('g,'l)par_state,'f) xstate) \<Rightarrow>  (('g\<times>'l)\<times>('l list),'f)  xstate"
  where "toSeq_xstate i (Normal s) = Normal (toSeqState i s)"
  |"toSeq_xstate i (Abrupt s) = Abrupt (toSeqState i s)"
  |"toSeq_xstate i (Fault f)  = Fault f"
  |"toSeq_xstate i Stuck = Stuck"

lemma Par_xstate_Seq_Abrupt:"i<length (snd s)  \<Longrightarrow> toPar_xstate i (toSeq_xstate i (Abrupt s)) = Abrupt s"
  apply (auto simp add: split_beta)
  by (metis Seq2Par prod.collapse)

lemma Par_xstate_Seq_Normal:"i<length (snd s)  \<Longrightarrow> toPar_xstate i (toSeq_xstate i (Normal s)) = Normal s"
  apply (auto simp add: split_beta)
  by (metis Seq2Par prod.collapse)

lemma Par_xstate_Seq_Fault:"toPar_xstate i (toSeq_xstate i (Fault f)) = Fault f"
  by auto

lemma Par_xstate_Seq_Stuck:"toPar_xstate i (toSeq_xstate i (Stuck)) = Stuck"
  by auto

lemma Par_Seq_xstate:"\<forall>nas. (s= Normal nas \<or> s = Abrupt nas)  \<longrightarrow> i< length (snd nas) \<Longrightarrow>
      toPar_xstate i (toSeq_xstate i s) = s"
  apply (cases s)
  using Par_xstate_Seq_Abrupt by auto
  

lemma Seq_xstate_Par_Abrupt:"i\<le>length (snd s)  \<Longrightarrow>  toSeq_xstate i (toPar_xstate i (Abrupt s))  = Abrupt s"
  apply (auto simp add: split_beta)
  by (metis Par2Seq prod.collapse)

lemma Seq_xstate_Par_Normal:"i\<le>length (snd s)  \<Longrightarrow>  toSeq_xstate i (toPar_xstate i (Normal s) )  = Normal s"
  apply (auto simp add: split_beta)
  by (metis Par2Seq prod.collapse)

lemma Seq_xstate_Par_Fault:"toSeq_xstate i (toPar_xstate i (Fault f))  = Fault f"
  by auto

lemma Seq_xstate_Par_Stuck:"toSeq_xstate i (toPar_xstate i Stuck)  = Stuck"
  by auto

lemma Seq_Par_xstate:"\<forall>nas. (s= Normal nas \<or> s = Abrupt nas)  \<longrightarrow> i\<le> length (snd nas) \<Longrightarrow>
      toSeq_xstate i (toPar_xstate i s) = s"
  using Par2Seq 
  by (cases s, auto)

definition toSeqCptn:: "nat \<Rightarrow> (('g,'l,'p,'f,'e) gconf list) \<Rightarrow> ('g, 'l,  'p,'f,'e) config_gs list"
  where "toSeqCptn p cpt \<equiv>                                                                
     map (\<lambda>cfg. (fst cfg, toSeq_xstate p (snd cfg))) cpt
"

lemma toSeqCptn_simp:"toSeqCptn i (x#xs) = (fst x, toSeq_xstate i (snd x)) # (toSeqCptn i xs)"
  by (simp add: toSeqCptn_def)

lemma toSeqCptn_j:"j<length cpt \<Longrightarrow> (toSeqCptn p cpt)!j = (fst (cpt!j), toSeq_xstate p (snd (cpt!j)))"
  unfolding toSeqCptn_def by auto


definition toParCptn::"nat \<Rightarrow> ('g, 'l,  'p,'f,'e) config_gs list \<Rightarrow> (('g,'l,'p,'f,'e) gconf list)"
  where "toParCptn p cpt \<equiv>
   map (\<lambda>cfg. (fst cfg, toPar_xstate p (snd cfg))) cpt
"

lemma toParCptn_simp:"toParCptn i (x#xs) = (fst x, toPar_xstate i (snd x)) # (toParCptn i xs)"
  by (simp add: toParCptn_def)

lemma toParCptn_j:"j<length cpt \<Longrightarrow> (toParCptn p cpt)!j = (fst (cpt!j), toPar_xstate p (snd (cpt!j)))"
  unfolding toParCptn_def by auto

definition Par_pred::"nat \<Rightarrow> (('g,'l) c_state)  set  \<Rightarrow> (('g,'l) par_state set)"
  where "Par_pred i p \<equiv> (toParState i) ` p"

definition Par_rel::"nat \<Rightarrow> ((('g,'l) c_state ,'f) tran) set  \<Rightarrow> ((('g,'l) par_state,'f) tran) set"
  where "Par_rel i r \<equiv> (\<lambda>(x,y). ((toPar_xstate i x), (toPar_xstate i y))) ` r"

definition Seq_pred::"nat \<Rightarrow> (('g,'l) par_state set) \<Rightarrow> (('g,'l) c_state)  set"
  where "Seq_pred i p \<equiv> (toSeqState i) ` p"

definition Seq_rel::"nat \<Rightarrow> ((('g,'l) par_state,'f) tran) set \<Rightarrow> ((('g,'l) c_state ,'f) tran) set  "
  where "Seq_rel i r \<equiv> (\<lambda>(x,y). ((toSeq_xstate i x), (toSeq_xstate i y))) ` r"

lemma Seq_Par_pred_ID:"\<forall>s\<in>p. i\<le>length (snd s) \<Longrightarrow> Seq_pred i (Par_pred i p) = p "
  unfolding Seq_pred_def Par_pred_def apply auto
  apply (simp add: Ball_def_raw Par2Seq0)
  by (metis Par2Seq0 rev_image_eqI snd_conv)

lemma Par_Seq_pred_ID:"\<forall>s\<in>p. i<length (snd s) \<Longrightarrow> Par_pred i (Seq_pred i p) = p "
  unfolding Seq_pred_def Par_pred_def apply auto
  apply (metis Seq2Par snd_conv)
  by (metis Seq2Par image_eqI snd_conv)

lemma Seq_Par_rel_ID:"\<forall>(x,y)\<in>(r::((('a,'b) c_state ,'c) tran) set). 
                      (\<forall>ns. x = Abrupt ns \<or> x = Normal ns \<longrightarrow> i\<le>length (snd ns)) \<and>
                      (\<forall>ns. y = Abrupt ns \<or> y = Normal ns \<longrightarrow> i\<le>length (snd ns)) \<Longrightarrow> 
                  Seq_rel i (Par_rel i r) =r"
  unfolding Seq_rel_def Par_rel_def split_beta image_def apply auto
   apply (simp add: Seq_Par_xstate)  
  by (metis Seq_Par_xstate eq_snd_iff prod.exhaust_sel swap_simp)


lemma Par_Seq_rel_ID:"\<forall>(x,y)\<in>(r::((('a,'b) par_state ,'c) tran) set). 
                      (\<forall>ns. x = Abrupt ns \<or> x = Normal ns \<longrightarrow> i<length (snd ns)) \<and>
                      (\<forall>ns. y = Abrupt ns \<or> y = Normal ns \<longrightarrow> i<length (snd ns)) \<Longrightarrow> 
                  Par_rel i (Seq_rel i r) =r"
  unfolding Seq_rel_def Par_rel_def split_beta image_def apply auto
   apply (simp add: Par_Seq_xstate)  
  by (metis Par_Seq_xstate eq_snd_iff prod.exhaust_sel swap_simp)



lemma eq_toParSeqCptn:
   "\<forall>j<length ls. (\<forall>nas. (snd (ls!j))= Normal nas \<or> (snd (ls!j)) = Abrupt nas  \<longrightarrow> i< length (snd nas)) \<Longrightarrow>
        toParCptn i (toSeqCptn i ls) = ls"
  unfolding toParCptn_def toSeqCptn_def
  apply (rule nth_equalityI, auto)
  by (simp add: Par_Seq_xstate)

lemma eq_toSeqParCptn:
   "\<forall>j<length ls. (\<forall>nas. (snd (ls!j))= Normal nas \<or> (snd (ls!j)) = Abrupt nas  \<longrightarrow> i\<le> length (snd nas)) \<Longrightarrow>
        toSeqCptn i (toParCptn i ls) = ls"
  unfolding toParCptn_def toSeqCptn_def
  apply (rule nth_equalityI, auto)
  by (simp add: Seq_Par_xstate)



inductive
 "step_cei"::"[('g\<times>'l,'p,'f,'e) body,nat,('g, 'l, 'p,'f,'e) gconf,('g, 'l, 'p,'f,'e) gconf] \<Rightarrow> bool"
                                ("_\<turnstile>\<^sub>c\<^sub>_ (_ \<rightarrow>\<^sub>c\<^sub>e/ _)" [81,81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
  where
c_stepi: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c (c,sg) \<rightarrow>\<^sub>c\<^sub>e (c',sg')\<rbrakk> \<Longrightarrow>
          \<Gamma>\<turnstile>\<^sub>c\<^sub>i (c,toPar_xstate i sg ) \<rightarrow>\<^sub>c\<^sub>e (c',toPar_xstate i sg')"

inductive_cases step_cei:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>i cfg \<rightarrow>\<^sub>c\<^sub>e cfg'"

inductive_set cptni :: "(nat\<times>('g,'l,'p,'f,'e) gconfs) set"
where
  CptnOnei: " (i,\<Gamma>, [(P,s)]) \<in> cptni"
| Cptni: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t); (i,\<Gamma>,(Q, t)#xs) \<in> cptni \<rbrakk> \<Longrightarrow>
             (i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni"

inductive_cases cptni_cases:
"(i,\<Gamma>, [(P,s)]) \<in> cptni"
"(i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni"


lemma step_cei_ce1: assumes a0:"\<nexists>sn. s = Normal sn \<or> s = Abrupt sn" and 
              a1:"\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
  shows "\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)"
proof-
  obtain ss st where ce:"\<Gamma>\<turnstile>\<^sub>c(P,ss) \<rightarrow>\<^sub>c\<^sub>e (Q,st)" and 
                  s1:"s=toPar_xstate i ss" and
                  s2:"t=toPar_xstate i st"
    by (auto intro:step_cei[OF a1])
  moreover have eq_ss_st:"ss = st" and eq_s_t:"s=t"
    using a0 ce s1 step_ce_notNormal toPar_xstate.simps(1) calculation
    by blast+
  show ?thesis     
  proof (cases s)
    case (Normal x1)
    then show ?thesis using a0 by auto
  next
    case (Abrupt x2)    
    then show ?thesis using a0 by auto       
  next
    case (Fault x3)
    moreover have "ss = Fault x3" using calculation s1 by (cases ss, auto)
    ultimately show ?thesis 
      using ce by (auto simp add: eq_s_t eq_ss_st)     
  next
    case Stuck
    moreover have "ss = Stuck" using calculation s1 by (cases ss, auto)
    ultimately show ?thesis 
      using ce by (auto simp add: eq_s_t eq_ss_st)  
  qed
qed


lemma step_cei_ce2: assumes a0:"s = Normal sn" and a0':"i<length (snd sn)" and
              a1:"\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
  shows "\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)"
proof-
  obtain ss st where ce:"\<Gamma>\<turnstile>\<^sub>c(P,ss) \<rightarrow>\<^sub>c\<^sub>e (Q,st)" and 
                  s1:"s=toPar_xstate i ss" and
                  s2:"t=toPar_xstate i st"
    by (auto intro:step_cei[OF a1])  
  moreover obtain ssn where ssn:"ss=Normal ssn" using a0 s1 by (cases ss, auto)
  then have "length (snd sn) = length (snd ssn) + 1" 
    using a0' s1 a0 len_toParState_list[of "fst sn" "snd sn" _ "fst (fst ssn)" "snd (fst ssn)" "snd ssn"]
    by auto
  then have len_i:"i\<le> length (snd ssn)" using a0' by auto
  show ?thesis     
  proof(cases st)
    case (Normal x2)
    have "length (snd x2) = length (snd ssn)" 
      using ssn  ce step_dest[OF ce[simplified ssn]] 
      by (auto simp add: Normal step_dest1 elim:step_e.cases)       
    then show ?thesis 
      using  ce a0 s1 s2 a0' Normal Seq_xstate_Par_Normal[OF len_i ]
      apply (auto simp add: Normal a0 s1 s2 a0' ssn intro: Seq_xstate_Par_Normal)
      by (metis Par2Seq len_i prod.exhaust_sel)  
  next    
    case (Abrupt x2)  
    
    then show ?thesis
      by (metis (no_types, hide_lams) Seq_xstate_Par_Abrupt Seq_xstate_Par_Normal 
            ce env_c_c' len_i prod.exhaust_sel s1 s2 ssn 
            step_dest stepe_Normal_elim_cases)
  next
    case (Fault x3)
    then show ?thesis
      using Seq_xstate_Par_Normal ce len_i s1 s2 ssn by fastforce
  next
    case Stuck
    then show ?thesis
      using Seq_xstate_Par_Normal ce len_i s1 s2 ssn by fastforce 
  qed   
qed

lemma step_cei_ce3: assumes a0:"s = Abrupt sn" and a0':"i<length (snd sn)" and
              a1:"\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
  shows "\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)"
proof-
  obtain ss st where ce:"\<Gamma>\<turnstile>\<^sub>c(P,ss) \<rightarrow>\<^sub>c\<^sub>e (Q,st)" and 
                  s1:"s=toPar_xstate i ss" and
                  s2:"t=toPar_xstate i st"
    by (auto intro:step_cei[OF a1])  
  moreover obtain ssn where ssn:"ss=Abrupt ssn" using a0 s1 by (cases ss, auto)
  then have "length (snd sn) = length (snd ssn) + 1" 
    using a0' s1 a0 len_toParState_list[of "fst sn" "snd sn" _ "fst (fst ssn)" "snd (fst ssn)" "snd ssn"]
    by auto
  then have len_i:"i\<le> length (snd ssn)" using a0' by auto
  show ?thesis     
  proof(cases st)
    case (Normal x2)
    have "length (snd x2) = length (snd ssn)"
      using Normal ce ssn step_ce_notNormal by blast       
    then show ?thesis 
      using  ce a0 s1 s2 a0' Normal Seq_xstate_Par_Normal[OF len_i ]
      apply (auto simp add: Normal a0 s1 s2 a0' ssn intro: Seq_xstate_Par_Normal)
      by (metis Par2Seq len_i prod.exhaust_sel)  
  next    
    case (Abrupt x2)      
    then show ?thesis
      by (metis Seq_xstate_Par_Abrupt ce len_i s1 s2 ssn step_ce_notNormal xstate.distinct(1))      
  next
    case (Fault x3)
    then show ?thesis
      using Seq_xstate_Par_Normal ce len_i s1 s2 ssn by fastforce
  next
    case Stuck
    then show ?thesis
      using Seq_xstate_Par_Normal ce len_i s1 s2 ssn by fastforce 
  qed
qed


lemma step_cei_not_normal_eq: 
  assumes a0:"\<forall>sn. s \<noteq> (Normal sn)" and
          a1:"\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"            
        shows "s=t"
proof-
  obtain ssj ssj1 where "s = toPar_xstate i ssj" and "t = toPar_xstate i ssj1" and 
                                 "\<Gamma>\<turnstile>\<^sub>c (P,ssj) \<rightarrow>\<^sub>c\<^sub>e (Q,ssj1)"
    using a0 a1 step_cei.simps by fastforce
  moreover have "\<forall>sn. ssj \<noteq> Normal sn" using  a0 a1 calculation
    by (metis toPar_xstate.simps 
         xstate.distinct(10) xstate.distinct(12) xstate.distinct(6))   
  moreover have "ssj1=ssj" using step_ce_notNormal a0 a1 calculation by blast
  ultimately show ?thesis using  step_ce_notNormal step_cei.simps
    by fastforce    
qed

lemma step_cei_normal_normal_same_len:
  assumes  a0:"\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,Normal ns) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"  and a1:"t= Normal nt \<or> t=Abrupt nt"
  shows "length (snd ns) = length (snd nt)"
proof-
  obtain ssj ssj1 where "Normal ns = toPar_xstate i ssj" and "t = toPar_xstate i ssj1" and
                                 "\<Gamma>\<turnstile>\<^sub>c (P,ssj) \<rightarrow>\<^sub>c\<^sub>e (Q,ssj1)"
    using  step_cei.simps a0 by fastforce
  moreover obtain ssjn ssj1n where "ssj = Normal ssjn" and "ssj1 = Normal ssj1n \<or> ssj1 = Abrupt ssj1n" 
    using calculation a1 apply auto
     apply (metis old.prod.exhaust toPar_xstate.simps(2) toPar_xstate.simps(3) toPar_xstate.simps(4) 
                 xstate.distinct(3) xstate.distinct(6) xstate.exhaust xstate.simps(5))
    by (metis step_ce_notNormal surj_pair toPar_xstate.simps(3) toPar_xstate.simps(4) toSeq_xstate.simps(2) 
              toSeq_xstate.simps(4) xstate.distinct(7) xstate.exhaust xstate.simps(5))  
  moreover  have "length (snd ssjn) = length (snd ssj1n)"
    using calculation ce_eq_length by blast
  moreover have "ns = (toParState i ssjn)" and "nt =  (toParState i ssj1n)"
    using \<open>ssj = Normal ssjn\<close>   calculation a1 by auto     
  ultimately show ?thesis  
    by (metis \<open>length (snd ssjn) = length (snd ssj1n)\<close> eq_snd_iff len_toParState_list)
qed

lemma step_ce_to_step_cei1:
  assumes a0:"\<nexists>sn. s = Normal sn \<or> s = Abrupt sn" and 
          a1:"\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P, s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
  using c_stepi[OF a1] using a0  Seq_xstate_Par_Fault Seq_xstate_Par_Stuck 
  apply (cases s; cases t, auto)
  using a1 step_ce_notNormal by force+


lemma step_ce_to_step_cei2:
  assumes a0:"s = Normal sn" and a0':"i<length (snd sn)"  and a0'':"t= Normal tn \<or> t=Abrupt tn" and
          a2:"length (snd sn) = length (snd tn)" and
          a1:"\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P, s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
 using c_stepi[OF a1, of i] using a0 a0' a1
  by (metis Par_xstate_Seq_Abrupt Par_xstate_Seq_Normal a0'' a2)

lemma step_ce_to_step_cei3:
  assumes a0:"s = Normal sn" and a0':"i<length (snd sn)"  and a0'':"\<forall>tn. t\<noteq>Normal tn \<and> t\<noteq>Abrupt tn" and          
          a1:"\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P, s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
 using c_stepi[OF a1, of i] using a0 a0' a1
  by (metis Par_xstate_Seq_Normal a0'' toPar_xstate.simps(3) toPar_xstate.simps(4) 
       toSeq_xstate.simps(3) toSeq_xstate.simps(4) xstate.exhaust)

lemma step_ce_to_step_cei4:
  assumes a0:"s = Abrupt sn" and a0':"i<length (snd sn)" and  
          a2:"s=t" and        
          a1:"\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P, s) \<rightarrow>\<^sub>c\<^sub>e (Q,t)"
using c_stepi[OF a1, of i] using a0 a0' a1 a2
  by (metis Par_xstate_Seq_Abrupt)

lemma same_local_sublist_toSeq_State1: 
  assumes a0:"\<forall>nas nasa. (s= Normal nas \<or> s = Abrupt nas) \<and> (sa= Normal nasa \<or> sa = Abrupt nasa) \<longrightarrow>
           (\<forall>j\<noteq>i. (snd nas)!j = (snd nasa)!j) \<and> length (snd nas) = length (snd nasa)" and    
a1:"sa = Normal na \<or>  sa = Abrupt na" and
a2:"s = Normal ns \<or>  s = Abrupt ns" and
a3:"\<forall>nas. (s= Normal nas \<or> s = Abrupt nas)  \<longrightarrow> i<length (snd nas)" 
  shows  " (toSeq_xstate i s = Normal nsx \<or> toSeq_xstate i s = Abrupt nsx) \<and>
           (toSeq_xstate i sa = Normal nsx' \<or> toSeq_xstate i sa = Abrupt nsx') \<longrightarrow>
           snd nsx = snd nsx'"
proof-  
  { assume "(toSeq_xstate i s = Normal nsx \<or> toSeq_xstate i s = Abrupt nsx) \<and>
           (toSeq_xstate i sa = Normal nsx' \<or> toSeq_xstate i sa = Abrupt nsx')"   
    have  a0:"(\<forall>j. j\<noteq>i\<longrightarrow> snd na!j =  snd ns!j)" and a3:"length (snd na) = length (snd ns)" and a5:"i<length (snd ns)"
      using a0 a1 a2 a3 by fastforce+  
    have ?thesis  using a1 a2                      
      apply (auto) unfolding toSeqState_def Let_def split_beta 
      by (auto intro:eq_list_i[OF  a3 a0 a5])
  } thus ?thesis by auto
qed

lemma same_local_sublist_toSeq_State: 
  assumes a0:"\<forall>nas nasa. (s= Normal nas \<or> s = Abrupt nas) \<and> (sa= Normal nasa \<or> sa = Abrupt nasa) \<longrightarrow>
           (\<forall>j\<noteq>i. (snd nas)!j = (snd nasa)!j) \<and> length (snd nas) = length (snd nasa)" and    
a3:"\<forall>nas. (s= Normal nas \<or> s = Abrupt nas)  \<longrightarrow> i<length (snd nas)" 
  shows  " (toSeq_xstate i s = Normal nsx \<or> toSeq_xstate i s = Abrupt nsx) \<and>
           (toSeq_xstate i sa = Normal nsx' \<or> toSeq_xstate i sa = Abrupt nsx') \<longrightarrow>
           snd nsx = snd nsx'"
proof-  
  { assume "(toSeq_xstate i s = Normal nsx \<or> toSeq_xstate i s = Abrupt nsx) \<and>
           (toSeq_xstate i sa = Normal nsx' \<or> toSeq_xstate i sa = Abrupt nsx')"   
    then obtain na ns where nas:"(s= Normal ns \<or> s = Abrupt ns) \<and> (sa= Normal na \<or> sa = Abrupt na)" 
      by (cases s; cases sa; auto)
    then have  a0:"(\<forall>j. j\<noteq>i\<longrightarrow> snd na!j =  snd ns!j)" and a3:"length (snd na) = length (snd ns)" and a5:"i<length (snd ns)"
      using a0  a3 by fastforce+  
    have ?thesis  using nas                      
      apply (auto) unfolding toSeqState_def Let_def split_beta 
      by (auto intro:eq_list_i[OF  a3 a0 a5])
  } thus ?thesis by auto
qed

lemma step_cei_i1:
  assumes a0:"\<forall>nas nasa. (s= Normal nas \<or> s = Abrupt nas) \<and> (t= Normal nasa \<or> t = Abrupt nasa) \<longrightarrow>
           (\<forall>j\<noteq>i. (snd nas)!j = (snd nasa)!j) \<and> length (snd nas) = length (snd nasa)" and    
          a1:"\<forall>nas. (s= Normal nas \<or> s = Abrupt nas)  \<longrightarrow> i<length (snd nas)" and
          a2:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq (toSeq_xstate i s)) \<rightarrow> (c', toSeq (toSeq_xstate i t))"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(c,s) \<rightarrow>\<^sub>c\<^sub>e (c',t)"
proof-
  have a1': "\<forall>nas. (t= Normal nas \<or> t = Abrupt nas)  \<longrightarrow> i<length (snd nas)"
  proof-
    {fix nas
      assume "(t= Normal nas \<or> t = Abrupt nas)"
      moreover obtain ns where "s = Normal ns \<or> s = Abrupt ns"
        using a2  apply (cases s, auto )
        using SmallStepCon.step_Fault_prop step_Stuck_prop calculation by fastforce+      
      ultimately have ?thesis using a0 a1 by auto
    } then show ?thesis by auto
  qed   
  have "\<forall>ns ns'.
       (toSeq_xstate i s = Normal ns \<or> toSeq_xstate i s = Abrupt ns) \<and>
       (toSeq_xstate i t = Normal ns' \<or> toSeq_xstate i t = Abrupt ns') \<longrightarrow>
       snd ns = snd ns'" using same_local_sublist_toSeq_State[OF a0 a1] by fastforce   
  then have  c:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (c', toSeq_xstate i t)"
    using c_step[OF a2]  by auto
  show ?thesis using c_stepi[OF c] a1 a1' apply (cases s; cases t, auto simp add: )
    by (metis (mono_tags, hide_lams) Seq2Par a0 snd_conv)+
qed


lemma step_cei_i2:
  assumes a0:"\<forall>nas nasa. (s= Normal nas \<or> s = Abrupt nas) \<and> (t= Normal nasa \<or> t = Abrupt nasa) \<longrightarrow>
              length (snd nas) = length (snd nasa)" and    
          a1:"\<forall>nas. (s= Normal nas \<or> s = Abrupt nas)  \<longrightarrow> i<length (snd nas)" and
          a2:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq_xstate i s) \<rightarrow>\<^sub>e (c, toSeq_xstate i t)"
        shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(c,s) \<rightarrow>\<^sub>c\<^sub>e (c,t)"
proof-
  have "\<forall>nas. (t= Normal nas \<or> t = Abrupt nas)  \<longrightarrow> i<length (snd nas)"    
    apply (cases s; cases t, auto) 
    using a0 a1 stepe_elim_cases[of \<Gamma> c "toSeq_xstate i s" "toSeq_xstate i t",OF a2] by auto    
  moreover have  a3:"\<Gamma>\<turnstile>\<^sub>c (c, toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (c, toSeq_xstate i t)" using e_step[OF a2] by auto
  ultimately show ?thesis using c_stepi[OF a3] apply (cases s; cases t, auto) using a1
    by (metis Seq2Par snd_conv)+
qed


lemma sublist:"j<(length c)-1 \<Longrightarrow> \<exists>c' c''. c = c'@([c!j,c!(j+1)]@c'')"
proof (induct j arbitrary: c)
  case 0
  then show ?case
    by (metis One_nat_def Suc_less_eq add.left_neutral append.assoc append_Cons append_Nil 
               id_take_nth_drop less_Suc_eq take_Suc_conv_app_nth zero_less_diff)
next
  case (Suc j)
  then have "j<length c - 1 -1"
    by simp
  then show ?case using Suc
    by (metis Suc_eq_plus1 Suc_lessD append.assoc append_Cons append_Nil 
             id_take_nth_drop less_diff_conv take_Suc_conv_app_nth)
qed

lemma cptni_dest:"(i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,(Q,t)#xs)\<in> cptni"
by (auto dest: cptni_cases)

lemma cptni_dest_pair:"(i,\<Gamma>,x#x1#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,x1#xs)\<in> cptni"
proof -
  assume "(i,\<Gamma>,x#x1#xs) \<in> cptni"
  thus ?thesis using cptni_dest prod.collapse by metis
qed

lemma cptni_dest1:"(i,\<Gamma>,(P,s)#(Q,t)#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,(P,s)#[(Q,t)])\<in> cptni"
proof -
  assume a1: "(i,\<Gamma>, (P, s) # (Q, t) # xs) \<in> cptni"
  have "(i,\<Gamma>, [(Q, t)]) \<in> cptni"
    by (meson cptni.CptnOnei)
  thus ?thesis
    using a1 cptni.Cptni cptni_cases(2) by blast
qed

lemma cptni_dest1_pair:"(i,\<Gamma>,x#x1#xs) \<in> cptni \<Longrightarrow> (i,\<Gamma>,x#[x1])\<in> cptni"
proof -
  assume "(i,\<Gamma>,x#x1#xs) \<in> cptni"
  thus ?thesis using cptni_dest1 prod.collapse by metis
qed

lemma cptni_append_is_cptni [rule_format]: 
 "\<forall>b a. (i,\<Gamma>,b#c1)\<in>cptni \<longrightarrow>  (i,\<Gamma>,a#c2)\<in>cptni \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> (i,\<Gamma>,b#c1@c2)\<in>cptni"
apply(induct c1)
 apply simp
apply clarify
apply(erule cptni.cases,simp_all)
  by (simp add: cptni.Cptni)
(* apply (simp add: cptn.CptnEnv)
by (simp add: cptn.CptnComp) *)

lemma cptni_dest_2:
  "(i,\<Gamma>,a#xs@ys) \<in> cptni  \<Longrightarrow> (i,\<Gamma>,a#xs)\<in> cptni"
proof (induct "xs" arbitrary: a)
  case Nil thus ?case using cptni.simps by fastforce 
next
  case (Cons x xs') 
  then have "(i,\<Gamma>,a#[x])\<in>cptni" by (simp add: cptni_dest1_pair)
  also have "(i,\<Gamma>, x # xs') \<in> cptni"
    using Cons.hyps Cons.prems cptni_dest_pair by fastforce    
  ultimately show ?case using cptni_append_is_cptni [of i \<Gamma> a "[x]" x xs']
    by force    
qed   

lemma tl_in_cptni: "\<lbrakk> (i,g,a#xs) \<in>cptni; xs\<noteq>[] \<rbrakk> \<Longrightarrow> (i,g,xs)\<in>cptni"
  by (force elim: cptni.cases)

lemma sublist_in_cptni:"(i,\<Gamma>, ys@ xs) \<in> cptni \<Longrightarrow> xs\<noteq> [] \<Longrightarrow> (i,\<Gamma>, xs) \<in> cptni"
proof(induct ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  then have "(i,\<Gamma>, a # (ys @ xs)) \<in> cptni" by auto
  then show ?case using cptni_cases
    by (metis Cons.hyps Cons.prems(2) Nil_is_append_conv tl_in_cptni)  
qed

lemma cptni_step_cei:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and a1:"j<(length c)-1"
  shows "\<Gamma>\<turnstile>\<^sub>c\<^sub>i (c!j) \<rightarrow>\<^sub>c\<^sub>e (c!(j+1))"
proof-
 obtain c' c'' where "c = c'@([c!j,c!(j+1)]@c'')" using sublist[OF a1] by auto
  then have "(i,\<Gamma>,c!j#(c!(j+1))#c'') \<in>cptni" using a0 sublist_in_cptni
    by (metis append_Cons append_Nil list.distinct(1))
  then obtain pj sj pj1 sj1 
    where cptni:"(i,\<Gamma>,(pj,sj)#(pj1,sj1)#c'') \<in>cptni" and 
          cj:"c!j = (pj,sj)" and cj1:"c!(j+1) =(pj1,sj1)"
    by (metis prod.exhaust_sel)     
  then show ?thesis using cptni_cases(2)[OF cptni] by auto  
qed


lemma step_cei_notNormal:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and a1:"j<(length c)-1" and a2:"\<forall>sn. snd (c!j) \<noteq> Normal sn"              
  shows "snd (c!j) = snd (c!(j+1))"
using step_cei_not_normal_eq cptni_step_cei[OF a0 a1] using a2
     by (metis eq_snd_iff)


lemma all_not_normal:"(i,\<Gamma>,c) \<in> cptni \<Longrightarrow>  j<(length c) \<Longrightarrow> (\<nexists>na. snd (c!j) =Normal na)  \<Longrightarrow> 
       j'< (length c) \<Longrightarrow> j' > j \<Longrightarrow>  \<nexists>na. snd (c!j') =Normal na"
proof (induct "j'-j" arbitrary: j)
  case 0
  then show ?case by auto
next
  case (Suc x)
  {assume "x = 0"
    then have ?case using Suc step_cei_notNormal[OF Suc(3)]      
      by (metis (no_types, lifting) One_nat_def add_diff_inverse_nat 
        dual_order.strict_trans less_diff_conv less_not_refl)
  }
  moreover { assume "x\<noteq>0"   
    moreover have "\<nexists>na. snd (c ! (j+1)) = Normal na"
      by (metis (no_types, lifting) Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4) 
        Suc.prems(5) diff_Suc_1 lessE not_less_eq step_cei_notNormal)
    ultimately have ?case using Suc
      by (metis (no_types, lifting) Suc_diff_Suc Suc_eq_plus1 Suc_lessI add_diff_cancel_left' 
               less_trans_Suc plus_1_eq_Suc)
  }
  ultimately show ?case by auto
qed

lemma cptni_not_normal_all_eq:
     "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow>  j<(length c) \<Longrightarrow> (\<nexists>na. snd (c!j) =Normal na)  \<Longrightarrow> 
       j'< (length c) \<Longrightarrow> j' \<ge> j \<Longrightarrow> snd (c!j) = snd (c!j')"
proof (induct "j'-j" arbitrary: j)
  case 0
  then show ?case by auto
next
  case (Suc x)
  {assume "x = 0"
    then have ?case using Suc step_cei_notNormal[OF Suc(3)]
      by (metis One_nat_def le_add_diff_inverse less_diff_conv) 
  }
  moreover { assume "x\<noteq>0"   
    moreover have "snd (c!j) = snd (c ! (j+1))"
      by (metis (no_types, lifting) Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc.prems(3) 
              Suc.prems(4) Suc.prems(5) 
               Suc_lessI add.right_neutral add_Suc_right add_diff_cancel_left' le_add_diff_inverse2 
                 less_diff_conv not_add_less1 plus_1_eq_Suc step_cei_notNormal) 
    ultimately have ?case using Suc
      by auto
  }
  ultimately show ?case by auto
qed


lemma cptni_normal_normal_same_length:
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and a1:"j<(length c)-1" and a2:"snd (c!j) =Normal na" and
       a3:"snd (c!(j+1)) =Normal nb \<or> snd (c!(j+1)) = Abrupt nb" 
     shows "length (snd na) = length (snd nb)"
  using cptni_step_cei[OF a0 a1] a2 a3 step_cei_normal_normal_same_len
  by (metis prod.exhaust_sel)

lemma cptni_i_normal_len:
    "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow>  length c > 1 \<Longrightarrow> j<length c \<Longrightarrow> j'<length c \<Longrightarrow> j'\<ge>j \<Longrightarrow>
      snd(c!j) = Normal ni  \<Longrightarrow> 
      snd(c!j') = Abrupt nj \<or> snd(c!j') = Normal nj \<Longrightarrow>
      length (snd (nj)) = length (snd (ni))"
proof (induct "j'-j" arbitrary: j ni)
  case 0
  then show ?case by auto
next
  case (Suc x)
  {assume "x = 0"
    then have ?case using Suc step_cei_notNormal[OF Suc(3)] 
   cptni_normal_normal_same_length[OF  Suc(3)]
      by (metis (no_types, lifting) One_nat_def le_add_diff_inverse less_diff_conv less_imp_le_nat)
  }
  moreover { assume "x\<noteq>0"   
    then have "j<(length c)-1" using Suc
      by linarith      
    have x:"x=j' - (j+1)"
        by (metis (no_types) Suc.hyps(2) diff_Suc_1 diff_diff_add)
    moreover have j1_len:"j+1 < length c"        
      using \<open>j < length c - 1\<close> less_diff_conv by blast
    moreover have  j_j':"j+1 \<le> j'"
      using \<open>x \<noteq> 0\<close> calculation(1) by auto
    have ?case 
    proof(cases "snd (c!(j+1))")
      case (Normal x1)      
      then show  ?thesis using Suc  x j1_len j_j'
        by (metis (mono_tags, lifting) \<open>j < length c - 1\<close> cptni_normal_normal_same_length)
    next
      case (Abrupt x2)
      then show ?thesis using cptni_not_normal_all_eq[OF Suc(3) j1_len _ Suc(6) j_j']
        by (metis Suc.prems(1) Suc.prems(6) Suc.prems(7) \<open>j < length c - 1\<close> 
                 cptni_normal_normal_same_length xstate.distinct(1))         
    next
      case (Fault x3)  
      then show ?thesis
        by (metis Suc.prems(1) Suc.prems(4) Suc.prems(6) Suc.prems(7) \<open>j < length c - 1\<close> cptni_normal_normal_same_length 
                  cptni_not_normal_all_eq j1_len j_j' xstate.distinct(3)) 
    next
      case Stuck
      then show ?thesis
        by (metis Suc.prems(1) Suc.prems(4) Suc.prems(6) Suc.prems(7) \<open>j < length c - 1\<close> 
           cptni_normal_normal_same_length
             cptni_not_normal_all_eq j1_len j_j' xstate.distinct(5))     
    qed
  }
  ultimately show ?case by auto
qed

lemma cptni_i_normal_abrupt_len: 
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and 
          a1:"length c > 1" and a2:"j<length c" and a3:"j'<length c" and 
          a4:"j'\<ge>j" and a5:"snd(c!j) = Normal ni \<or> snd(c!j) = Abrupt ni" and
      a6:"snd(c!j') = Abrupt nj \<or> snd(c!j') = Normal nj"
    shows "length (snd (nj)) = length (snd (ni))"
  using a5
proof
  assume a5:"snd (c ! j) = Normal ni "
  then show ?thesis using a0 a1 a2 a3 a4 a6 cptni_i_normal_len by blast
next
  assume a5:"snd (c ! j) = Abrupt ni"
  then show ?thesis using a0 a1 a2 a3 a4 a6
    by (metis cptni_not_normal_all_eq xstate.distinct(1) xstate.inject(2))
qed

lemma cptni_i_normal_abrupt_eq_len: 
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and 
          a1:"length c > 1" and a2:"j<length c" and a3:"j'<length c" and 
          a4:"j'\<ge>j" and 
          a5:"\<forall>ni. snd(c!j) = Normal ni \<or> snd(c!j) = Abrupt ni \<longrightarrow> 
                                  length (snd ni) = x"
  shows "\<forall>ni. snd(c!j') = Normal ni \<or> snd(c!j') = Abrupt ni \<longrightarrow> 
                                  length (snd ni) = x"      
proof-
  {fix ni
    assume a00:" snd(c!j') = Normal ni \<or> snd(c!j') = Abrupt ni"
    {assume "\<nexists>ni. snd(c!j) = Normal ni \<or> snd (c!j) = Abrupt ni"
      then have "length (snd ni) = x"
        by (metis a0 a00 a2 a3 a4 cptni_not_normal_all_eq)
    }
    moreover {assume "\<exists>ni. snd(c!j) = Normal ni \<or> snd (c!j) = Abrupt ni"
      then obtain ni' where "snd(c!j) = Normal ni' \<or> snd (c!j) = Abrupt ni'" by auto
      moreover have "length (snd ni') = x" using calculation
        by (simp add: a5)     
      ultimately have "length (snd ni) = x" using a0 a1 a2 a3 a4
        using a00 cptni_i_normal_abrupt_len by blast      
    }
    ultimately have "length (snd ni) = x" by auto 
  }
  thus ?thesis by auto  
qed

lemma cptni_i_normal_abrupt_eq_len1: 
  assumes a0:"(i,\<Gamma>,c) \<in> cptni" and 
          a1:"length c > 1" and a2:"j<length c" and a3:"j'<length c" and 
          a4:"j'\<ge>j" and 
          a5:"\<forall>ni. snd(c!j) = Normal ni \<or> snd(c!j) = Abrupt ni \<longrightarrow> 
                                  length (snd ni) = x"
  shows "\<forall>ni. snd(c!j') = Normal ni \<or> snd(c!j') = Abrupt ni \<longrightarrow> 
                                  length (snd ni) = x"      
proof-
  {fix ni
    assume a00:" snd(c!j') = Normal ni \<or> snd(c!j') = Abrupt ni"
    {assume "\<nexists>ni. snd(c!j) = Normal ni \<or> snd (c!j) = Abrupt ni"
      then have "length (snd ni) = x"
        by (metis a0 a00 a2 a3 a4 cptni_not_normal_all_eq)
    }
    moreover {assume "\<exists>ni. snd(c!j) = Normal ni \<or> snd (c!j) = Abrupt ni"
      then obtain ni' where "snd(c!j) = Normal ni' \<or> snd (c!j) = Abrupt ni'" by auto
      moreover have "length (snd ni') = x" using calculation
        by (simp add: a5)     
      ultimately have "length (snd ni) = x" using a0 a1 a2 a3 a4
        using a00 cptni_i_normal_abrupt_len by blast      
    }
    ultimately have "length (snd ni) = x" by auto 
  }
  thus ?thesis by auto  
qed

lemma length_locs_less_i':assumes a0:"(i,\<Gamma>,c) \<in> cptni" and
       a1:"length c > 0" and
       a2:"(\<forall>nas. (snd (c!0))= Normal nas \<or> (snd (c!0)) = Abrupt nas  \<longrightarrow> i< length (snd nas))" 
     shows "\<forall>j<length c. (\<forall>nas. (snd (c!j))= Normal nas \<or> (snd (c!j)) = Abrupt nas  \<longrightarrow> 
            i< length (snd nas))"
proof (cases "length c = 1")
  assume "length c = 1"
  then show ?thesis using a0 a1 a2 by auto
next
  assume "length c\<noteq>1"
  then have l0:"length c>1" using a1 by linarith
  { fix j nas
    assume a00:"j<length c"
    assume a01:" (snd (c!j))= Normal nas \<or> (snd (c!j)) = Abrupt nas "
    then have "i< length (snd nas)" 
    proof(cases "snd (c!0)")
      case (Normal x1)
      then show ?thesis using  cptni_i_normal_abrupt_len[OF a0 l0 _ a00] a0 a1 a2
        by (metis a01 not_less0 not_less_iff_gr_or_eq order.order_iff_strict)
    next
      case (Abrupt x2)
      then show ?thesis using  cptni_i_normal_abrupt_len[OF a0 l0 _ a00] a0 a1 a2
        by (metis a01 not_less not_less0)
    next
      case (Fault x3)
      then show ?thesis
        by (metis a0 a00 a01 a1 a2 cptni_not_normal_all_eq not_less not_less0 xstate.distinct(3)) 
    next
      case Stuck
      then show ?thesis
        by (metis a0 a00 a01 a1 a2 cptni_not_normal_all_eq not_less not_less0 xstate.distinct(5))  
    qed
  } thus ?thesis by auto
qed

lemma cptni_length_locs_less_i:
     assumes a0:"(i,\<Gamma>,c) \<in> cptni" and       
       a1:"(\<forall>nas. (snd (c!0))= Normal nas \<or> (snd (c!0)) = Abrupt nas  \<longrightarrow> i< length (snd nas))" 
     shows "\<forall>j<length c. (\<forall>nas. (snd (c!j))= Normal nas \<or> (snd (c!j)) = Abrupt nas  \<longrightarrow> 
            i< length (snd nas))"
proof(cases "length c")
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then show ?thesis using length_locs_less_i'[OF a0 _ a1] by auto
qed


lemma cptni_cptn_not_abrupt_normal:
 "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow> 
  \<forall>sn. snd(c!0) \<noteq> Normal sn \<and> snd(c!0) \<noteq>Abrupt sn  \<Longrightarrow>
 (\<Gamma>, toSeqCptn i c) \<in> cptn"
proof (induct rule:cptni.induct)
  case (CptnOnei i \<Gamma> P s)
  then show ?case unfolding toSeqCptn_def using cptn.intros by auto
next
  case (Cptni \<Gamma> i P s Q t xs)
  then have "\<forall>sn. s\<noteq>Normal sn \<and> s \<noteq>Abrupt sn"
    by simp    
  then  have "\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)" 
    using step_cei_ce1[OF _ Cptni(1)] by blast
  moreover have " (\<Gamma>, toSeqCptn i ((Q, t) # xs)) \<in> cptn" using Cptni
    by (metis nth_Cons_0 snd_conv step_cei_not_normal_eq)
  ultimately show ?case using toSeqCptn_simp
    by (simp add: toSeqCptn_simp cptn.Cptn)
qed



lemma cptni_cptn_Abrupt:
 "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow> 
  snd(c!0) = Abrupt sn   \<Longrightarrow> i< length (snd sn) \<Longrightarrow>
 (\<Gamma>, toSeqCptn i c) \<in> cptn"
proof (induct arbitrary: sn rule:cptni.induct)
  case (CptnOnei i \<Gamma> P s)
  then show ?case unfolding toSeqCptn_def using cptn.intros by auto
next
  case (Cptni \<Gamma> i P s Q t xs)
  then have s:"s=Abrupt sn " and "s=t"
    apply simp
    using Cptni.hyps(1) Cptni.prems(1) step_cei_not_normal_eq by fastforce    
  then  have "\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)" 
    using   step_cei_ce3[OF s _ Cptni(1)]
    using Cptni.prems(2) by linarith
  moreover have " (\<Gamma>, toSeqCptn i ((Q, t) # xs)) \<in> cptn" using Cptni
    by (simp add: \<open>s = t\<close>)
  ultimately show ?case using toSeqCptn_simp
    by (simp add: toSeqCptn_simp cptn.Cptn)
qed


lemma cptni_cptn_normal:
 "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow> 
  snd(c!0) = Normal sn   \<Longrightarrow> i< length (snd sn) \<Longrightarrow>
 (\<Gamma>, toSeqCptn i c) \<in> cptn"
proof (induct arbitrary: sn rule:cptni.induct)
  case (CptnOnei i \<Gamma> P s)
  then show ?case unfolding toSeqCptn_def using cptn.intros by auto
next
  case (Cptni \<Gamma> i P s Q t xs)
  then have s:"s=Normal sn "
    by simp    
  then  have "\<Gamma>\<turnstile>\<^sub>c(P,toSeq_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toSeq_xstate i t)" 
    using   step_cei_ce2[OF s _ Cptni(1)]
    using Cptni.prems(2) by linarith
  moreover have " (\<Gamma>, toSeqCptn i ((Q, t) # xs)) \<in> cptn"
  proof(cases t)
    case (Normal x1)
    then show ?thesis
      using Cptni.hyps(1) Cptni.hyps(3) Cptni.prems(2) s 
            step_cei_normal_normal_same_len by fastforce
  next
    case (Abrupt x2)
    then show ?thesis
      by (metis Cptni.hyps(1) Cptni.hyps(2) Cptni.prems(2) cptni_cptn_Abrupt 
          nth_Cons_0 s snd_conv step_cei_normal_normal_same_len) 
  next
    case (Fault x3)
    then show ?thesis
      using Cptni.hyps(2) cptni_cptn_not_abrupt_normal by force  
  next
    case Stuck
    then show ?thesis  using Cptni.hyps(2) cptni_cptn_not_abrupt_normal by force 
  qed
  ultimately show ?case using toSeqCptn_simp
    by (simp add: toSeqCptn_simp cptn.Cptn)
qed

lemma cptni_cptn:
 "(i,\<Gamma>,c) \<in> cptni \<Longrightarrow> 
  \<forall>sn. snd(c!0) = Normal sn \<or> snd(c!0) = Abrupt sn \<longrightarrow>  i< length (snd sn) \<Longrightarrow>
 (\<Gamma>, toSeqCptn i c) \<in> cptn" 
  apply (cases "snd (c!0)") using cptni_cptn_normal cptni_cptn_Abrupt cptni_cptn_not_abrupt_normal 
  by fastforce+


lemma cptn_cptni_not_abrupt_normal:
 "(\<Gamma>,c) \<in> cptn \<Longrightarrow> 
  \<forall>sn. snd(c!0) \<noteq> Normal sn \<and> snd(c!0) \<noteq>Abrupt sn  \<Longrightarrow>
 (i, \<Gamma>, toParCptn i c) \<in> cptni"
proof (induct rule:cptn.induct)
  case (CptnOne \<Gamma> P s)
  then show ?case unfolding toParCptn_def using cptni.intros by auto
next
  case (Cptn \<Gamma> P s Q t xs)
  then have "\<forall>sn. s\<noteq>Normal sn \<and> s \<noteq>Abrupt sn"
    by simp    
  then  have "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,toPar_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toPar_xstate i t)" 
    using Cptn(1) by (simp add: c_stepi)
  moreover have " (i,\<Gamma>, toParCptn i ((Q, t) # xs)) \<in> cptni" using Cptni
    by (metis Cptn.hyps(1) Cptn.hyps(3) \<open>\<forall>sn. s \<noteq> Normal sn \<and> s \<noteq> Abrupt sn\<close> 
          nth_Cons_0 snd_conv step_ce_notNormal)
  ultimately show ?case using toParCptn_simp
    by (simp add: toParCptn_simp cptni.Cptni)
qed

lemma cptn_cptni_Abrupt:
 "(\<Gamma>,c) \<in> cptn \<Longrightarrow> 
  snd(c!0) = Abrupt sn   \<Longrightarrow> i\<le> length (snd sn) \<Longrightarrow>
 (i,\<Gamma>, toParCptn i c) \<in> cptni"
proof (induct arbitrary: sn rule:cptn.induct)
  case (CptnOne \<Gamma> P s)
  then show ?case unfolding toParCptn_def using cptni.intros by auto
next
  case (Cptn \<Gamma> P s Q t xs)
  then have s:"s=Abrupt sn " and "s=t"
    apply simp
    using Cptn.hyps(1) Cptn.prems(1)
    using step_ce_notNormal by force     
  then  have "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,toPar_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toPar_xstate i t)" 
    using  Cptni(1) Cptn.hyps(1) c_stepi by blast
  moreover have " (i,\<Gamma>, toParCptn i ((Q, t) # xs)) \<in> cptni" using Cptni
    using Cptn.hyps(3) Cptn.prems(2) \<open>s = t\<close> s by fastforce
  ultimately show ?case using toParCptn_simp
    by (simp add: toParCptn_simp cptni.Cptni)
qed


lemma cptn_cptni_normal:
 "(\<Gamma>,c) \<in> cptn \<Longrightarrow> 
  snd(c!0) = Normal sn   \<Longrightarrow> i\<le> length (snd sn) \<Longrightarrow>
 (i,\<Gamma>, toParCptn i c) \<in> cptni"
proof (induct arbitrary: sn rule:cptn.induct)
  case (CptnOne \<Gamma> P s)
  then show ?case  unfolding toParCptn_def using cptni.intros by auto
next
  case (Cptn \<Gamma> P s Q t xs)
  then have s:"s=Normal sn "
    by simp    
  then  have "\<Gamma>\<turnstile>\<^sub>c\<^sub>i(P,toPar_xstate i s) \<rightarrow>\<^sub>c\<^sub>e (Q,toPar_xstate i t)" 
    using Cptn(1) c_stepi by blast 
  moreover have " (i,\<Gamma>, toParCptn i ((Q, t) # xs)) \<in> cptni"
  proof(cases t)
    case (Normal x1)
    then show ?thesis
      using Cptn.hyps(1) Cptn.hyps(3) Cptn.prems(2) s 
            step_cei_normal_normal_same_len
      by (simp add: ce_eq_length)
  next
    case (Abrupt x2)
    then show ?thesis
      by (metis Cptn.hyps(1) Cptn.hyps(2) Cptn.prems(2) 
               ce_eq_length cptn_cptni_Abrupt nth_Cons_0 s snd_conv)
  next
    case (Fault x3)
    then show ?thesis
      using Cptn.hyps(2) cptn_cptni_not_abrupt_normal by fastforce      
  next
    case Stuck
    then show ?thesis  using Cptn.hyps(2) cptn_cptni_not_abrupt_normal by force 
  qed
  ultimately show ?case using toParCptn_simp
    by (simp add: toParCptn_simp cptni.Cptni)
qed


lemma cptn_cptni:
 "(\<Gamma>,c) \<in> cptn \<Longrightarrow> 
  \<forall>sn. snd(c!0) = Normal sn \<or> snd(c!0) = Abrupt sn \<longrightarrow>  i\<le> length (snd sn) \<Longrightarrow>
 (i,\<Gamma>, toParCptn i c) \<in> cptni" 
  apply (cases "snd (c!0)") using cptn_cptni_normal cptn_cptni_Abrupt cptn_cptni_not_abrupt_normal 
  by fastforce+
 
lemma cptn_length_locs_less_i:
     assumes a0:"(\<Gamma>,c) \<in> cptn" and       
       a1:"\<forall>nas. (snd (c!0))= Normal nas \<or> (snd (c!0)) = Abrupt nas  \<longrightarrow> i\<le> length (snd nas)" 
     shows "\<forall>j<length c. (\<forall>nas. (snd (c!j))= Normal nas \<or> (snd (c!j)) = Abrupt nas  \<longrightarrow> 
            i\<le> length (snd nas))"
proof(cases "length c")
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then have len:"length c>0" by auto
  have  cptni:"(i,\<Gamma>, toParCptn i c) \<in> cptni" using cptn_cptni[OF a0 a1] by auto  
  then have "\<forall>nas. (snd (toParCptn i c!0))= Normal nas \<or> (snd (toParCptn i c!0)) = Abrupt nas  \<longrightarrow> 
             i< length (snd nas)"
    using a1 len unfolding toParCptn_def apply (cases "snd (c ! 0)", auto)  
    unfolding toParState_def Let_def split_beta
    by auto
  then have "\<forall>j<length (toParCptn i c). 
                (\<forall>nas. (snd ((toParCptn i c)!j))= Normal nas \<or> 
                         (snd ((toParCptn i c)!j)) = Abrupt nas  \<longrightarrow> 
                          i<length (snd nas))" using cptni_length_locs_less_i[OF cptni] 
    by fastforce
  then show ?thesis using len unfolding toParCptn_def 
    apply (auto)    
     apply (metis Suc_eq_plus1 len_toParState not_less not_less_eq prod.exhaust_sel snd_conv toPar_xstate.simps(1))
    by (metis Suc_eq_plus1 len_toParState not_less not_less_eq prod.exhaust_sel snd_conv toPar_xstate.simps(2)) 
qed


(* definition toParPred:: "(((('g, 'l, 'p,'f,'e) config_gs) list) \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ((('g,'l,'p,'f,'e) gconf list) \<Rightarrow> bool)"
  where "toParPred Q i \<equiv> (\<lambda>x. Q (toSeqCptn i x) )"

lemma "(\<Gamma>,c) \<in> cptn \<Longrightarrow> P c \<Longrightarrow> \<forall>sn. snd(c!0) = Normal sn \<or> snd(c!0) = Abrupt sn \<longrightarrow>  i\<le> length (snd sn) \<Longrightarrow>       
       (\<lambda>x. P (toSeqCptn i x)) (toParCptn i c)" *)


definition final_glob:: "('g,'l,'p,'f,'e) config_gs \<Rightarrow> bool" where
  "final_glob cfg \<equiv>   (fst cfg=Skip \<or> ((fst cfg=Throw) \<and> (\<exists>s. snd cfg=Normal s)))"
                                           
lemma final_eq:"final_glob cfg = SmallStepCon.final (fst cfg, toSeq (snd cfg))"
  unfolding final_def final_glob_def SmallStepCon.final_def
  by (cases "snd cfg",auto)

definition cpi1 :: "nat \<Rightarrow> ('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g\<times>'l,'p,'f,'e)com  \<Rightarrow>
                  (('g,'l)par_state,'f) xstate \<Rightarrow> (nat \<times>('g,'l,'p,'f,'e) gconfs) set" where
  "cpi1 i \<Gamma> P s \<equiv> {(i1,\<Gamma>1,l). l!0=(P,s) \<and> (i,\<Gamma>,l) \<in> cptni \<and> \<Gamma>1=\<Gamma>}"  

 

lemma cpi1_sub: 
  assumes a0: "(i,\<Gamma>,(x#l0)@l1) \<in> cpi1 i \<Gamma> P s"
  shows "(i,\<Gamma>,(x#l0)) \<in> cpi1 i \<Gamma> P s"
proof -    
  show ?thesis using a0 unfolding cpi1_def
    using cptni_dest_2 by fastforce
qed

definition wf_state:: "nat \<Rightarrow> (('g,'l)par_state,'f) xstate \<Rightarrow> bool"
  where "wf_state i s \<equiv> \<forall>ns. s=Normal ns \<or> s = Abrupt ns \<longrightarrow> i = length (snd ns)"

definition cpi :: "nat \<Rightarrow> nat \<Rightarrow> ('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g\<times>'l,'p,'f,'e)com  \<Rightarrow>
                  (('g,'l)par_state,'f) xstate \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) set" where
  "cpi len i \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (i,\<Gamma>,l) \<in> cptni \<and> \<Gamma>1=\<Gamma> \<and> wf_state len s}"  


lemma cpi_sub: 
  assumes a0: "(\<Gamma>,(x#l0)@l1) \<in> cpi len i \<Gamma> P s"
  shows "(\<Gamma>,(x#l0)) \<in> cpi len i \<Gamma> P s"
proof -    
  show ?thesis using a0 unfolding cpi_def
    using cptni_dest_2 by fastforce
qed

end