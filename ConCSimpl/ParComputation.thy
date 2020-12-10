theory ParComputation imports ComputationConGlob
begin
section \<open>Parallel Computation: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sub>p  (c', s')"}\<close>

type_synonym ('g,'l) par_state = "('g \<times> 'l list)"
type_synonym ('g,'l,'p,'f,'e) par_com = "('g \<times> 'l,'p,'f,'e)com  list" 
type_synonym ('g,'l,'p,'f,'e) par_config = "('g,'l,'p,'f,'e) par_com \<times> ('g,'l)par_state"
type_synonym ('g,'l,'p,'f,'e) par_confs = "('g\<times>'l,'p,'f,'e) body \<times> (('g,'l,'p,'f,'e) par_config) list"

definition par_seq_rel::"nat \<Rightarrow> (('g,'l) c_state \<times> ('g,'l) par_state) set"
  where "par_seq_rel i \<equiv> {(sc,pl). fst pl = fst (fst sc) \<and> (snd pl)!i = (snd (fst sc)) \<and> 
                                   i<length (snd pl) \<and> length (snd pl)-1 = length (snd sc) \<and>
                                 (\<forall>j<i. (snd pl)!j = (snd sc)!j) \<and> (\<forall>j>i. j<length (snd pl) \<longrightarrow> 
                                          (snd pl)!j = (snd sc)!(j-1))}"

lemma par_seq_rel_i_length:"(sc,pl) \<in> par_seq_rel i \<Longrightarrow> i<length (snd pl)"
  unfolding par_seq_rel_def by auto

lemma par_seq_rel_length:"(sc,pl) \<in> par_seq_rel i \<Longrightarrow> length (snd pl)-1 = length (snd sc)"
  unfolding par_seq_rel_def by auto

lemma par_seq_rel_globals:"(sc,pl) \<in> par_seq_rel i \<Longrightarrow> fst pl = fst (fst sc)"
  unfolding par_seq_rel_def by auto

lemma par_seq_rel_local:"(sc,pl) \<in> par_seq_rel i \<Longrightarrow> snd (fst sc) = (snd pl)!i"
  unfolding par_seq_rel_def by auto

lemma par_seq_rel_locals: 
  assumes a0:"(sc, pl) \<in>par_seq_rel i" 
  shows "snd sc = (take i (snd pl))@(drop (i+1) (snd pl))"
proof-
  have a003:"length ((take i (snd (pl)))@[((snd pl)!i)]) = i+1" 
    using a0 unfolding par_seq_rel_def by auto     
  moreover have "\<forall>j<length (snd sc). (snd sc)!j = ((take i (snd pl))@(drop (i+1) (snd pl)))!j"
    using  a003 using a0 unfolding par_seq_rel_def           
    by (auto simp add: List.nth_tl nth_append)                
  moreover have "length ((take i (snd pl))@(drop (i+1) (snd pl))) = (length (snd pl)) -1"
    using  calculation a0 unfolding par_seq_rel_def 
    by fastforce
  ultimately have "(snd sc) =(take i (snd pl))@(drop (i+1) (snd pl))"
    using a0 unfolding par_seq_rel_def 
    apply auto
    by (metis One_nat_def Suc_eq_plus1 
           \<open>length (take i (snd pl) @ drop (i + 1) (snd pl)) = length (snd pl) - 1\<close> nth_equalityI)    
  thus ?thesis by auto 
qed

definition par_state_rel::"nat \<Rightarrow> (('g,'l) c_state \<times> ('g,'l) par_state) set"
  where "par_state_rel i \<equiv> {(sc,pl). (sc, pl) \<in>par_seq_rel i}"

definition par_state_list_rel::"nat \<Rightarrow> ((('g, 'l,  'p,'f,'e) config_gs list \<times> ('g,'l,'p,'f,'e) gconf list)) set"
  where "par_state_list_rel i \<equiv> 
  {(ls, lp). list_all2 (\<lambda>s p. fst s = fst p \<and> (snd s, snd p)\<in>par_state_rel i)  ls lp}"

lemma par_seq_rel_seq:
  assumes a1:"(s1,s2)\<in>par_seq_rel i"
  shows "s1 = toSeqState i s2"  
  unfolding toSeqState_def Let_def split_beta apply auto
  using par_seq_rel_locals[OF a1] par_seq_rel_local[OF a1] par_seq_rel_globals[OF a1]
  by (metis Suc_eq_plus1 prod.collapse)
  

lemma par_seq_rel_par:
  assumes a1:"(s1,s2)\<in>par_seq_rel i"
  shows "s2 = toParState i s1"
  using par_seq_rel_seq
  by (metis Seq2Par assms par_seq_rel_i_length prod.exhaust_sel)

lemma par_xstate_rel_par:
  assumes a1:"(s1,s2)\<in>par_state_rel i"
  shows "s2 = toParState i s1"
  using a1 unfolding par_state_rel_def   
  by (auto intro: par_seq_rel_par)

lemma par_xstate_rel_seq:
  assumes a1:"(s1,s2)\<in>par_state_rel i"
  shows "s1 = toSeqState i s2"
  using a1 unfolding par_state_rel_def  
  by (auto intro: par_seq_rel_seq)


lemma toParState_in_rel:
      assumes a0:"i\<le> length (snd s)"
      shows"(s,toParState i s)\<in>par_seq_rel i"
proof-
  obtain pg pls where p:"(pg,pls) = toParState i s"
    by (metis surj_pair)
  moreover obtain sg sl sls where "((sg,sl),sls) = s"
    by (metis prod.collapse)    
  ultimately have "pg = sg" and "length pls = length sls +1" and
                  "sl = pls!i" and "\<forall>j<i. pls!j = sls!j" and
                  "\<forall>j>i. j<length pls \<longrightarrow> pls !j  = sls!(j-1)"   
    apply auto 
    using toPar_gi apply fastforce       
    by (simp add: toPar_li[OF a0] len_toParState_list toPar_ljlti[OF a0] toPar_ljgti[OF a0])+
  thus ?thesis unfolding par_seq_rel_def using \<open>((sg, sl), sls) = s\<close> a0 \<open>((sg, sl), sls) = s\<close>    
    apply auto            
    by (metis One_nat_def diff_Suc_1 fst_conv le_imp_less_Suc p snd_conv)+
qed

   
lemma toSeqState_in_rel:
  assumes a0:"i<length (snd s)"
  shows "(toSeqState i s,s)\<in>par_seq_rel i"
  by (metis Seq2Par assms diff_Suc_1 len_toSeqState less_Suc_eq_le less_imp_Suc_add 
      prod.exhaust_sel toParState_in_rel)

lemma data_ref:"(x,y) \<in> r \<Longrightarrow> 
       r `` Q \<subseteq> Q'  \<Longrightarrow> x \<in> Q \<Longrightarrow> y\<in>Q'"
  by auto 

lemma data_ref_pred:"(x,y) \<in> r \<Longrightarrow> 
       r `` (Collect Q) \<subseteq> (Collect Q')  \<Longrightarrow> Q x \<Longrightarrow> Q' y"
  by auto 

lemma data_ref_par:"(s,p)\<in>par_seq_rel i \<Longrightarrow>
               (par_seq_rel i) `` Q \<subseteq> Q' \<Longrightarrow> s\<in>Q \<Longrightarrow>  
               p \<in> Q'"
  using data_ref by fastforce

lemma data_ref_seq: 
   "(s, p)\<in>par_seq_rel i \<Longrightarrow> 
      (par_seq_rel i)\<inverse> `` Q' \<subseteq>  Q \<Longrightarrow> p\<in>Q' \<Longrightarrow>  
     s \<in> Q"
 using data_ref by fastforce

lemma data_ref_par_pred:"(s,p)\<in>par_seq_rel i \<Longrightarrow>
               (par_seq_rel i) `` (Collect Q) \<subseteq> (Collect Q') \<Longrightarrow> Q s \<Longrightarrow>  
               Q' p"
  using data_ref_pred by blast

lemma data_ref_seq_pred:"(s, p)\<in>par_seq_rel i \<Longrightarrow>
               (par_seq_rel i)\<inverse> `` (Collect Q') \<subseteq> (Collect Q) \<Longrightarrow> Q' p \<Longrightarrow>  
               Q s"
  using data_ref_pred by blast



lemma data_ref_par_xstate_tuple_pred:
   "((s1,s2),(p1,p2))\<in> {(s,p). (fst s,fst p) \<in> par_state_rel i \<and> (snd s,snd p) \<in> par_state_rel i} \<Longrightarrow>     
    {(s,p). (fst s,fst p) \<in> par_state_rel i \<and> (snd s,snd p) \<in> par_state_rel i} `` 
        (Collect Q) \<subseteq>  (Collect Q') \<Longrightarrow> Q (s1,s2) \<Longrightarrow>  
     Q' (p1,p2)"
  using data_ref by fast

lemma toPar_state_in_rel: 
  assumes  a0:"i\<le> length (snd s)"
  shows "(s, toParState i s) \<in> par_state_rel i"
  unfolding par_state_rel_def
  using  a0 
  by (simp add: toParState_in_rel)

lemma toSeq_state_in_rel: 
  assumes a0:"s=(g,ls)" and a0':"i< length ls"
  shows "(toSeqState i s, s) \<in> par_state_rel i"
  unfolding par_state_rel_def
  apply (auto)
  by (simp add: a0 a0' toSeqState_in_rel)

lemma data_ref_par_state:
   "(s,p)\<in>par_xstate_rel i \<Longrightarrow>
     par_xstate_rel i `` Q \<subseteq> Q' \<Longrightarrow> s\<in>Q \<Longrightarrow>  
     p \<in> Q'"
  using data_ref by fastforce

lemma data_ref_par_state_pred:
   "(s,p)\<in>par_xstate_rel i \<Longrightarrow>
     par_xstate_rel i ``  (Collect Q) \<subseteq>  (Collect Q') \<Longrightarrow> Q s \<Longrightarrow>  
     Q' p"
  using data_ref by fastforce

lemma data_ref_seq_state:
   "(toSeq_xstate i s, s)\<in>par_xstate_rel i\<Longrightarrow>
     (par_xstate_rel i)\<inverse> `` Q' \<subseteq> Q \<Longrightarrow> s\<in>Q' \<Longrightarrow>  
     toSeq_xstate i s \<in> Q"
  using data_ref by fastforce

lemma data_ref_seq_state_pred:
   "(s, p)\<in>par_xstate_rel i \<Longrightarrow>
     (par_xstate_rel i)\<inverse> `` (Collect Q') \<subseteq> (Collect Q) \<Longrightarrow> Q' p \<Longrightarrow>  
     Q s"
  using data_ref by fastforce

lemma toSeqCptn_in_rel:
     "\<forall>j<length ls. i< length (snd (snd (ls!j))) \<Longrightarrow>
        (toSeqCptn i ls, ls) \<in> par_state_list_rel i"
  unfolding  par_state_list_rel_def 
  by (auto intro:list_all2_all_nthI simp add: par_state_rel_def toSeqCptn_def toSeqState_in_rel)  


lemma toParCptn_in_rel:
   "\<forall>j<length ls.  i\<le> length (snd (snd (ls!j))) \<Longrightarrow>
        (ls, toParCptn i ls) \<in> par_state_list_rel i"
  unfolding  par_state_list_rel_def
  by(auto intro: list_all2_all_nthI simp add: par_state_rel_def toParState_in_rel toParCptn_def)

lemma data_ref_par_xstatelist:
   "(ls, lp)\<in>par_xstate_list_rel i \<Longrightarrow>
     (par_xstate_list_rel i)`` Q \<subseteq> Q' \<Longrightarrow> ls \<in> Q \<Longrightarrow>  
     lp \<in> Q'"
  using data_ref by fastforce

lemma data_ref_par_xstatelist_pred:
   "(ls, lp)\<in>par_xstate_list_rel i \<Longrightarrow>
     (par_xstate_list_rel i)`` (Collect Q) \<subseteq> (Collect Q') \<Longrightarrow>  Q ls \<Longrightarrow>  
     Q' lp"
  using data_ref by fastforce

lemma data_ref_seq_xstatelist:
   "(ls,lp)\<in>par_xstate_list_rel i \<Longrightarrow>
     (par_xstate_list_rel i)\<inverse> `` Q' \<subseteq> Q \<Longrightarrow> lp\<in>Q' \<Longrightarrow>  
     ls \<in> Q"
  using data_ref by fastforce

lemma data_ref_seq_xstatelist_pred:
   "(ls, lp)\<in>par_xstate_list_rel i \<Longrightarrow>
     (par_xstate_list_rel i)\<inverse> `` (Collect Q') \<subseteq> (Collect Q) \<Longrightarrow> Q' lp \<Longrightarrow>  
     Q ls"
  using data_ref by fastforce

lemma data_ref_seq_xstatelist_pred_par:
   "(ls, lp)\<in>par_xstate_list_rel i \<Longrightarrow>
      (par_xstate_list_rel i) `` (Collect Q) \<subseteq> (Collect Q') \<Longrightarrow> Q ls \<Longrightarrow>  
      Q' lp"
  using data_ref by fastforce

definition final1:: "('s,'p,'f,'e)com \<Rightarrow>  'gs \<Rightarrow> bool" where
"final1 c s \<equiv> c = Skip \<or> c = Throw \<or> (\<exists>f. c= Fault f) \<or> c = Stuck"

lemma final_eq_final1:"final ((fst cfg),(snd cfg)) = final1 (fst cfg) (snd cfg)"
  unfolding final_def final1_def by auto

definition final_c:: "('g, 'l, 'p,'f,'e) par_config \<Rightarrow> bool" where
"final_c cfg = (\<forall>i. i<length (fst cfg) \<longrightarrow> final1 ((fst cfg)!i)  (snd cfg))"

inductive
      "step_pe"::"[('g\<times>'l,'p,'f,'e) body,('g,'l,'p,'f,'e) par_config,
                   ('g,'l, 'p,'f,'e) par_config] \<Rightarrow> bool"      
                                ("_\<turnstile>\<^sub>p (_ \<rightarrow>\<^sub>e/ _)" [81,81,81] 100)  
  for \<Gamma>::"('g\<times>'l,'p,'f,'e) body"
where
ParEnv: "\<Gamma>\<turnstile>\<^sub>p (Ps, (g,l)) \<rightarrow>\<^sub>e (Ps,  (g',l))"


lemma ptranE: "\<Gamma>\<turnstile>\<^sub>p c \<rightarrow>\<^sub>e c' \<Longrightarrow> (\<And>P s t. c = (P, s) \<Longrightarrow> c' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct c, induct c', erule  step_pe.cases, blast)

inductive_cases step_pe_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(PS,s) \<rightarrow>\<^sub>e (Ps,t)"

lemma env_pe_c_c'_false:
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "~(c=c')  \<Longrightarrow> P"
using step_m ptranE by blast

lemma env_pe_c_c':
   assumes step_m: "\<Gamma>\<turnstile>\<^sub>p (c, s) \<rightarrow>\<^sub>e (c', s')" 
   shows "(c=c')"
using env_pe_c_c'_false step_m by fastforce 


fun toSeqPar ::"nat \<Rightarrow> 'g\<times>('l list) \<Rightarrow> ('g\<times>'l)"
  where
"toSeqPar i s = (fst s, snd s!i)"

(* definition meaning :: "('g, 'l) global_s \<Rightarrow> ('g\<times>'l list)"
  where "meaning arg1 = (let conc = Rep_global_s arg1 in undefined)"

lift_definition toSeqPar3 :: "nat \<Rightarrow> ('g, 'l) global_s \<Rightarrow> ('g, 'l) global_s"
  is "\<lambda>i arg. undefined" sorry

lift_definition toSeqPar4 :: "nat \<Rightarrow>('g\<times>'l) \<Rightarrow> ('l) list \<Rightarrow> ('g, 'l) global_s"
  is "\<lambda>i arg1 arg2. undefined" sorry *)

fun getList::"'g\<times>('l list) \<Rightarrow> 'l list"
  where 
"getList s = snd s"

fun toPar ::"nat \<Rightarrow> ('g\<times>'l) \<Rightarrow> 'g\<times>('l list)  \<Rightarrow> 'g\<times>('l list)"
  where
"toPar i s s' = (fst s, (getList s')[i:= snd s])"


lemma toSeqPar_eq_toSeq: 
  shows "toSeqPar i s = toSeq (toSeqState i s)"
  by (auto simp add: toSeqState_def split_beta)

lemma toSeqPar_toSeq:"toSeq(toSeqState i s) =  toSeqPar i s "
  by (auto simp add:  toSeqState_def split_beta)

lemma toPar_eq_globs:
     "sa = toPar i s' s \<Longrightarrow> 
      (\<forall>j. j\<noteq>i\<longrightarrow> snd (sa)!j = snd s!j)"
  by auto

lemma to_par_toSeq: assumes a0:"sa = toPar i s' s" and 
a3:"i<length (snd s)" and 
a5:"length (snd s) = length (snd sa)"
  shows  " snd (toSeqState i s) = snd (toSeqState i sa)"
  by (simp add: a0 a3 same_local_sublist_toSeq_State)


lemma to_par_toSeqState: assumes a0:"sa = toPar i s' s" and    
a3:"i<length (snd s)" and a5:"length (snd s) = length (snd sa)"
  shows  " snd (toSeqState i s) = snd (toSeqState i sa)"
  using a0 a3 a5 to_par_toSeq by blast

inductive       
"step_p"::"[('g\<times>'l,'p,'f,'e) body, ('g,'l,'p,'f,'e) par_config, 
            ('g,'l,'p,'f,'e) par_config] \<Rightarrow> bool"
("_\<turnstile>\<^sub>p (_ \<rightarrow>/ _)" [81,81,81] 100)  
where
 ParComp: "\<lbrakk>i<length Ps;  \<Gamma>\<turnstile>\<^sub>c(Ps!i,toSeqPar i s) \<rightarrow> (r,s')\<rbrakk> \<Longrightarrow>  
           \<Gamma>\<turnstile>\<^sub>p(Ps, s) \<rightarrow> (Ps[i:=r], toPar i s' s)"

  
lemmas steppe_induct = step_p.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
ParComp, induct set]

inductive_cases step_p_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(Ps, s) \<rightarrow> u"

inductive_cases step_p_pair_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<^sub>p(Ps, s) \<rightarrow> (Qs, t)"

lemma ParCompNormalI:
  assumes a0:"i<length Ps" and a1:"\<Gamma>\<turnstile>\<^sub>c(Ps!i,  (g,ls!i)) \<rightarrow> (r, (g',l'))"
  shows"\<Gamma>\<turnstile>\<^sub>p(Ps,  (g,ls)) \<rightarrow> (Ps[i:=r],  (g',ls[i:=l']))"  
proof-
  have "toSeqPar i ( (g,ls)) =  (g,ls!i)" by auto
  moreover have "toPar i ( (g',l')) ( (g,ls)) =  (g',ls[i:=l'])" by auto
  ultimately show ?thesis using ParComp a0 a1 by metis
qed


lemma par_ctranE: "\<Gamma> \<turnstile>\<^sub>p c \<rightarrow> c' \<Longrightarrow>
  (\<And>i Ps s r s'. c = (Ps, s) \<Longrightarrow> c' = (Ps[i := r], toPar i s' s) \<Longrightarrow> i < length Ps \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>c (Ps!i, toSeqPar i s) \<rightarrow> (r, s') \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule step_p.cases, blast)


lemma par_ctranNE:"\<Gamma>\<turnstile>\<^sub>p (Ps,  s) \<rightarrow> (Ps',  s') \<Longrightarrow>
 (\<And>i r ss'.
    i < length Ps \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps ! i,  (fst s, snd s ! i)) \<rightarrow> (r,  ss') \<Longrightarrow> Ps' = Ps[i := r] \<Longrightarrow>
     s' = (fst ss', (snd s)[i:=(snd ss')])
    \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule step_p.cases, auto)


lemma par_ctransN:"\<Gamma>\<turnstile>\<^sub>p (Ps, s) \<rightarrow> (Ps',  t) \<Longrightarrow>
 (\<And>i r t'.
    i < length Ps \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps ! i,  (fst s, snd s ! i)) \<rightarrow> (r,  t') \<Longrightarrow> Ps' = Ps[i := r]   \<Longrightarrow>
   t = (fst t', (snd s)[i:=(snd t')]) \<Longrightarrow>  P) \<Longrightarrow> P"
  by (erule step_p.cases, auto)

  
lemma pe_ce: 
  assumes a1:"\<Gamma>\<turnstile>\<^sub>p(P,s) \<rightarrow>\<^sub>e (P,t)"
  shows "\<forall>i<length P. \<Gamma>\<turnstile>\<^sub>c(P!i,toSeqState i s) \<rightarrow>\<^sub>e (P!i,toSeqState i t)"
proof-
   have  "snd s = snd t" using a1   
     by (metis snd_conv step_pe_elim_cases)          
   then show ?thesis 
     by (simp add: env_intro prod.case_eq_if  toSeqState_def)   
qed

lemma pe_step_cei_step:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow>\<^sub>e (as, sa)" and 
          a1:"length xs = length (snd s)"
  shows"\<forall>i < length xs. \<Gamma>\<turnstile>\<^sub>c\<^sub>i (xs!i, s) \<rightarrow>\<^sub>c\<^sub>e (as!i, sa)"       
proof-
  { fix i
    assume a00:"i<length xs"    
    have sa_s:"(s = sa) \<or> (snd s = snd sa)"
      using step_pe_elim_cases[OF a0] by fastforce 
    have xs_as_eq:"xs=as" using a0 by (meson env_pe_c_c'_false)     
     then have ce:"\<Gamma>\<turnstile>\<^sub>c (xs!i, toSeqState i s) \<rightarrow>\<^sub>e (as!i, toSeqState i sa)" using a00 a0 pe_ce by fastforce
    then have ce':"\<Gamma>\<turnstile>\<^sub>c (xs!i, toSeqState i s) \<rightarrow>\<^sub>c\<^sub>e (as!i, toSeqState i sa)"
      by (simp add: e_step)    
     have "\<Gamma>\<turnstile>\<^sub>c\<^sub>i (xs!i, s) \<rightarrow>\<^sub>c\<^sub>e (as!i, sa)" 
       by (metis a00 a1 ce' sa_s step_ce_to_step_cei2)           
    then have ?thesis using sa_s
      by (metis a0 a1 pe_ce step_cei_i2 xs_as_eq)        
  } thus ?thesis by auto
qed

lemma toPar_toSeqPar:
  "length (snd s) = length (snd s') \<Longrightarrow> \<forall>j\<noteq>i. (snd s!j) = (snd s'!j) \<Longrightarrow>
       s' = toPar i (toSeqPar i s') s"
  apply auto
  by (smt fst_conv length_list_update list_update_beyond not_le 
         nth_equalityI nth_list_update prod_eqI snd_conv)

lemma p_step_cei:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c (xs!i, toSeqPar i s) \<rightarrow> (c', toSeqPar i s')"  and a0':"i<length xs" and                 
          a2:"length xs = length (snd s)" and a3:"length (snd s) = length (snd s')" and
          a4:"\<forall>j\<noteq>i. (snd s!j) = (snd s'!j)"
        shows "\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow> (xs[i:=c'], s')"   
proof-
  have  "\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow> (xs[i:=c'], toPar i (toSeqPar i s') s)"
    using ParComp[OF a0' a0] by auto
  thus ?thesis using toPar_toSeqPar[OF a3 a4] a0' a2  by auto                   
qed


lemma eq_length_p_step':"\<Gamma>\<turnstile>\<^sub>p (Ps, s) \<rightarrow> (Ps', s') \<Longrightarrow>
                        length (snd s) = length (snd s') "
  by (erule step_p.cases,auto)    

lemma eq_length_p_step'':"\<Gamma>\<turnstile>\<^sub>p (Ps, s) \<rightarrow> (Ps', s') \<Longrightarrow>   length Ps \<le> length (snd s) \<Longrightarrow>
       length Ps \<le> length (snd s') "
  by (erule step_p.cases,auto) 


lemma eq_length_p_step:"\<Gamma>\<turnstile>\<^sub>p (Ps, s) \<rightarrow> (Ps', s') \<Longrightarrow> 
                         length (snd s) = length (snd s') "
  by (erule step_p.cases,auto)

lemma step_p_elim_toseqpar:
   "\<Gamma>\<turnstile>\<^sub>p (Ps, s) \<rightarrow> (Ps', s') \<Longrightarrow> length Ps \<le> length (snd s) \<Longrightarrow>      
      (\<And>i r  ss ss'.
    i < length Ps \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c (Ps ! i, toSeqPar i s) \<rightarrow> (r, toSeqPar i s') \<Longrightarrow> Ps' = Ps[i := r]   \<Longrightarrow>
    (ss = toSeqPar i s \<and> ss'=toSeqPar i s')  \<Longrightarrow> P) \<Longrightarrow> P"  
  apply (frule eq_length_p_step'', auto)
  by (erule step_p.cases,auto)


lemma final_c_step_false:
   "\<Gamma>\<turnstile>\<^sub>p (Ps, s) \<rightarrow> (Ps', s') \<Longrightarrow> final_c (Ps,s) \<Longrightarrow>  P" 
  unfolding final_c_def final1_def
  apply (auto)
  apply (erule step_p.cases,auto)
  by (metis fault_no_tran stepc_elim_cases(1) stepc_elim_cases(11) stepc_elim_cases(14))

subsubsection \<open>Parallel computations\<close>

inductive_set par_cptn :: "('g,'l,'p,'f,'e) par_confs set"
where
  ParCptnOne: "(\<Gamma>, [(P,s)]) \<in> par_cptn"
| ParCptnEnv: "\<lbrakk>\<Gamma>\<turnstile>\<^sub>p(P,s) \<rightarrow>\<^sub>e (P,t);(\<Gamma>,(P, t)#xs) \<in> par_cptn \<rbrakk> \<Longrightarrow>(\<Gamma>,(P,s)#(P,t)#xs) \<in> par_cptn"
| ParCptnComp: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>p(P,s) \<rightarrow> (Q,t); (\<Gamma>,(Q,t)#xs) \<in> par_cptn \<rbrakk> \<Longrightarrow> (\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn"

inductive_cases par_cptn_elim_cases [cases set]:
"(\<Gamma>, [(P,s)]) \<in> par_cptn"
"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn"


lemma par_cptn_all_final': 
"(\<Gamma>,c) \<in> par_cptn \<Longrightarrow> final_c (c!0) \<Longrightarrow> i<length c \<Longrightarrow> fst (c!i) = fst (c!0)"
proof(induct arbitrary: i rule:par_cptn.induct)
  case (ParCptnOne \<Gamma> P s)
  then show ?case
    by simp 
next
  case (ParCptnEnv \<Gamma> P s t xs)
  then have  "final_c (P,t)" unfolding final_c_def final1_def by auto
  then show ?case using ParCptnEnv
    by (metis diff_Suc_1 fst_conv length_Cons less_Suc_eq_0_disj nth_Cons')
next
  case (ParCptnComp \<Gamma> P s Q t xs)  
  then show ?case using final_c_step_false
    by (metis nth_Cons_0)
qed

lemma par_cptn_all_final: 
"(\<Gamma>,c) \<in> par_cptn \<Longrightarrow> final_c (c!0) \<Longrightarrow> i<length c \<Longrightarrow> final_c (c!i)"
  apply (frule par_cptn_all_final', assumption+)
  by (auto simp add: final_c_def final1_def)

definition par_cp :: "('g\<times>'l,'p,'f,'e) body \<Rightarrow> ('g,'l,'p,'f,'e) par_com \<Rightarrow> 
                      ('g,'l)par_state \<Rightarrow> ('g,'l,'p,'f,'e) par_confs set" 
where                                                                  
  "par_cp \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> par_cptn \<and> \<Gamma>1=\<Gamma> \<and> (length P \<le> length (snd s))}"  
                                                 
(* definition par_cp :: "('s,'p,'f,'e) body \<Rightarrow> ('s,'p,'f,'e) com list \<Rightarrow> ('s,'f) xstate \<Rightarrow> (('s,'p,'f,'e) par_confs) set" 
where
  "par_cp \<Gamma> P s \<equiv> {(\<Gamma>1,l). l!0=(P,s) \<and> (\<Gamma>,l) \<in> par_cptn \<and> \<Gamma>1=\<Gamma>}" *)

lemma par_cptn_dest:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn \<Longrightarrow> (\<Gamma>,(Q,t)#xs)\<in> par_cptn"
  by (auto dest: par_cptn_elim_cases)

lemma takepar_cptn_is_par_cptn [rule_format,elim]:
  "\<forall>j. (\<Gamma>,c) \<in> par_cptn \<longrightarrow> (\<Gamma>,take (Suc j) c) \<in> par_cptn"
apply(induct "c")
 apply(force elim: cptn.cases)
apply clarify
apply(case_tac j,simp)
 apply(rule ParCptnOne)
apply(force intro:par_cptn.intros elim:par_cptn.cases)
done

lemma droppar_cptn_is_par_cptn [rule_format]:
  "\<forall>j<length c. (\<Gamma>,c) \<in> par_cptn \<longrightarrow> (\<Gamma>,drop j c) \<in> par_cptn"
apply(induct "c")
 apply(force elim: par_cptn.cases)
apply clarify
apply(case_tac j,simp+)
apply(erule par_cptn.cases)
  apply simp
 apply force
apply force
done

lemma par_cptn_dest_pair:"(\<Gamma>,x#x1#xs) \<in> par_cptn \<Longrightarrow> (\<Gamma>,x1#xs)\<in> par_cptn"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> par_cptn"
  thus ?thesis using par_cptn_dest prod.collapse by metis
qed

lemma par_cptn_dest1:"(\<Gamma>,(P,s)#(Q,t)#xs) \<in> par_cptn \<Longrightarrow> (\<Gamma>,(P,s)#[(Q,t)])\<in> par_cptn"
proof -
  assume a1: "(\<Gamma>, (P, s) # (Q, t) # xs) \<in> par_cptn"
  have "(\<Gamma>, [(Q, t)]) \<in> par_cptn"
    by (meson par_cptn.ParCptnOne)
  thus ?thesis
    using a1 ParCptnEnv ParCptnComp par_cptn.cases by blast
qed

lemma par_cptn_dest1_pair:"(\<Gamma>,x#x1#xs) \<in> par_cptn \<Longrightarrow> (\<Gamma>,x#[x1])\<in> par_cptn"
proof -
  assume "(\<Gamma>,x#x1#xs) \<in> par_cptn"
  thus ?thesis using par_cptn_dest1 prod.collapse by metis
qed

lemma par_cptn_append_is_par_cptn [rule_format]: 
 "\<forall>b a. (\<Gamma>,b#c1)\<in>par_cptn \<longrightarrow>  (\<Gamma>,a#c2)\<in>par_cptn \<longrightarrow> (b#c1)!length c1=a \<longrightarrow> (\<Gamma>,b#c1@c2)\<in>par_cptn"
apply(induct c1)
 apply simp
apply clarify
apply(erule par_cptn.cases,simp_all)
  by (auto simp add: par_cptn.ParCptnEnv ParCptnComp)
(* apply (simp add: cptn.CptnEnv)
by (simp add: cptn.CptnComp) *)

lemma par_cptn_dest_2:
  "(\<Gamma>,a#xs@ys) \<in> par_cptn  \<Longrightarrow> (\<Gamma>,a#xs)\<in> par_cptn"
proof (induct "xs" arbitrary: a)
  case Nil thus ?case using par_cptn.simps
  proof -
    have "\<exists>p. [p] = [a]"
      by blast
    then show ?thesis
      using par_cptn.simps by fastforce
  qed  
next
  case (Cons x xs') 
  then have "(\<Gamma>,a#[x])\<in>par_cptn" by (simp add: par_cptn_dest1_pair)
  also have "(\<Gamma>, x # xs') \<in> par_cptn"
    using Cons.hyps Cons.prems par_cptn_dest_pair by fastforce    
  ultimately show ?case using par_cptn_append_is_par_cptn [of \<Gamma> a "[x]" x xs']
    by force    
qed   


lemma tl_in_par_cptn: "\<lbrakk> (g,a#xs) \<in>par_cptn; xs\<noteq>[] \<rbrakk> \<Longrightarrow> (g,xs)\<in>par_cptn"
  by (force elim: par_cptn.cases)

lemma sublist_in_par_cptn:"(\<Gamma>, ys@ xs) \<in> par_cptn \<Longrightarrow> xs\<noteq> [] \<Longrightarrow> (\<Gamma>, xs) \<in> par_cptn"
proof(induct ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  then have "(\<Gamma>, a # (ys @ xs)) \<in> par_cptn" by auto
  then show ?case 
    by (metis Cons.hyps Cons.prems(2) Nil_is_append_conv tl_in_par_cptn)  
qed

lemma par_cptn_step_ce:
  assumes a0:"(\<Gamma>,c) \<in> par_cptn" and a1:"j<(length c)-1"
  shows "\<Gamma>\<turnstile>\<^sub>p (c!j) \<rightarrow>\<^sub>e  (c!(j+1)) \<or> \<Gamma>\<turnstile>\<^sub>p (c!j) \<rightarrow>  (c!(j+1))"
proof-
 obtain c' c'' where "c = c'@([c!j,c!(j+1)]@c'')" using sublist[OF a1] by auto
  then have "(\<Gamma>,c!j#(c!(j+1))#c'') \<in>par_cptn" using a0 sublist_in_par_cptn
    by (metis append_Cons append_Nil list.distinct(1))
  then obtain pj sj pj1 sj1 
    where cptni:"(\<Gamma>,(pj,sj)#(pj1,sj1)#c'') \<in>par_cptn" and 
          cj:"c!j = (pj,sj)" and cj1:"c!(j+1) =(pj1,sj1)"
    by (metis prod.exhaust_sel)     
  then show ?thesis using par_cptn_elim_cases(2)[OF cptni] by force  
qed

lemma all_same_length:"(\<Gamma>,c) \<in> par_cptn \<Longrightarrow> i < length c \<Longrightarrow> length (fst (c!0)) = length (fst (c!i))"
proof (induct i)
  case 0
  then show ?case
    by blast 
next
  case (Suc i)
  then have "\<Gamma>\<turnstile>\<^sub>p (c!i) \<rightarrow>\<^sub>e  (c!(i+1)) \<or> \<Gamma>\<turnstile>\<^sub>p (c!i) \<rightarrow>  (c!(i+1))"
    by (metis (no_types) Suc.prems(1) Suc.prems(2) Suc_eq_plus1 less_diff_conv par_cptn_step_ce)
  moreover have "length (fst (c ! 0)) = length (fst (c ! i))" using Suc by auto 
  ultimately show ?case
    apply auto using step_pe_elim_cases
    apply (metis fst_conv old.prod.exhaust)     
    using step_p_pair_elim_cases
    by (metis length_list_update prod.exhaust_sel)
qed

lemma par_cptn_all_not_normal: "(\<Gamma>,c) \<in> par_cptn \<Longrightarrow>final_c (c!i) \<Longrightarrow> j<length c \<Longrightarrow> 
                                 i\<le>j \<Longrightarrow> final_c (c!j)"
proof-
  assume a0:"(\<Gamma>,c) \<in> par_cptn" and a1:"final_c (c!i)" and a2:"j<length c" and a3:"i\<le>j"
  moreover have  c:"c = (take i c)@ (c!i# drop (Suc i) c)"
    using calculation id_take_nth_drop le_less_trans by blast   
  ultimately have a0':"(\<Gamma>,(take i c)@ (c!i# drop (Suc i) c)) \<in> par_cptn" by auto
  then have par:"(\<Gamma>,(c!i# drop (Suc i) c)) \<in> par_cptn" using sublist_in_par_cptn[OF a0'] by auto
  have "\<forall>j<(length (drop (Suc i) c)) + 1. final_c ((c!i# drop (Suc i) c)!j)"  
    using par_cptn_all_final[OF par]
    by (simp add: a1)
  thus ?thesis using a2 a3 c
    by (smt One_nat_def leD le_add_diff_inverse le_less_trans length_append length_take less_imp_le_nat list.size(4)
     min.absorb2 nat_add_left_cancel_less nth_append)
qed


subsection \<open>Compositionality of the Semantics\<close>

subsubsection \<open>Definition of the conjoin operator\<close>

definition same_length :: "('g,'l,'p,'f,'e) par_confs \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) list \<Rightarrow> bool" where
  "same_length c clist \<equiv> (\<forall>i<length clist. length(snd (clist!i))=length (snd c))"

lemma same_length_non_pair:
  assumes a1:"same_length c clist " and
          a2:"clist'=map (\<lambda>x. snd x) clist"
  shows "(\<forall>i <length clist'. length( (clist'!i))=length (snd c))"
using a1 a2 by (auto simp add: same_length_def)


definition same_state :: "('g,'l,'p,'f,'e) par_confs \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) list \<Rightarrow> bool" where
  "same_state c clist \<equiv> (\<forall>i <length clist. \<forall>j<length (snd c). snd((snd c)!j) = snd((snd (clist!i))!j))"

lemma same_state_non_pair:
  assumes a1:"same_state c clist " and
          a2:"clist'=map (\<lambda>x. snd x) clist"
  shows "(\<forall>i <length clist'. \<forall>j<length (snd c). snd((snd c)!j) = snd( (clist'!i)!j))"
using a1 a2 by (auto simp add: same_state_def)

definition same_program :: "('g,'l,'p,'f,'e) par_confs \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) list \<Rightarrow> bool" where
  "same_program c clist \<equiv> (\<forall>j<length (snd c). fst((snd c)!j) = map (\<lambda>x. fst(nth (snd x) j)) clist)"

lemma same_program_non_pair:
  assumes a1:"same_program c clist " and
          a2:"clist'=map (\<lambda>x. snd x) clist"
  shows "(\<forall>j<length (snd c). fst((snd c)!j) = map (\<lambda>x. fst(nth x j)) clist')"
using a1 a2 by (auto simp add: same_program_def)

definition same_functions :: "('g,'l,'p,'f,'e) par_confs \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) list \<Rightarrow> bool" where
 "same_functions c clist \<equiv> \<forall>i <length clist. fst (clist!i) = fst c"


definition compat_label :: "('g,'l,'p,'f,'e) par_confs \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) list \<Rightarrow> bool" where
  "compat_label c clist \<equiv> 
    let (\<Gamma>c, cfgs) = c in
     (\<forall>j. Suc j<length cfgs \<longrightarrow> 
         (\<Gamma>c\<turnstile>\<^sub>p(cfgs!j)  \<rightarrow> (cfgs!(Suc j)) \<and> 
            (\<exists>i<length clist. 
               (fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeq (toSeqState i (snd((snd (clist!i))!j)))) \<rightarrow>  
                   (fst ((snd (clist!i))!(Suc j)), toSeq (toSeqState  i (snd((snd (clist!i))!(Suc j))))) \<and> 
            (\<forall>l<length clist.                                           
               l\<noteq>i \<longrightarrow>  (fst (clist!l))\<turnstile>\<^sub>c(fst ((snd (clist!l))!j),  toSeqState l (snd((snd (clist!l))!j))) \<rightarrow>\<^sub>e  
                        (fst ((snd (clist!l))!(Suc j)), toSeqState  l (snd((snd (clist!l))!(Suc j))))  ))) \<or> 
         (\<Gamma>c\<turnstile>\<^sub>p(cfgs!j)  \<rightarrow>\<^sub>e (cfgs!(Suc j)) \<and> 
          (\<forall>i<length clist. (fst (clist!i))\<turnstile>\<^sub>c(fst ((snd (clist!i))!j),  toSeqState i (snd((snd (clist!i))!j))) \<rightarrow>\<^sub>e  
                            (fst ((snd (clist!i))!(Suc j)), toSeqState  i (snd((snd (clist!i))!(Suc j)))))))"

(* definition compat_label :: "('g,'l,'p,'f,'e) par_confs \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) list \<Rightarrow> bool" where
  "compat_label c clist \<equiv> 
    let (\<Gamma>c, cfgs) = c;
        cptni = (\<lambda>i. clist!i);
        \<Gamma>i = (\<lambda>i. fst (cptni i));
        cfgli = (\<lambda>i. snd (cptni i));
        cfgij=  (\<lambda>i j. (cfgli i)!j);
        seqcfg = (\<lambda>i j. (fst (cfgij i j), toSeq_xstate i (snd (cfgij i j))));
        seqseqcfg = (\<lambda>i j. (fst (cfgij i j), toSeq (toSeq_xstate i (snd (cfgij i j))))) in
     (\<forall>j. Suc j<length cfgs \<longrightarrow> 
         (\<Gamma>c\<turnstile>\<^sub>p(cfgs!j)  \<rightarrow> (cfgs!(Suc j)) \<and> 
            (\<exists>i<length clist. 
               (\<Gamma>i i\<turnstile>\<^sub>c seqseqcfg i j  \<rightarrow> seqseqcfg i (Suc j)) \<and> 
            (\<forall>l<length clist.                                           
               l\<noteq>i \<longrightarrow>  (\<Gamma>i l)\<turnstile>\<^sub>c seqcfg l j  \<rightarrow>\<^sub>e seqcfg l (Suc j)  ))) \<or> 
         (\<Gamma>c\<turnstile>\<^sub>p(cfgs!j)  \<rightarrow>\<^sub>e (cfgs!(Suc j)) \<and> 
          (\<forall>i<length clist. (\<Gamma>i i)\<turnstile>\<^sub>c seqcfg i j  \<rightarrow>\<^sub>e seqcfg i (Suc j))))"
*)

lemma compat_label_tran_0:
 assumes assm1:"compat_label c clist \<and> length (snd c) > Suc 0" 
 shows  "((fst c)\<turnstile>\<^sub>p((snd c)!0)  \<rightarrow> ((snd c)!(Suc 0))) \<or> 
      ((fst c)\<turnstile>\<^sub>p((snd c)!0)  \<rightarrow>\<^sub>e ((snd c)!(Suc 0)))"    
  using assm1 unfolding compat_label_def Let_def split_beta
  by blast

definition same_length_state_program::"(('g,'l,'p,'f,'e) par_config) list \<Rightarrow> bool"
  where "same_length_state_program c  \<equiv>           
         c \<noteq> [] \<longrightarrow> length (fst (c!0)) \<le> length (snd (snd (c!0)))"

lemma all_same_length_state_program_par_step:
  assumes a0:"(\<Gamma>\<turnstile>\<^sub>p cfg0  \<rightarrow> cfg1) \<or> (\<Gamma>\<turnstile>\<^sub>p cfg0  \<rightarrow>\<^sub>e cfg1)" and
      a1:"length (fst cfg0) \<le> length (snd (snd cfg0))" 
    shows "length (fst cfg1) \<le> length (snd (snd cfg1))"
  using a0 a1
  by (smt fst_conv length_list_update prod.exhaust_sel step_p_pair_elim_cases 
             step_pe_elim_cases swap_simp)


lemma all_same_length_state_program:"(\<Gamma>,c)\<in> par_cptn \<Longrightarrow> same_length_state_program c \<Longrightarrow>  
       i<length c \<Longrightarrow>  
       length (fst (c!i)) \<le> length (snd (snd (c!i)))"
proof(induct i)
  case 0
  then show ?case unfolding same_length_state_program_def by fastforce
next
  case (Suc i)
  then have "i<length c -1" by auto
  moreover obtain c' c'' where    "c = c'@([c!i,c!Suc i])@c''" using sublist calculation
    by (metis Suc_eq_plus1)
  ultimately show ?case
    by (metis Suc(2) Suc(3) Suc(4) Suc.hyps Suc_eq_plus1 Suc_lessD  
       all_same_length_state_program_par_step par_cptn_step_ce)  
qed
  
  
  
definition conjoin :: "('g,'l,'p,'f,'e) par_confs \<Rightarrow> (('g,'l,'p,'f,'e) gconfs) list \<Rightarrow> bool"  ("_ \<propto> _" [65,65] 64) where
  "c \<propto> clist \<equiv> (same_length c clist) \<and> (same_state c clist) \<and> (same_program c clist) \<and> 
                (compat_label c clist) \<and> (same_functions c clist) \<and> same_length_state_program (snd c)"


lemma conjoin_same_length: 
   "c \<propto> clist \<Longrightarrow> \<forall>i < length (snd c). length (fst ((snd c)!i)) =  length clist"
proof (auto)
  fix i
  assume a1:"c \<propto> clist"
  assume a2:"i < length (snd c)"
  then have "(\<forall>j<length (snd c). fst((snd c)!j) = map (\<lambda>x. fst(nth (snd x) j)) clist)"
    using a1 unfolding conjoin_def same_program_def by auto
  thus "length (fst (snd c ! i)) = length clist" by (simp add: a2)
qed

lemma no_idea:"c \<propto> clist \<Longrightarrow>
       i< length (snd c) \<and> j < length (snd c) \<Longrightarrow>  
       length (fst ((snd c)!i)) = length (fst ((snd c)!j))"
using conjoin_same_length by fastforce

lemma conjoin_same_length_i_suci:"c \<propto> clist \<Longrightarrow>
       Suc i< length (snd c) \<Longrightarrow>
       length (fst ((snd c)!i)) = length (fst ((snd c)!(Suc i)))"
using conjoin_same_length by fastforce

lemma conjoin_same_program_i:
  "c \<propto> clist \<Longrightarrow>
   j < length (snd c) \<Longrightarrow>
   i < length clist \<Longrightarrow>
   fst ((snd (clist!i))!j) = (fst ((snd c)!j))!i"
proof -
  assume a0:"c \<propto> clist" and
         a1:"j < length (snd c)" and
         a2:"i < length clist"
  have "length (fst ((snd c)!j)) = length clist"
    using conjoin_same_length a0 a1 by fastforce
  also have "fst (snd c ! j) = map (\<lambda>x. fst (snd x ! j)) clist"
    using a0 a1 unfolding conjoin_def same_program_def by fastforce
  ultimately show ?thesis using a2 by fastforce
qed

lemma conjoin_same_program_i_j:
  "c \<propto> clist \<Longrightarrow>
   Suc j < length (snd c) \<Longrightarrow>
   \<forall>l< length clist. fst ((snd (clist!l))!j) = fst ((snd (clist!l))!(Suc j)) \<Longrightarrow>
   fst ((snd c)!j) = (fst ((snd c)!(Suc j)))"
proof -
  assume a0:"c \<propto> clist" and
         a1:"Suc j < length (snd c)" and
         a2:"\<forall>l< length clist. fst ((snd (clist!l))!j) = fst ((snd (clist!l))!(Suc j))"
  have "length (fst ((snd c)!j)) = length clist"
    using conjoin_same_length a0 a1 by fastforce
  then have "map (\<lambda>x. fst (snd x ! j)) clist = map (\<lambda>x. fst (snd x ! (Suc j))) clist"
    using a2 by (metis (no_types, lifting) in_set_conv_nth map_eq_conv) 
  moreover have "fst (snd c ! j) = map (\<lambda>x. fst (snd x ! j)) clist"
    using a0 a1 unfolding conjoin_def same_program_def by fastforce
  moreover have "fst (snd c ! Suc j) = map (\<lambda>x. fst (snd x ! Suc j)) clist"
    using a0 a1 unfolding conjoin_def same_program_def by fastforce
  ultimately show ?thesis by fastforce
qed

lemma conjoin_last_same_state:
  assumes a0: "(\<Gamma>,l)\<propto> clist" and
   a1: "i < length clist" and
   a2: "(snd (clist!i))\<noteq>[]"
   shows "snd (last (snd (clist!i))) = snd (last l)"
proof -
  have "length l = length (snd (clist!i))" 
    using a0 a1 unfolding conjoin_def same_length_def by fastforce
  also then have length_l:"length l \<noteq>0" using a2 by fastforce
  ultimately have "last (snd (clist!i)) = (snd (clist!i))!((length l)-1)" 
    using a1 a2 
    by (simp add: last_conv_nth)
  thus ?thesis using length_l a0 a1 unfolding conjoin_def same_state_def
    by (simp add:  a2 last_conv_nth )      
qed



lemma conjoin_tl: 
  assumes 
    a1: "(\<Gamma>,x#xs) \<propto> ys" and
    a2:"zs = map (\<lambda>i. (fst i, tl (snd i))) ys"    
   shows "(\<Gamma>,xs) \<propto> zs"
proof -
  have s_p:"same_program (\<Gamma>,x#xs) ys" using a1 unfolding conjoin_def by simp
  have s_l:"same_length (\<Gamma>,x#xs) ys" using a1 unfolding conjoin_def by simp
  have "\<forall>i<length zs. snd (zs!i) = tl (snd (ys!i))"
    by (simp add: a2)   
  { 
     { assume "xs = []" then have "same_length_state_program xs" 
         unfolding same_length_state_program_def by auto
     }
     moreover { assume a00:"xs \<noteq>[]"
       then obtain x' xs' where xs:"xs = x'#xs'"
         using list.exhaust_sel by blast
       then have "(\<Gamma>\<turnstile>\<^sub>p x  \<rightarrow> x') \<or> (\<Gamma>\<turnstile>\<^sub>p x  \<rightarrow>\<^sub>e x')"
         using a1 compat_label_tran_0 conjoin_def by fastforce
       moreover have "length (fst x) \<le> length (snd (snd x))"
          using a1 unfolding same_length_state_program_def  conjoin_def by auto
        ultimately have "length (fst x') \<le> length (snd (snd x'))" 
         using all_same_length_state_program_par_step
         by blast 
       then have "same_length_state_program xs" using xs
         by (simp add:  same_length_state_program_def)     
     } ultimately have "same_length_state_program xs" by auto
   } moreover note same_state_program = this
  {
    have "same_length (\<Gamma>,xs) zs" using a1 a2 unfolding conjoin_def 
     by (simp add: same_length_def)
  } moreover note same_len = this
  {    
    {
       fix j
       assume a11:"j<length (snd (\<Gamma>, xs))"                                                               
       then have fst_suc:"fst (snd (\<Gamma>, xs) ! j) = fst(snd (\<Gamma>,x#xs)! Suc j)"
         by auto       
       then have "fst (snd (\<Gamma>, xs) ! j) = map (\<lambda>x. fst (snd x ! j)) zs" 
       proof -
         have s_l_y_z:"length ys = length zs" using a2 by fastforce
         have Suc_j_l_ys:"\<forall>i < length ys. Suc j < length (snd (ys!i))" 
           using a11 s_l unfolding same_length_def by fastforce
         have tail: "\<forall>i < length ys. snd (zs!i) = tl (snd (ys!i))" using a2 
           by fastforce                  
         then have l_xs_zs_eq:"length (fst (snd (\<Gamma>, xs) ! j)) = length zs"
            using fst_suc s_l_y_z s_p a11 unfolding same_program_def by auto         
         then have "\<forall>i<length ys. 
           fst (snd (\<Gamma>, x#xs) ! Suc j)!i = fst (snd (ys!i) ! (Suc j))"
             using s_p a11 unfolding same_program_def by fastforce
         then have "\<forall>i<length zs. 
           fst (snd (\<Gamma>, x#xs) ! Suc j)!i = fst (snd (zs!i) ! (j))"
           using Suc_j_l_ys tail s_l_y_z tl_zero_pair by metis
        then have "\<forall>i<length zs. 
           fst (snd (\<Gamma>, xs) ! j)!i = map (\<lambda>x. fst (snd x !  j)) zs!i"
          using fst_suc by auto
        also have "length (fst (snd (\<Gamma>, xs) ! j)) = 
                   length (map (\<lambda>x. fst (snd x !  j)) zs) " 
          using l_xs_zs_eq by auto
        ultimately show ?thesis using  l_xs_zs_eq list_eq by metis
       qed                 
    }
    then have "same_program  (\<Gamma>,xs) zs"
    unfolding conjoin_def  same_program_def same_length_def     
    by blast    
  }moreover note same_prog = this
  {
    have "same_state  (\<Gamma>,xs) zs" 
    using a1 a2 unfolding conjoin_def same_length_def same_state_def
    apply auto
    by (metis (no_types, hide_lams) List.nth_tl Suc_less_eq diff_Suc_1 length_tl nth_Cons_Suc)    
  }moreover note same_sta = this
  {
    have "same_functions  (\<Gamma>,xs) zs" 
     using a1 a2 unfolding conjoin_def
     apply auto
     apply (simp add: same_functions_def)          
     done
  }moreover note same_fun = this
  { {
      fix j
      assume a11:"Suc j<length (snd (\<Gamma>, xs))"
      have s_l_y_z:"length ys = length zs" using a2 by fastforce
      have Suc_j_l_ys:"\<forall>i < length ys. Suc (Suc j) < length (snd (ys!i))" 
        using a11 s_l unfolding same_length_def by fastforce
      have tail: "\<forall>i < length ys. snd (zs!i) = tl (snd (ys!i))" using a2 
        by fastforce    
      have same_env: "\<forall>i < length ys. (fst (ys!i)) = \<Gamma>"
        using a1 unfolding conjoin_def same_functions_def by auto
      have fst: "\<forall>x. fst(\<Gamma>, x) = \<Gamma>" by auto
      then have fun_ys_eq_fun_zs: "\<forall>i < length ys. (fst (ys!i)) = (fst (zs!i))"
        using same_env s_l_y_z
        
      proof -          
        have "\<forall>n. \<not> n < length ys \<or> fst (zs ! n) = fst (ys ! n)"            
          by (simp add: a2)
        thus ?thesis by presburger        
      qed                
      have suc_j:"Suc (Suc j) < length (snd (\<Gamma>, x#xs))" using a11 by auto
      note t=a1[simplified conjoin_def compat_label_def fst Let_def split_beta ]
      then have or_compat:
      "\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow> (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (\<exists>i<length ys.
              fst (ys ! i)\<turnstile>\<^sub>c (fst (snd (ys ! i) ! (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! (Suc j))))) \<rightarrow>
                       (fst (snd (ys ! i) ! Suc (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! Suc (Suc j))))) \<and>
                 (\<forall>l<length ys.
                     l \<noteq> i \<longrightarrow>
                     fst (ys ! l)\<turnstile>\<^sub>c (fst (snd (ys ! l) ! (Suc j)), toSeqState l (snd (snd (ys ! l) ! (Suc j)))) \<rightarrow>\<^sub>e
                           (fst (snd (ys ! l) ! Suc (Suc j)), toSeqState l (snd (snd (ys ! l) ! Suc (Suc j)))))) \<or>
             \<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow>\<^sub>e (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (\<forall>i<length ys.
                 fst (ys ! i)\<turnstile>\<^sub>c (fst (snd (ys ! i) ! (Suc j)), toSeqState i (snd (snd (ys ! i) ! (Suc j)))) \<rightarrow>\<^sub>e
                       (fst (snd (ys ! i) ! Suc (Suc j)), toSeqState i (snd (snd (ys ! i) ! Suc (Suc j)))))"       
        using suc_j by auto
      then have 
      "fst (\<Gamma>,xs)\<turnstile>\<^sub>p snd (\<Gamma>, xs) ! j \<rightarrow> (snd (\<Gamma>, xs) ! Suc j) \<and>
             (\<exists>i<length zs.
                  fst (zs ! i)\<turnstile>\<^sub>c (fst (snd (zs ! i) ! j), toSeq (toSeqState i (snd (snd (zs ! i) ! j)))) \<rightarrow>
                       (fst (snd (zs ! i) ! Suc j), toSeq (toSeqState i (snd (snd (zs ! i) ! Suc j))))  \<and>
                 (\<forall>l<length zs.
                     l \<noteq> i \<longrightarrow>
                     fst (zs ! l)\<turnstile>\<^sub>c (fst (snd (zs ! l) ! j), toSeqState l (snd (snd (zs ! l) ! j))) \<rightarrow>\<^sub>e
                           (fst (snd (zs ! l) ! Suc j), toSeqState l (snd (snd (zs ! l) ! Suc j))))) \<or>
             \<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, xs) ! j \<rightarrow>\<^sub>e (snd (\<Gamma>, xs) ! Suc j) \<and>
             (\<forall>i<length zs.
                 fst (zs ! i)\<turnstile>\<^sub>c (fst (snd (zs ! i) ! j), toSeqState i (snd (snd (zs ! i) ! j))) \<rightarrow>\<^sub>e
                       (fst (snd (zs ! i) ! Suc j), toSeqState i (snd (snd (zs ! i) ! Suc j))))"       

      proof
        assume a21:
        "\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow> (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (\<exists>i<length ys.
              fst (ys ! i)\<turnstile>\<^sub>c (fst (snd (ys ! i) ! (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! (Suc j))))) \<rightarrow>
                       (fst (snd (ys ! i) ! Suc (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! Suc (Suc j))))) \<and>
                 (\<forall>l<length ys.
                     l \<noteq> i \<longrightarrow>
                     fst (ys ! l)\<turnstile>\<^sub>c (fst (snd (ys ! l) ! (Suc j)), toSeqState l (snd (snd (ys ! l) ! (Suc j)))) \<rightarrow>\<^sub>e
                           (fst (snd (ys ! l) ! Suc (Suc j)), toSeqState l (snd (snd (ys ! l) ! Suc (Suc j))))))"
        then obtain i where   
        f1:"\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow> (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (i<length ys \<and>
              fst (ys ! i)\<turnstile>\<^sub>c (fst (snd (ys ! i) ! (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! (Suc j))))) \<rightarrow>
                       (fst (snd (ys ! i) ! Suc (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! Suc (Suc j))))) \<and>
                 (\<forall>l<length ys.
                     l \<noteq> i \<longrightarrow>
                     fst (ys ! l)\<turnstile>\<^sub>c (fst (snd (ys ! l) ! (Suc j)), toSeqState l (snd (snd (ys ! l) ! (Suc j)))) \<rightarrow>\<^sub>e
                           (fst (snd (ys ! l) ! Suc (Suc j)), toSeqState l (snd (snd (ys ! l) ! Suc (Suc j))))))" 
          by auto
        then have "fst (\<Gamma>,xs)\<turnstile>\<^sub>p snd (\<Gamma>, xs) ! j \<rightarrow> (snd (\<Gamma>, xs) ! Suc j) \<and>
             (\<exists>i<length zs.
                  fst (zs ! i)\<turnstile>\<^sub>c (fst (snd (zs ! i) ! j), toSeq (toSeqState i (snd (snd (zs ! i) ! j)))) \<rightarrow>
                       (fst (snd (zs ! i) ! Suc j), toSeq (toSeqState i (snd (snd (zs ! i) ! Suc j))))  \<and>
                 (\<forall>l<length zs.
                     l \<noteq> i \<longrightarrow>
                     fst (zs ! l)\<turnstile>\<^sub>c (fst (snd (zs ! l) ! j), toSeqState l (snd (snd (zs ! l) ! j))) \<rightarrow>\<^sub>e
                           (fst (snd (zs ! l) ! Suc j), toSeqState l (snd (snd (zs ! l) ! Suc j)))))"        
        proof-
          have f1:"\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow> (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (i<length ys \<and>
              fst (ys ! i)\<turnstile>\<^sub>c (fst (snd (ys ! i) ! (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! (Suc j))))) \<rightarrow>
                       (fst (snd (ys ! i) ! Suc (Suc j)), toSeq (toSeqState i (snd (snd (ys ! i) ! Suc (Suc j))))) \<and> 
                       (\<forall>l. (\<not> l < length ys \<or> l = i) \<or> 
                           fst (ys ! l)\<turnstile>\<^sub>c (fst (snd (ys ! l) ! (Suc j)), toSeqState l (snd (snd (ys ! l) ! (Suc j)))) \<rightarrow>\<^sub>e
                           (fst (snd (ys ! l) ! Suc (Suc j)), toSeqState l (snd (snd (ys ! l) ! Suc (Suc j))))))"            
            using f1 by blast
          have f2: "j < length (snd (\<Gamma>, xs))"
            by (meson Suc_lessD a11)          
          then have f3: "\<forall>n. \<not> n < length zs \<or> length (snd (zs ! n)) = length (snd (\<Gamma>, xs))"
            using same_len same_length_def
            by (simp add: same_length_def)          
          have "\<forall>n. \<not> n < length ys \<or> snd (zs ! n) = tl (snd (ys ! n))"
            using tail by blast                                 
          thus ?thesis using f3 f2 f1 List.nth_tl a11 s_l_y_z 
            Suc_j_l_ys  Suc_lessD nth_map fun_ys_eq_fun_zs 
            by (smt fst_conv fun_ys_eq_fun_zs nth_Cons_Suc snd_conv) 
        qed
        then show ?thesis by auto
      next
        assume a22:"\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow>\<^sub>e (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (\<forall>i<length ys.
                 fst (ys ! i)\<turnstile>\<^sub>c (fst (snd (ys ! i) ! (Suc j)), toSeqState i (snd (snd (ys ! i) ! (Suc j)))) \<rightarrow>\<^sub>e
                       (fst (snd (ys ! i) ! Suc (Suc j)), toSeqState i (snd (snd (ys ! i) ! Suc (Suc j)))))"        
        then have "\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow>\<^sub>e (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (\<forall>i<length ys.
                 fst (ys ! i)\<turnstile>\<^sub>c (fst (snd (zs ! i) ! j), toSeqState i (snd (snd (zs ! i) ! j))) \<rightarrow>\<^sub>e
                       (fst (snd (zs ! i) ! Suc j), toSeqState i (snd (snd (zs ! i) ! Suc j))))"
          using Suc_j_l_ys tail s_l_y_z  a11 same_len unfolding same_length_def        
          by (metis (no_types, hide_lams) List.nth_tl Suc_lessD)
        then have  "\<Gamma>\<turnstile>\<^sub>p snd (\<Gamma>, x # xs) ! (Suc j) \<rightarrow>\<^sub>e (snd (\<Gamma>, x # xs) ! Suc (Suc j)) \<and>
             (\<forall>i<length zs.
                 fst (zs ! i)\<turnstile>\<^sub>c (fst (snd (zs ! i) ! j), toSeqState i (snd (snd (zs ! i) ! j))) \<rightarrow>\<^sub>e
                       (fst (snd (zs ! i) ! Suc j), toSeqState i (snd (snd (zs ! i) ! Suc j))))"
        using same_env s_l_y_z fun_ys_eq_fun_zs  by fastforce
        then show ?thesis by auto
      qed             
    }
    then have "compat_label  (\<Gamma>,xs) zs"
      unfolding compat_label_def Let_def split_beta by auto 
  } note same_label = this
  ultimately show ?thesis using conjoin_def by fastforce
qed


lemma clist_snd:
 assumes a1: "(\<Gamma>, a # ys) \<propto> map (\<lambda>x. (fst x, tl (snd x)))
                    (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist))" and
         a2: "length clist > 0 \<and> length clist = length xs"
 shows "clist = (map snd
          (map (\<lambda>x. (\<Gamma>, (fst x, snd (clist ! 0 ! 0)) # snd x))
            (zip (map (\<lambda>x. fst (hd x)) clist) (map tl clist))))"
proof -
     let ?concat_zip = "(\<lambda>i. (\<Gamma>, (fst i, s) # snd i))"  
     let ?clist_ext = "map ?concat_zip (zip xs clist)"
     let ?exec_run = "(xs, s) # a # ys"
     let ?exec = "(\<Gamma>,?exec_run)"
     let ?exec_ext = "map (\<lambda>x. (fst x, tl (snd x))) ?clist_ext"
     let ?zip = "(zip (map (\<lambda>x. fst (hd x)) clist) 
                         (map (\<lambda>x. tl x) clist))"
  have \<Gamma>_all: "\<forall>i < length ?clist_ext. fst (?clist_ext !i) = \<Gamma>"
       by auto       
  have len:"length xs = length clist" using a2 by auto
  then have len_clist_exec:
   "length clist = length ?exec_ext" 
   by fastforce    
  then have len_clist_exec_map:
    "length ?exec_ext = 
              length (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)" 
   by fastforce               
  then have clist_snd:"clist = map (\<lambda>x. snd x) ?exec_ext"
    using clist_map1 [of xs clist \<Gamma> s] clist_map2 len by blast   
  then have clist_len_eq_ays: 
      "\<forall>i < length clist. length( (clist!i))=length (snd (\<Gamma>,a#ys))"      
    using len  same_length_non_pair a1 conjoin_def
    by blast
  then have clist_gz:"\<forall>i < length clist. length (clist!i) > 0" 
    by fastforce
  have clist_len_eq: 
     "\<forall>i < length clist. \<forall>j < length clist. 
        length (clist ! i) = length (clist ! j)" 
    using clist_len_eq_ays by auto          
  have clist_same_state: 
    "\<forall>i < length clist. \<forall>j< length clist. \<forall>k<length  (clist!i).
       snd ((clist!i)!k) = snd ((clist!j)!k)"
  proof -
    have 
      "(\<forall>i <length clist. \<forall>j<length (snd (\<Gamma>, a # ys)). snd((snd (\<Gamma>, a # ys))!j) = snd( (clist!i)!j))"
      using len clist_snd conjoin_def a1 conjoin_def same_state_non_pair 
    by blast
    thus ?thesis using clist_len_eq_ays by (metis (no_types))
  qed      
  then have clist_map:
    "clist = map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ?zip"
    using list_as_map a2 clist_gz clist_len_eq by blast      
  moreover have "map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ?zip =
             map snd (map (\<lambda>x. (\<Gamma>, (fst x, snd (clist ! 0 ! 0)) # snd x))
       (zip (map (\<lambda>x. fst (hd x)) clist) (map tl clist)))"
  using map_snd' by auto
  ultimately show ?thesis by auto   
qed

lemma list_as_zip:
 assumes a1: "(\<Gamma>, a # ys) \<propto> map (\<lambda>x. (fst x, tl (snd x)))
                    (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist))" and
         a2: "length clist > 0 \<and> length clist = length xs"
 shows "  map (\<lambda>x. (fst x, tl (snd x)))
                    (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist)) =
          map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                       (zip (map (\<lambda>x. fst (hd x)) clist) 
                         (map (\<lambda>x. tl x) clist))"
proof -
     let ?concat_zip = "(\<lambda>i. (\<Gamma>, (fst i, s) # snd i))"  
     let ?clist_ext = "map ?concat_zip (zip xs clist)"
     let ?exec_run = "(xs, s) # a # ys"
     let ?exec = "(\<Gamma>,?exec_run)"
     let ?exec_ext = "map (\<lambda>x. (fst x, tl (snd x))) ?clist_ext"
     let ?zip = "(zip (map (\<lambda>x. fst (hd x)) clist) 
                         (map (\<lambda>x. tl x) clist))"
  have \<Gamma>_all: "\<forall>i < length ?clist_ext. fst (?clist_ext !i) = \<Gamma>"
       by auto       
  have len:"length xs = length clist" using a2 by auto
  then have len_clist_exec:
   "length clist = length ?exec_ext" 
   by fastforce    
  then have len_clist_exec_map:
    "length ?exec_ext = 
              length (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)" 
   by fastforce               
  then have clist_snd:"clist = map (\<lambda>x. snd x) ?exec_ext"
    using clist_map1 [of xs clist \<Gamma> s] clist_map2 len by blast   
  then have clist_len_eq_ays: 
      "\<forall>i < length clist. length( (clist!i))=length (snd (\<Gamma>,a#ys))"      
    using len  same_length_non_pair a1 conjoin_def
    by blast
  then have clist_gz:"\<forall>i < length clist. length (clist!i) > 0" 
    by fastforce
  have clist_len_eq: 
     "\<forall>i < length clist. \<forall>j < length clist. 
        length (clist ! i) = length (clist ! j)" 
    using clist_len_eq_ays by auto          
  have clist_same_state: 
    "\<forall>i < length clist. \<forall>j< length clist. \<forall>k<length  (clist!i).
       snd ((clist!i)!k) = snd ((clist!j)!k)"
  proof -
    have 
      "(\<forall>i <length clist. \<forall>j<length (snd (\<Gamma>, a # ys)). snd((snd (\<Gamma>, a # ys))!j) = snd( (clist!i)!j))"
      using len clist_snd conjoin_def a1 conjoin_def same_state_non_pair 
    by blast
    thus ?thesis using clist_len_eq_ays by (metis (no_types))
  qed      
  then have clist_map:
    "clist = map (\<lambda>i. (fst i,snd ((clist!0)!0))#snd i) ?zip"
    using list_as_map a2 clist_gz clist_len_eq by blast      
  then have "\<forall>i < length clist. 
                clist ! i = (fst (?zip!i),snd ((clist!0)!0)) # snd (?zip!i)"
  using len nth_map length_map by (metis (no_types, lifting))
  then have 
    "\<forall>i < length clist. 
     ?exec_ext ! i = (\<Gamma>, (fst (?zip!i),snd ((clist!0)!0)) # snd (?zip!i))" 
  using \<Gamma>_all len  by fastforce           
  moreover have "\<forall>i < length clist. 
    (\<Gamma>, (fst (?zip!i),snd ((clist!0)!0)) # snd (?zip!i)) = 
    (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)!i" 
  by auto        
  ultimately have 
     "\<forall>i < length clist. 
       ?exec_ext ! i =(map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)!i" 
  by auto
  then also have "length clist = length ?exec_ext" 
  using len by fastforce 
  ultimately have exec_ext_eq_clist_map:
     "\<forall>i < length ?exec_ext. 
       ?exec_ext ! i =(map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)!i" 
  by presburger
  then moreover have "length ?exec_ext = 
              length (map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) 
                          ?zip)" 
  using len clist_map by fastforce    
  ultimately show ?thesis
     using list_eq by blast  
 qed

  

lemma clist_map_zip:"xs\<noteq>[] \<Longrightarrow> (\<Gamma>,(xs,s)#ys) \<propto> clist \<Longrightarrow> 
      clist = map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist))"
proof -
  let ?clist = "map snd clist"
  assume a1: "xs\<noteq>[]"
  assume a2:  "(\<Gamma>,(xs,s)#ys) \<propto> clist"
  then have all_in_clist_not_empty:"\<forall>i < length ?clist. (?clist!i) \<noteq> []"
   unfolding conjoin_def same_length_def by auto
  then have hd_clist:"\<forall>i < length ?clist. hd (?clist!i) = (?clist!i)!0" 
     by (simp add: hd_conv_nth)  
  then have all_xs:"\<forall>i< length ?clist. fst (hd (?clist!i)) = xs!i"
   using  a2 unfolding conjoin_def same_program_def by auto
  
  then have  all_s: "\<forall>i < length ?clist. snd (hd (?clist!i)) = s"
    using a2 hd_clist unfolding conjoin_def same_state_def by fastforce
  have fst_clist_\<Gamma>:"\<forall>i < length clist. fst (clist!i) = \<Gamma>"
    using a2 unfolding conjoin_def same_functions_def by auto 
   have p2:"length xs = length clist" using conjoin_same_length a2
   by fastforce   
  then have "\<forall>i< length (map (\<lambda>x. fst (hd x)) ?clist). 
               (map (\<lambda>x. fst (hd x)) ?clist)!i = xs!i"
    using all_xs by auto
  also have "length (map (\<lambda>x. fst (hd x)) ?clist) = length xs" using p2 by auto
  ultimately have "(map (\<lambda>x. fst (hd x)) ?clist) = xs"
   using nth_equalityI by metis
  then have xs_clist:"map (\<lambda>x. fst (hd (snd x))) clist = xs" by auto
       
  have clist_hd_tl:"\<forall>i < length ?clist. ?clist!i = hd (?clist!i) # (tl (?clist!i))"
   using all_in_clist_not_empty list.exhaust_sel by blast   
  then have "\<forall>i < length ?clist. ?clist!i =(fst  (hd (?clist!i)),snd  (hd (?clist!i)))# (tl (?clist!i))"
    by auto
  then have "?clist = map (\<lambda>x. (fst (hd x),snd (hd x))#tl x) ?clist" 
   using length_map list_eq_iff_nth_eq list_update_id map_update nth_list_update_eq
   by (metis (no_types, lifting) length_map list_eq_iff_nth_eq list_update_id map_update nth_list_update_eq)
  then have "?clist = map (\<lambda>x. (fst (hd x),s)#tl x) ?clist"
   using all_s length_map nth_equalityI nth_map
    by (metis (no_types, lifting) ) 
  then have map_clist:"map (\<lambda>x. (fst (hd (snd x)),s)#tl (snd x)) clist = ?clist" 
   by auto   
  then have "(map (\<lambda>x. (fst x, s)#snd x) 
               (zip (map (\<lambda>x. fst (hd (snd x))) clist) 
                    (map (\<lambda>x. tl (snd x)) clist))) =  ?clist"     
    using map_clist  by (auto intro: nth_equalityI) 
  then have "\<forall>i<length clist. clist!i =  (\<Gamma>,(map (\<lambda>x. (fst x, s)#snd x) 
               (zip xs 
                   (map (\<lambda>x. tl (snd x)) clist)))!i)" 
   using  xs_clist fst_clist_\<Gamma>  by auto   
  also have "length clist = length (map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist)))" 
    using p2 by auto
  ultimately show "clist = map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist))" 
    using length_map length_zip nth_equalityI nth_map 
    by (metis (no_types, lifting)) 
qed
            
lemma aux_if' : 
  assumes a:"length clist > 0 \<and> length clist = length xs \<and> 
             (\<forall>i<length xs. (i,\<Gamma>,(xs!i,s)#clist!i) \<in> cptni) \<and> 
             ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
  shows "(\<Gamma>,(xs, s)#ys) \<in> par_cptn"                            
using a
proof (induct ys arbitrary: xs s clist) 
  case Nil then show ?case by (simp add: par_cptn.ParCptnOne)
next
  case (Cons a ys xs s clist)     
     let ?concat_zip = "(\<lambda>i. (\<Gamma>, (fst i, s) # snd i))"  
     let ?com_clist_xs = "map ?concat_zip (zip xs clist)"
     let ?xs_a_ys_run = "(xs, s) # a # ys"
     let ?xs_a_ys_run_exec = "(\<Gamma>,?xs_a_ys_run)"
     let ?com_clist' = "map (\<lambda>x. (fst x, tl (snd x))) ?com_clist_xs"
     let ?xs' = "(map (\<lambda>x. fst (hd x)) clist)"     
     let ?clist' = "(map (\<lambda>x. tl x) clist)"
     let ?zip_xs'_clist' = "zip ?xs' 
                            ?clist'"         
     obtain as sa where a_pair:"a=(as,sa)"
       by (meson prod.exhaust_sel)
       let ?comp_clist'_alt = "map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) ?zip_xs'_clist' "
       let ?clist'_alt = "map (\<lambda>x. snd x) ?comp_clist'_alt"
       let ?comp_a_ys = "(\<Gamma>, (as,sa) # ys)"   
     have conjoin_hyp1:
       "(\<Gamma>, (as,sa) # ys) \<propto> ?com_clist'"
       using conjoin_tl using a_pair Cons by blast     
     then have conjoin_hyp:
       "(\<Gamma>, (as,sa) # ys) \<propto> map (\<lambda>x. (\<Gamma>, (fst x,snd ((clist!0)!0))#snd x)) ?zip_xs'_clist'"
     using list_as_zip Cons.prems
     proof -
       have "map (\<lambda>p. (fst p, tl (snd p))) (map (\<lambda>p. (\<Gamma>, (fst p, s) # snd p)) (zip xs clist)) = 
               map (\<lambda>p. (\<Gamma>, (fst p, snd (clist ! 0 ! 0)) # snd p)) (zip (map (\<lambda>ps. fst (hd ps)) clist) 
                     (map tl clist))"
         using Cons.prems conjoin_hyp1 list_as_zip by blast
       then show ?thesis
         using conjoin_hyp1 by presburger
     qed     
     have len:"length xs = length clist" using Cons by auto 
     have clist_snd_map:
        "(map snd
          (map (\<lambda>x. (\<Gamma>, (fst x, snd (clist ! 0 ! 0)) # snd x))
         (zip (map (\<lambda>x. fst (hd x)) clist) (map tl clist)))) = clist"
       using clist_snd Cons.prems conjoin_hyp1
     proof -
       have "\<not> 0 < length clist \<or> length clist \<noteq> length xs \<or> 
            map snd (map (\<lambda>p. (\<Gamma>, (fst p, snd (clist ! 0 ! 0)) # snd p)) 
                      (zip (map (\<lambda>ps. fst (hd ps)) clist) (map tl clist))) = clist"
         using clist_snd conjoin_hyp1 by fastforce
       then show ?thesis
         using Cons.prems by linarith
     qed
     have eq_len_clist_clist':
       "length ?clist' > 0" using Cons.prems by auto  
     have "(\<forall>i <length clist. \<forall>j<length (snd ?comp_a_ys). snd((snd ?comp_a_ys)!j) = snd( (clist!i)!j))"
        using clist_snd_map conjoin_hyp conjoin_def same_state_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
         by fastforce   
     then have "\<forall>i<length clist.
                  sa = snd ( (clist ! i)!0)" by fastforce
     also have clist_i_grz:"(\<forall>i <length clist. length( (clist!i)) > 0)"
         using clist_snd_map conjoin_hyp conjoin_def same_length_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
     by fastforce  
     ultimately have all_i_sa_hd_clist:"\<forall>i<length clist.
                  sa = snd (hd (clist ! i))"
     by (simp add: hd_conv_nth)      
     have as_sa_eq_xs'_s':"as = ?xs' \<and>  sa = snd ((clist!0)!0)" 
     proof -              
       have "(\<forall>j<length (snd ?comp_a_ys). fst((snd ?comp_a_ys)!j) = 
                map (\<lambda>x. fst(nth x j)) ?clist'_alt)"       
       using conjoin_hyp conjoin_def same_program_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
       by fast
       then have are_eq:"fst((snd ?comp_a_ys)!0) = 
                map (\<lambda>x. fst(nth x 0)) ?clist'_alt" by fastforce
       have fst_exec_is_as:"fst((snd ?comp_a_ys)!0) =as" by auto              
       then have "map (\<lambda>x. fst(hd x)) clist=map (\<lambda>x. fst(x!0)) clist"
         using map_hd_nth clist_i_grz by auto 
       then have "map (\<lambda>x. fst(nth x 0)) ?clist'_alt =?xs'" using clist_snd_map map_hd_nth
        by fastforce
       moreover have "(\<forall>i <length clist. \<forall>j<length (snd ?comp_a_ys). snd((snd ?comp_a_ys)!j) = snd( (clist!i)!j))"
        using clist_snd_map conjoin_hyp conjoin_def same_state_non_pair[of ?comp_a_ys ?comp_clist'_alt ?clist'_alt]
         by fastforce
       ultimately show ?thesis using are_eq fst_exec_is_as
          using Cons.prems by force 
    qed
    then have conjoin_hyp:
       "(\<Gamma>, (as,sa) # ys) \<propto> map (\<lambda>x. (\<Gamma>, (fst x,sa)#snd x))
                            (zip as (map tl clist))"
    using conjoin_hyp by auto
    then have eq_len_as_clist':
       "length as = length ?clist'" using Cons.prems as_sa_eq_xs'_s' by auto
    then have len_as_ys_eq:"length as = length xs" using Cons.prems by auto
    have " (\<forall>i<length as. (i,\<Gamma>, ((as!i),sa)#(map (\<lambda>x. tl x) clist)!i) \<in> cptni)" 
     using Cons.prems cptn_dest clist_snd_map len 
    proof -     
      have "\<forall>i<length clist. clist!i = (hd (clist!i))#(tl (clist!i))" 
       using clist_i_grz 
      by auto
      then have "(\<forall>i<length clist. (i,\<Gamma>, (xs ! i, s) # (hd (clist!i))#(tl (clist!i))) \<in> cptni)"
      using Cons.prems by auto
      then have f1:"(\<forall>i<length clist. (i,\<Gamma>, (hd (clist!i))#(tl (clist!i))) \<in> cptni)"
      by (metis list.distinct(2) tl_in_cptni) 
      then have "(\<forall>i<length clist. (i,\<Gamma>, ((as!i),sa)#(tl (clist!i))) \<in> cptni)"
      using as_sa_eq_xs'_s' all_i_sa_hd_clist by auto      
      then have "(\<forall>i<length clist. (i,\<Gamma>, ((as!i),sa)#(map (\<lambda>x. tl x) clist)!i) \<in> cptni)"
      by auto
      thus ?thesis using  len clist_i_grz len_as_ys_eq by auto
   qed
   then have a_ys_par_cptn:"(\<Gamma>, (as, sa) # ys) \<in> par_cptn"           
   using 
    conjoin_hyp eq_len_clist_clist' eq_len_as_clist'[THEN sym] Cons.hyps
   by blast  
   have \<Gamma>_all: "\<forall>i < length ?com_clist_xs. fst (?com_clist_xs !i) = \<Gamma>"
   by auto
   have Gamma: "\<Gamma>= (fst ?xs_a_ys_run_exec)" by fastforce  
   have exec: "?xs_a_ys_run = (snd ?xs_a_ys_run_exec)" by fastforce  
   have split_par:
       "\<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow> ((a # ys) ! 0) \<or>
        \<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow>\<^sub>e ((a # ys) ! 0)"     
       using compat_label_def compat_label_tran_0
             Cons.prems Gamma exec 
             compat_label_tran_0[of "(\<Gamma>, (xs, s) # a # ys)" 
                                   "(map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist))"]    
       unfolding conjoin_def by auto      
     {
      assume "\<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow> ((a # ys) ! 0)"      
      then have  " (\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" 
      using a_ys_par_cptn a_pair par_cptn.ParCptnComp by fastforce
     } note env_sol=this
     {
      assume " \<Gamma>\<turnstile>\<^sub>p ((xs, s) # a # ys) ! 0 \<rightarrow>\<^sub>e ((a # ys) ! 0)"      
      then have env_tran:" \<Gamma>\<turnstile>\<^sub>p (xs, s)  \<rightarrow>\<^sub>e (as,sa)" using a_pair by auto
      have "xs = as"
       by (meson env_pe_c_c'_false env_tran)
      then have " (\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" 
      using a_ys_par_cptn a_pair env_tran ParCptnEnv  by blast
     }
     then show "(\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" using env_sol Cons split_par by fastforce
qed


lemma aux_if : 
  assumes a:" length clist = length xs \<and> 
             (\<forall>i<length xs. (i,\<Gamma>,(xs!i,s)#clist!i) \<in> cptni) \<and> 
             ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist))"
  shows "(\<Gamma>,(xs, s)#ys) \<in> par_cptn"
using a
proof (cases "length clist")
 case 0 
    then have clist_empty:"clist = []" by auto
    then have map_clist_empty:"map (\<lambda>i. (\<Gamma>,(fst i,s)#snd i)) (zip xs clist) = []"
      by fastforce
    then have conjoin:"(\<Gamma>,(xs, s)#ys) \<propto> []" using a by auto   
    then have all_eq:"\<forall>j<length (snd (\<Gamma>,(xs, s)#ys)). fst (snd (\<Gamma>,(xs, s)#ys) ! j) = []"
      using conjoin_def same_program_def
    by (simp add: conjoin_def same_program_def)          
    show ?thesis using conjoin
    proof (induct ys arbitrary: s xs) 
       case Nil then show ?case by (simp add: par_cptn.ParCptnOne)
     next       
       case (Cons a ys)                
       then have conjoin_ind:"(\<Gamma>, (xs, s) # a # ys) \<propto> []" using Cons by auto                     
       then have step:" \<Gamma>\<turnstile>\<^sub>p ((xs, s)) \<rightarrow>\<^sub>e a " unfolding conjoin_def same_length_def 
                 same_state_def same_program_def same_functions_def
                 compat_label_def same_length_state_program_def Let_def split_beta by auto 
       then have  "(\<Gamma>,(a # ys)) \<propto> []" using conjoin_ind
        unfolding conjoin_def same_length_def 
                 same_state_def same_program_def same_functions_def
                 compat_label_def same_length_state_program_def Let_def split_beta
        by auto        
      moreover obtain as sa where pair_a: "a=(as,sa)" using Cons
        using prod.exhaust_sel by blast 
      ultimately have ays_par_cptn:"(\<Gamma>, a # ys) \<in> par_cptn" using Cons.hyps by auto
      have "\<forall>j. Suc j<length (snd (\<Gamma>,(xs, s)#(as,sa)#ys)) \<longrightarrow> 
                   \<not>(\<exists>i<length []. 
                     ((fst ([]!i))\<turnstile>\<^sub>c ((snd ([]!i))!j)  \<rightarrow> ((snd ([]!i))!(Suc j))))"
        using conjoin_def compat_label_def by fastforce          
      have env_tran:"\<Gamma>\<turnstile>\<^sub>p (xs, s)  \<rightarrow>\<^sub>e (as,sa)"
        using conjoin_ind pair_a unfolding  conjoin_def compat_label_def Let_def split_beta by  auto              
      then show " (\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" 
        using ays_par_cptn pair_a  ParCptnEnv env_pe_c_c'_false by blast
   qed
next
 case Suc
    then have "length clist > 0" by auto
    then show ?thesis using a aux_if' by blast
qed

lemma aux_onlyif [rule_format]: 
 "\<forall>xs s. (\<Gamma>,(xs, s)#ys) \<in> par_cptn \<and> (length xs\<le> length (snd s))  \<longrightarrow> 
       (\<exists>clist. (length clist = length xs) \<and> 
      (\<Gamma>, (xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i,s)#(snd i))) (zip xs clist) \<and> 
      (\<forall>i<length xs. (i,\<Gamma>, (xs!i,s)#(clist!i)) \<in> cptni))"
proof (induct ys) 
  case Nil 
  {fix xs s
    assume "(\<Gamma>, [(xs, s)]) \<in> par_cptn \<and>  length xs \<le> length (snd s)"
    then have f0:"length xs \<le> length (snd s)" by auto
    have f1:"length (map (\<lambda>i. []) [0..<length xs]) = length xs" by auto
    have f2:"(\<Gamma>, [(xs, s)]) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                              (zip xs (map (\<lambda>i. []) [0..<length xs]))"
      unfolding conjoin_def same_length_state_program_def same_length_def 
             same_functions_def same_state_def same_program_def compat_label_def  
      by(simp add: f0, rule nth_equalityI,simp,simp)
    note h = conjI[OF f1 f2]
    have f3:"(\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # (map (\<lambda>i. []) [0..<length xs]) ! i) \<in> cptni)"
      by (simp add: cptni.CptnOnei)
    note this = conjI[OF h f3]
    }
     thus ?case by blast
next
  case (Cons a ys) 
  {fix  xs s
    assume a1:"(\<Gamma>, (xs, s) # a # ys) \<in> par_cptn \<and>   length xs \<le> length (snd s)"
    then have a1:"(\<Gamma>, (xs, s) # a # ys) \<in> par_cptn" and 
              state_prog:"same_length_state_program ((xs, s) # a # ys)"
      unfolding same_length_state_program_def by auto
   then obtain as sa where a_pair: "a=(as,sa)"  using prod.exhaust_sel by blast
   then have par_cptn':"(\<Gamma>,( (as,sa)#ys)) \<in> par_cptn"
     using a1 par_cptn_dest by blast 
   moreover  have sa_len:"length as \<le> length (snd sa)"  
     using all_same_length_state_program[OF a1[simplified a_pair] state_prog[simplified a_pair], 
                                         of "Suc 0"]  by auto
   ultimately obtain clist where hyp: "
              length clist = length as \<and>
              (\<Gamma>, (as, sa) #
                   ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, sa) # snd i)) (zip as clist) \<and>
              (\<forall>i<length as. (i,\<Gamma>, (as ! i, sa) # clist ! i) \<in> cptni)"
     using Cons.hyps by fastforce
   have a11:"(\<Gamma>, (xs, s) # (as,sa) # ys) \<in> par_cptn" using a1 a_pair by auto
   have par_cptn_dest:"\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow>\<^sub>e (as, sa) \<or> \<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow> (as, sa)"
     using par_cptn_elim_cases par_cptn' a1  a_pair by blast 
   {
     assume a1: "\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow>\<^sub>e (as, sa)"          
     then have xs_as_eq:"xs=as" by (meson env_pe_c_c'_false)     
     then have ce:"\<forall>i < length xs. \<Gamma>\<turnstile>\<^sub>c (xs!i, toSeqState i s) \<rightarrow>\<^sub>e (as!i, toSeqState i sa)" using a1 pe_ce by fastforce
     then have ce':"\<forall>i < length xs. \<Gamma>\<turnstile>\<^sub>c (xs!i, toSeqState i s) \<rightarrow>\<^sub>c\<^sub>e (as!i, toSeqState i sa)"
       by (simp add: e_step) 
     then have ce_ci:"\<forall>i < length xs. \<Gamma>\<turnstile>\<^sub>c\<^sub>i (xs!i, s) \<rightarrow>\<^sub>c\<^sub>e (as!i, sa)"
       by (smt Pair_inject Suc_less_SucD a1 ce eq_snd_iff less_Suc_eq_le less_trans_Suc sa_len step_cei_i2 step_pe.cases)
     let ?clist="(map (\<lambda>j. (xs!j, sa)#(clist!j)) [0..<length xs])"    
     have s1:"length ?clist = length xs"
       by auto
     have s2:"(\<forall>i<length xs. (i, \<Gamma>, (xs ! i, s) # ?clist ! i) \<in> cptni)"  
        using a1 hyp  xs_as_eq ce cptni.Cptni  cptni_cases
        by (smt ce_ci length_map map_nth nth_map) 
     have s3:"(\<Gamma>, (xs, s) #
                       (as,sa) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist)"     
     proof -        
         have s_len:"same_length (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
               using hyp conjoin_def same_length_def xs_as_eq a1 by fastforce
         have s_state: "same_state (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp
              apply (simp add:hyp conjoin_def same_state_def  a1)              
              apply clarify
              apply(case_tac j) 
              by (simp add: xs_as_eq,simp add: xs_as_eq)
         have s_function: "same_functions (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp conjoin_def same_functions_def a1 by fastforce
         have s_program: "same_program (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"          
              using hyp
              apply (simp add:hyp conjoin_def same_program_def same_length_def a1)
              apply clarify
              apply(case_tac j)                
                apply(rule nth_equalityI) 
                apply(simp,simp)              
              by(rule nth_equalityI, simp add: hyp xs_as_eq, simp add:xs_as_eq)
         have s_compat:"compat_label (\<Gamma>, (xs, s) # (xs,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))" 
           using a1  
            apply (simp add:compat_label_def Let_def split_beta)
           apply clarify
           apply(case_tac j;simp add: xs_as_eq) 
            apply (blast dest: pe_ce)
           using hyp unfolding conjoin_def compat_label_def Let_def split_beta toSeqCptn_def apply simp
            apply clarify
            apply(erule_tac x=nat in allE,erule impE,assumption)             
            apply(erule disjE,simp)
            apply clarify
            apply(rule_tac x=i in exI) 
           by auto
        thus ?thesis using s_len s_program s_state s_function  xs_as_eq state_prog a_pair unfolding conjoin_def
          by auto
     qed
     then have 
      "(\<exists>clist. length clist = length xs \<and>
                  (\<Gamma>, (xs, s) #
                       a # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs clist) \<and>
                  (\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni))"
     using s1 s2 a_pair by blast
   } note s1=this
   {
     assume a1':"\<Gamma>\<turnstile>\<^sub>p (xs, s) \<rightarrow> (as, sa)"
     have s_len:" length xs \<le> length (snd s)"
       using same_length_state_program_def state_prog by force    
     then obtain i r s' where 
       inter_tran:"i < length xs \<and> \<Gamma>\<turnstile>\<^sub>c (xs ! i, toSeqPar i s) \<rightarrow> (r, s') \<and> 
                   as = xs[i := r] \<and> sa = toPar i s' s" 
       using par_ctranE[OF a1']                                                                
       by (smt Pair_inject)
     have eq_locals:"(\<forall>j\<noteq>i. (snd s)!j = (snd sa)!j)"
       by (simp add: inter_tran)
     have 
       inter_tran:"i < length xs \<and> \<Gamma>\<turnstile>\<^sub>c (xs ! i, toSeqPar i s) \<rightarrow> (r, toSeqPar i sa) \<and> as = xs[i := r]"        
       using inter_tran sa_len  by auto       
     then have xs_as_eq_len: "length xs = length as" by simp
     (* from inter_tran 
      have s_states:"\<exists>nsa. s=Normal nsa \<or> (s=sa \<and> (\<forall>sa. (s\<noteq>Normal sa)))"      
        using a1' par_cptn_not_normal_eq by blast *)
      then have  xstate_s:
         "\<And>j. j\<noteq>i  \<Longrightarrow> snd (fst (toSeqState j s)) = snd (fst (toSeqState j sa)) \<and> 
                  length (snd ( toSeqState j s)) = length (snd ( toSeqState j sa))"        
        apply (auto simp add: toSeqState_def  case_prod_beta' eq_locals )
        by (metis (no_types) a1' eq_length_p_step')                        
     have as_xs:"\<forall>i'<length as. (i'=i \<and> as!i'=r) \<or> (as!i'=xs!i')"
       using xs_as_eq_len by (simp add: inter_tran nth_list_update)
     let ?clist="(map (\<lambda>j. (as!j, sa)#(clist!j)) [0..<length xs]) [i:=((r, sa)#(clist!i))]"
     have s1:"length ?clist = length xs"
       by auto
     have s2:"(\<forall>i'<length xs. (i', \<Gamma>, (xs ! i', s) # ?clist ! i') \<in> cptni)" 
        proof -
         {fix i'
          assume a1:"i' < length xs"          
          have "(i',\<Gamma>, (xs ! i', s) # ?clist ! i') \<in> cptni"
          proof (cases "i=i'")
            case True 
             then show ?thesis using True inter_tran[simplified toSeqPar_eq_toSeq] 
                             step_cei_i1[of  i s sa \<Gamma> "xs!i" r]  
                       eq_locals hyp s1 cptni.Cptni  s_len sa_len
               by (smt Suc_lessD a1' eq_length_p_step' le_neq_implies_less 
               length_list_update less_trans_Suc nth_list_update_eq)
          next              
            case False    
            have a01:"\<Gamma>\<turnstile>\<^sub>c (xs ! i', toSeqState i' s) \<rightarrow>\<^sub>e (xs ! i',toSeqState i' sa)"
              apply (auto simp add: toSeqState_def)
              by (metis (mono_tags, lifting) False a1' env_intro eq_length_p_step' 
                   eq_locals length_append length_drop length_take prod.case_eq_if)              
            have a02:"length (snd s) = length (snd sa)"
              using a1' eq_length_p_step' eq_refl by blast
            have a03:"i'<length (snd s)"
              using a1 s_len by auto
            show ?thesis using  inter_tran  False hyp Cptni a1
              apply clarify
              apply simp
              apply(erule_tac x=i' in allE)
              apply (simp)
              apply(rule Cptni) using step_cei_i2[OF a02 a03 a01]
              by auto
          qed
         } 
        thus ?thesis by fastforce
      qed
     then have s3:"(\<Gamma>, (xs, s) # (as,sa) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs ?clist)"
     proof -        
        from hyp have 
         len_list:"length clist = length as" by auto
        from hyp have same_len:"same_length (\<Gamma>, (as, sa) # ys)  
                      (map (\<lambda>i. (\<Gamma>, (fst i, sa) # snd i)) (zip as clist))"
          using conjoin_def by auto        
        have s_len: "same_length (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"  
          using 
            same_len  inter_tran  
            unfolding conjoin_def same_length_def
            apply clarify 
            apply(case_tac "i=ia")            
            by (auto simp add: len_list)            
        have s_state: "same_state (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp inter_tran unfolding conjoin_def same_state_def
               apply clarify
               apply(case_tac j, simp, simp (no_asm_simp))
               apply(case_tac "i=ia",simp , simp )
              by (metis (no_types, hide_lams) as_xs nth_list_update_eq xs_as_eq_len)              
        have s_function: "same_functions (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"
              using hyp conjoin_def same_functions_def a1 by fastforce
        have s_program: "same_program (\<Gamma>, (xs, s) # (as,sa) # ys) 
                           (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))"          
          using hyp inter_tran unfolding conjoin_def same_program_def
           apply clarify
           apply(case_tac j,simp)           
           apply(rule nth_equalityI,simp,simp)
           apply simp
           apply(rule nth_equalityI,simp,simp)
           apply(erule_tac x=nat and P="\<lambda>j. H j \<longrightarrow> (fst (a j))=((b j))" for H a b in allE)
           apply(case_tac nat)
           apply clarify
           apply(case_tac "i=ia",simp,simp)
           apply clarify
          by(case_tac "i=ia",simp,simp)                   
        have s_compat:"compat_label (\<Gamma>, (xs, s) # (as,sa) # ys) (map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs ?clist))" 
        using inter_tran hyp 
        unfolding conjoin_def compat_label_def Let_def
         apply clarify
         apply(case_tac j)
          apply(rule conjI,simp)
          using a1' apply fastforce
           apply clarify 
           apply(rule exI[where x=i],simp  add: toSeqPar_eq_toSeq toSeqState_def split_beta)
           apply clarify 
           apply (rule snormal_enviroment, simp)
          apply (metis (no_types, lifting) a1' eq_length_p_step' eq_locals)
         apply(erule_tac x=nat and P="\<lambda>j. H j \<longrightarrow> (P j \<or> Q j)" for H P Q in allE,simp)         
        apply(erule disjE )
         apply clarify
         apply(rule_tac x=ia in exI,simp)
         apply(rule conjI)
          apply(case_tac "i=ia",simp,simp)
         apply clarify
         apply(case_tac "i=l",simp)
          apply(case_tac "l=ia",simp,simp)
          apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
         apply simp
         apply(erule_tac x=l in allE,erule impE,assumption,erule impE, assumption,simp)
        apply clarify
        apply (thin_tac " \<forall>ia<length xs. (ia,\<Gamma>, (xs[i := r] ! ia, sa) # clist ! ia) \<in> cptni")
        apply(erule_tac x=ia and P="\<lambda>j. H j \<longrightarrow> (P j)" for H P in allE, erule impE, assumption)
        by(case_tac "i=ia",simp,simp)               
        thus ?thesis using s_len s_program s_state s_function conjoin_def state_prog a_pair
          by fastforce
     qed     
     then have "(\<exists>clist.
                  length clist = length xs \<and>
                  (\<Gamma>, (xs, s) #
                       a # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs clist) \<and>
                  (\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni))"
     using s1 s2 a_pair by blast
   } 
   then have 
      "(\<exists>clist.
                  length clist = length xs \<and>
                  (\<Gamma>, (xs, s) #
                       a # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                                   (zip xs clist) \<and>
                  (\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni))"
      using s1 par_cptn_dest by fastforce
  }  
  thus ?case by auto
qed  

lemma one_iff_aux_if:"xs\<noteq>[] \<Longrightarrow> (\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
 (\<exists>clist. length clist= length xs \<and> 
 ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
 (\<forall>i<length xs. (i,\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptni))) \<Longrightarrow>
 (par_cp  \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. clist!i \<in> cpi i \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"
proof
  assume a1:"xs\<noteq>[]"
  assume a2:"\<forall>ys. ((\<Gamma>, (xs, s) # ys) \<in> par_cptn) =
         (\<exists>clist.
             length clist = length xs \<and>
             (\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist) \<and>
             (\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni))"         
   show "par_cp \<Gamma> xs s \<subseteq> 
             {(\<Gamma>1, c). \<exists>clist.
               length clist = length xs \<and>
               (\<forall>i<length clist. clist ! i \<in> cpi  i \<Gamma> (xs ! i) s) \<and>
               (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
   proof-{     
     fix x
     let ?show = "x\<in> {(\<Gamma>1, c). \<exists>clist. length clist = length xs \<and>
                   (\<forall>i<length clist. clist ! i \<in> cpi  i \<Gamma> (xs ! i) s) \<and>
                    (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
     assume a3:"x\<in>par_cp  \<Gamma> xs s"   
     then obtain y where x_pair: "x=(\<Gamma>,y)"
       unfolding par_cp_def by auto       
     have ?show          
     proof (cases y)
        case Nil then 
         show ?show using a1 a2 a3 x_pair
          unfolding par_cp_def cp_def
          by (force elim:par_cptn.cases)
     next 
        case (Cons a list) then
          show ?show using a1 a2 a3 x_pair
          unfolding par_cp_def cpi_def wf_state_def         
          by(auto, rule_tac x="map (\<lambda>i. (\<Gamma>,(fst i, s) # snd i)) (zip xs clist)" in exI, auto)            
     qed
   } thus ?thesis using a1 a2 by auto 
   qed
   {   
   show "{(\<Gamma>1, c). \<exists>clist.
          length clist = length xs \<and>
          (\<forall>i<length clist. clist ! i \<in> cpi i \<Gamma> (xs ! i) s) \<and>
          (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>} \<subseteq> par_cp \<Gamma> xs s" using a1 a2 
   proof-
     { 
     fix x
     assume a3:"x\<in>{(\<Gamma>1, c). \<exists>clist.
          length clist = length xs \<and>
          (\<forall>i<length clist. clist ! i \<in> cpi  i \<Gamma> (xs ! i) s) \<and>
          (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
     then obtain c where x_pair: "x=(\<Gamma>,c)"  by auto
     then obtain clist where 
      props:"length clist = length xs \<and>
           (\<forall>i<length clist. clist ! i \<in> cpi  i \<Gamma> (xs ! i) s) \<and>
           (\<Gamma>, c) \<propto> clist " using a3 by auto
     then have "x\<in>par_cp  \<Gamma> xs s"
       proof (cases c)
         case Nil 
         have clist_0: 
           "clist ! 0 \<in> cpi  0 \<Gamma> (xs ! 0) s" using props a1 
         by auto
         thus "x\<in>par_cp  \<Gamma> xs s"  
           using a1 a2 props Nil x_pair
         unfolding cpi_def conjoin_def same_length_def 
         apply clarify  
         by (erule cptni.cases, fastforce, fastforce)
       next
         case (Cons a ys) 
         then obtain a1 a2 where a_pair: "a=(a1,a2)" 
           using props
           using prod.exhaust_sel by blast 
         from a2 have 
               a2:"(((\<Gamma>, (xs, s) # ys) \<in> par_cptn) =
                   (\<exists>clist. length clist = length xs \<and>
                   (\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist) \<and>
                   (\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni)))" by auto
         have a2_s:"a2=s" using a1 props a_pair Cons
           unfolding  conjoin_def   same_state_def  cpi_def         
           by force
         have a1_xs:"a1 = xs"
           using  props a_pair Cons 
           unfolding par_cp_def conjoin_def  same_program_def cpi_def           
           apply clarify
           apply(erule_tac x=0 and P="\<lambda>j. H j \<longrightarrow> (fst (s j))=((t j))" for H s t in allE)                      
           by(rule nth_equalityI,auto)   
         then have conjoin_clist_xs:"(\<Gamma>, (xs,s)#ys) \<propto> clist"     
           using a1  props a_pair Cons a1_xs a2_s by auto
         also then have "clist = map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs ((map (\<lambda>x. tl (snd x))) clist))"             
           using clist_map_zip a1
           by blast
         ultimately have conjoin_map:"(\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs ((map (\<lambda>x. tl (snd x))) clist))"
           using props x_pair Cons a_pair a1_xs a2_s by auto    
         have "\<And>n. \<not> n < length xs \<or> clist ! n \<in> {(f, ps). ps ! 0 = (xs ! n, a2) \<and> (n,\<Gamma>, ps) \<in> cptni \<and> f = \<Gamma>}"
               using a1_xs a2_s props 
               by (simp add: cpi_def prod.case_eq_if)
         then have clist_cptn:"(\<forall>i<length clist. (fst (clist!i) = \<Gamma>) \<and> 
                                 (i,\<Gamma>, snd (clist!i)) \<in> cptni \<and>
                                 (snd (clist!i))!0 = (xs!i,s))"
         using a1_xs a2_s props by fastforce         
                       
          {fix i
          assume a4: "i<length xs"     
          then have clist_i_cptn:"(fst (clist!i) = \<Gamma>) \<and> 
                     (i,\<Gamma>, snd (clist!i)) \<in> cptni \<and>
                     (snd (clist!i))!0 = (xs!i,s)"
           using props clist_cptn by fastforce 
          from a4 props have a4':"i<length clist" by auto
          have lengz:"length (snd (clist!i))>0" 
            using conjoin_clist_xs a4'
            unfolding  conjoin_def same_length_def 
           by auto
          then have clist_hd_tl:"snd (clist!i) =  hd (snd (clist!i)) # tl (snd (clist ! i))"
            by auto        
          also have " hd (snd (clist!i)) =  (snd (clist!i))!0"
            using a4' lengz by (simp add: hd_conv_nth)
          ultimately have clist_i_tl:"snd (clist!i) =  (xs!i,s) # tl (snd (clist ! i))"
            using clist_i_cptn by fastforce
          also have "tl (snd (clist ! i)) = map (\<lambda>x. tl (snd x)) clist!i"
            using nth_map a4' 
          by auto
          ultimately have snd_clist:"snd (clist!i) =  (xs ! i, s) # map (\<lambda>x. tl (snd x)) clist ! i"
            by auto
          also have "(clist!i) = (fst (clist!i),snd (clist!i))"
            by auto
          ultimately have "(clist!i) =(\<Gamma>, (xs ! i, s) # map (\<lambda>x. tl (snd x)) clist ! i)"
           using clist_i_cptn by auto
          then have "(i,\<Gamma>, (xs ! i, s) # map (\<lambda>x. tl (snd x)) clist ! i) \<in> cptni" 
             using clist_i_cptn by auto
          } 
          then have clist_in_cptn:"(\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # ((map (\<lambda>x. tl (snd x))) clist) ! i) \<in> cptni)"
          by auto
         have same_length_clist_xs:"length ((map (\<lambda>x. tl (snd x))) clist)  = length xs"
           using props by auto
         then have "(\<exists>clist. length clist = length xs \<and>
                        (\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist) \<and>
                        (\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni))"
         using  a1  props x_pair a_pair Cons a1_xs a2_s conjoin_clist_xs clist_in_cptn
            conjoin_map clist_map by blast         
         then have "(\<Gamma>, c) \<in> par_cptn" using  a1 a2  props x_pair a_pair Cons a1_xs a2_s
         unfolding par_cp_def by simp          
         thus "x\<in>par_cp \<Gamma> xs s"  
           using a1 a2  props x_pair a_pair Cons a1_xs a2_s
           unfolding wf_state_def par_cp_def conjoin_def  same_length_def same_program_def 
                     same_state_def same_functions_def compat_label_def Let_def split_beta 
                     same_length_state_program_def
           by simp
       qed
     }
     thus ?thesis using a1 a2 by auto  
   qed
  } 
qed



lemma one_iff_aux_only_if:"xs\<noteq>[] \<Longrightarrow>  
 (par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. clist!i \<in> cpi  i \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}) \<Longrightarrow>
 length xs \<le> length (snd s)  \<Longrightarrow>
 (\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
   (\<exists>clist. length clist= length xs \<and> 
   ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
   (\<forall>i<length xs. (i,\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptni)))"
proof
  fix ys
  assume a1: "xs\<noteq>[]"
  assume a2: "par_cp  \<Gamma> xs s =
          {(\<Gamma>1, c).
           \<exists>clist.
              length clist = length xs \<and>
              (\<forall>i<length clist.
                  clist ! i \<in> cpi  i \<Gamma> (xs ! i) s) \<and>
              (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
  assume a3:"  length xs \<le> length (snd s) "
  from a1 a2 a3 show
  "((\<Gamma>, (xs, s) # ys) \<in> par_cptn) =
          (\<exists>clist.
              length clist = length xs \<and>
              (\<Gamma>,
               (xs, s) #
               ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                       (zip xs clist) \<and>
              (\<forall>i<length xs.
                  (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni))"
  proof auto
    {assume a4:"(\<Gamma>, (xs, s) # ys) \<in> par_cptn"
     then show "\<exists>clist.
       length clist = length xs \<and>
       (\<Gamma>, (xs, s) # ys) \<propto> map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i))
                (zip xs clist) \<and>
       (\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i) \<in> cptni)"
       using a1 a2 a3 by (auto simp add: aux_onlyif)
    }                                      
    {fix clist ::"(('a \<times> 'b, 'c, 'd, 'e) LanguageCon.com \<times> 'a \<times> 'b list) list list"
    assume a4: "length clist = length xs"
    assume a5:"(\<Gamma>, (xs, s) # ys) \<propto> 
               map (\<lambda>i. (\<Gamma>, (fst i, s) # snd i)) (zip xs clist)"
    assume a6: "\<forall>i<length xs. (i,\<Gamma>, (xs ! i, s) # clist ! i)
                     \<in> cptni"
    show "(\<Gamma>, (xs, s) # ys) \<in> par_cptn" 
    using a3 a4 a5 a6 using aux_if by blast 
    }
  qed
qed

lemma one_iff_aux: "xs\<noteq>[]  \<Longrightarrow>  length xs \<le> length (snd s)  \<Longrightarrow>
 (\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
         (\<exists>clist. length clist= length xs \<and> 
     ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
     (\<forall>i<length xs. (i, \<Gamma>,(xs!i,s)#(clist!i)) \<in> cptni))) = 
 (par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
 (\<forall>i<length clist. clist!i \<in> cpi  i \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"
proof 
  assume a1:"xs\<noteq>[]"  and a1':"length xs \<le> length (snd s) "
  {assume a2:"(\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
   (\<exists>clist. length clist= length xs \<and> 
   ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
   (\<forall>i<length xs. (i,\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptni)))"      
    then show "(par_cp \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
   (\<forall>i<length clist. clist!i \<in> cpi  i \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"      
      by (smt Collect_cong a1 all_same_length_state_program aux_if aux_onlyif conjoin_def 
             fst_conv length_Cons nth_Cons_0 one_iff_aux_if prod.case_eq_if snd_conv zero_less_Suc)
  }
  {assume a2:"(par_cp  \<Gamma> (xs) s = {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and>
   (\<forall>i<length clist. clist!i \<in> cpi  i \<Gamma> (xs!i) s) \<and> (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>})"    
    then show "(\<forall>ys. ((\<Gamma>,((xs, s)#ys)) \<in> par_cptn) = 
   (\<exists>clist. length clist= length xs \<and> 
   ((\<Gamma>,(xs, s)#ys) \<propto> map (\<lambda>i. (\<Gamma>,(fst i,s)#(snd i))) (zip xs clist)) \<and> 
   (\<forall>i<length xs. (i,\<Gamma>,(xs!i,s)#(clist!i)) \<in> cptni)))" 
   by (auto simp add: a1 a1' a2 one_iff_aux_only_if)
  }
qed

inductive_cases cptni_cases1:
"(i,\<Gamma>, x) \<in> cptni"

lemma no_cptni_empty:" (i, \<Gamma>, x) \<in> cptni \<Longrightarrow> x=[] \<Longrightarrow> P"
  by (rule cptni_cases1, auto)

theorem notwf:"xs \<noteq> [] \<Longrightarrow> 
   \<not> (length xs \<le> length (snd s)) \<Longrightarrow> 
   par_cp  \<Gamma> xs s =
        {(\<Gamma>1, c).
         \<exists>clist.
            length clist = length xs \<and> length xs \<le>  length (snd s) \<and>
            (\<forall>i<length clist. clist ! i \<in> cpi  i \<Gamma> (xs ! i) s) \<and> (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}"
proof-
  assume a0:"xs\<noteq>[]" and a1:"\<not> (length xs \<le> length (snd s))"
  then have "par_cp  \<Gamma> xs s = {}" unfolding par_cp_def  by auto
  moreover have "{(\<Gamma>1, c).
         \<exists>clist.
            length clist = length xs \<and> length xs \<le>  length (snd s) \<and>
            (\<forall>i<length clist. clist ! i \<in> cpi  i \<Gamma> (xs ! i) s) \<and> (\<Gamma>, c) \<propto> clist \<and> \<Gamma>1 = \<Gamma>}= {}"
    unfolding cpi_def conjoin_def same_length_def wf_state_def same_state_def same_program_def same_functions_def
same_length_state_program_def split_beta apply auto  using no_cptni_empty
    using a0 a1 apply blast 
    using a0 a1 by blast
  ultimately show ?thesis by auto
qed

theorem one: 
"xs\<noteq>[] \<Longrightarrow>
 par_cp  \<Gamma> xs s = 
    {(\<Gamma>1,c). \<exists>clist. (length clist)=(length xs) \<and> length xs \<le> length (snd s) \<and>
             (\<forall>i<length clist. (clist!i) \<in> cpi i \<Gamma> (xs!i) s) \<and> 
             (\<Gamma>,c) \<propto> clist \<and> \<Gamma>1=\<Gamma>}"
  apply (cases "(length xs) \<le> length (snd s) ")
   apply(frule one_iff_aux[], assumption) 
  apply (auto simp add: aux_onlyif aux_if )[1]
  by (auto simp add: aux_onlyif aux_if notwf)


end
