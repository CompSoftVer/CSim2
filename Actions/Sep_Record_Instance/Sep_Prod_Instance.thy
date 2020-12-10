(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      Sep_Prod_Instance.thy
    Author:     David Sanan, NTU

Copyright (C) 2015-2016 David Sanan 
Some rights reserved, NTU
This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)
theory Sep_Prod_Instance
imports Sep_Algebra.Separation_Algebra "Separata.Separata"
begin
section{* Product of Separation Algebras Instantiation *} 

instantiation prod::(sep_algebra,sep_algebra) sep_algebra
begin                             
definition zero_prod_def: "0 \<equiv> (0,0)"
definition plus_prod_def: "p1 + p2 \<equiv> ((fst p1) + (fst p2),(snd p1) + (snd p2))"
definition sep_disj_prod_def: "sep_disj p1 p2 \<equiv> ((fst p1) ## (fst p2) \<and> (snd p1) ## (snd p2))"

instance
  apply standard
        apply (simp add: sep_disj_prod_def zero_prod_def)
       apply (simp add: sep_disj_commute sep_disj_prod_def)       
      apply (simp add: zero_prod_def  plus_prod_def)
     apply (simp add: plus_prod_def sep_disj_prod_def sep_disj_commute sep_add_commute)     
    apply (simp add: plus_prod_def sep_add_assoc sep_disj_prod_def)    
   apply (simp add: sep_disj_prod_def plus_prod_def )
   apply (fastforce intro:sep_disj_addD1)
  apply (simp add: sep_disj_prod_def prod_def plus_prod_def sep_disj_addI1)  
  done
end

instantiation prod::(heap_sep_algebra, heap_sep_algebra) heap_sep_algebra
begin
  instance
   proof
    fix x :: "'a \<times> 'b" and z :: "'a \<times> 'b" and y :: "'a \<times> 'b"
    assume a1: "x + z = y + z"
    assume a2: "x ## z"
    assume a3: "y ## z"
    have f4: "fst x + fst z = fst y + fst z \<and> snd x + snd z = snd y + snd z"
      using a1 by (simp add: plus_prod_def)
    have f5: "\<forall>p pa. p ## pa = ((fst p::'a) ## fst pa \<and> (snd p::'b) ## snd pa)"
      using sep_disj_prod_def by blast
    hence f6: "fst x = fst y"
      using f4 a3 a2 by (meson sep_add_cancel)
    have "snd x = snd y"
      using f5 f4 a3 a2 by (meson sep_add_cancel)
    thus "x = y"
      using f6 by (simp add: prod_eq_iff) 
  next
     fix x:: "'a \<times> 'b"
     assume "x##x"
     thus "x=0"
      by (metis sep_add_disj sep_disj_prod_def surjective_pairing zero_prod_def)  
   next
     fix a :: "'a \<times> 'b" and b :: "'a \<times> 'b" and c :: "'a \<times> 'b" and d :: "'a \<times> 'b" and w :: "'a \<times> 'b"
     assume wab:"a + b = w" and wcd:"c + d = w" and  abdis:"a ## b" and cddis:"c ## d"     
     then obtain a1 a2 b1 b2 c1 c2 d1 d2 w1 w2 where 
       a:"a= (a1,a2)" and
       b:"b= (b1,b2)" and
       c:"c= (c1,c2)" and
       d:"d= (d1,d2)" and
       e:"w= (w1,w2)" by fastforce   
     have "\<exists>e1 f1 g1 h1. a1=e1+f1 \<and> b1 = g1 + h1 \<and> c1=e1+g1 \<and> d1 = f1+h1 \<and> 
         e1##f1 \<and> g1##h1 \<and> e1##g1 \<and> f1##h1"
     using wab wcd abdis cddis a b c d e
       unfolding plus_prod_def sep_disj_prod_def
       using sep_add_cross_split 
       by fastforce 
     also have "\<exists>e2 f2 g2 h2. a2=e2+f2 \<and> b2 = g2 + h2 \<and> c2=e2+g2 \<and> d2 = f2+h2 \<and> 
         e2##f2 \<and> g2##h2 \<and> e2##g2 \<and> f2##h2"
       using wab wcd abdis cddis a b c d e
       unfolding plus_prod_def sep_disj_prod_def
       using sep_add_cross_split 
       by fastforce
     ultimately show  "\<exists> e f g h. e + f = a \<and> g + h = b \<and> e + g = c \<and> f + h = d \<and> 
                  e ## f \<and> g ## h \<and> e ## g \<and> f ## h"        
     using  a b c d e
       unfolding plus_prod_def sep_disj_prod_def       
       by fastforce
    next
      fix x :: "'a \<times> 'b" and y :: "'a \<times> 'b"
      assume "x+y=0" and
             "x##y"
      thus "x=0"
      proof -
        have f1: "(fst x + fst y, snd x + snd y) = 0"
          by (metis (full_types) \<open>x + y = 0\<close> plus_prod_def)
        then have f2: "fst x = 0"
          by (metis (no_types) \<open>x ## y\<close> fst_conv sep_add_ind_unit sep_disj_prod_def zero_prod_def)
        have "snd x + snd y = 0"
          using f1 by (metis snd_conv zero_prod_def)
        then show ?thesis
          using f2 by (metis (no_types) \<open>x ## y\<close> fst_conv plus_prod_def sep_add_ind_unit sep_add_zero sep_disj_prod_def snd_conv zero_prod_def)
      qed
    next 
      fix x :: "'a \<times> 'b" and y :: "'a \<times> 'b" and z :: "'a \<times> 'b"
      assume "x ## y" and "y ## z" and "x ## z"
      then have "x ## (fst y + fst z, snd y + snd z)"
          by (metis \<open>x ## y\<close> \<open>x ## z\<close> \<open>y ## z\<close> disj_dstri fst_conv sep_disj_prod_def snd_conv)
      thus "x ## y + z" by (metis plus_prod_def)
    next
      fix x :: "'a \<times> 'b" and y :: "'a \<times> 'b" and z :: "'a \<times> 'b"      
      assume "y ## z"              
      then show "x ## y + z = (x ## y \<and> x ## z)" 
        unfolding sep_disj_prod_def plus_prod_def
        by auto
    next
      fix x :: "'a \<times> 'b" and y :: "'a \<times> 'b"
      assume "x ## x" and "x + x = y"
      thus  "x=y"
        by (metis disjoint_zero_sym plus_prod_def sep_add_disj sep_add_zero_sym sep_disj_prod_def)        
  qed
end

lemma fst_fst_dist:"fst (fst x + fst y) = fst (fst x) + fst (fst y)"
by (simp add: plus_prod_def)

lemma fst_snd_dist:"fst (snd x + snd y) = fst (snd x) + fst (snd y)"
by (simp add: plus_prod_def)

lemma snd_fst_dist:"snd (fst x + fst y) = snd (fst x) + snd (fst y)"
by (simp add: plus_prod_def)

lemma snd_snd_dist:"snd (snd x + snd y) = snd (snd x) + snd (snd y)"
by (simp add: plus_prod_def)


lemma dis_sep:"(\<sigma>1, \<sigma>2) = (x1',x2') + (x1'',x2'') \<and> 
       (x1',x2') ## (x1'',x2'') \<Longrightarrow>
       \<sigma>1 =(x1'+ x1'') \<and> x1' ## x1'' \<and> x2' ## x2''
      \<and> \<sigma>2 =(x2'+ x2'')"
by (simp add: plus_prod_def sep_disj_prod_def)

lemma substate_prod: "\<sigma>1 \<preceq> \<sigma>1' \<and> \<sigma>2 \<preceq> \<sigma>2' \<Longrightarrow> (\<sigma>1,\<sigma>2)  \<preceq>  (\<sigma>1',\<sigma>2')"
proof -
  assume a1:"\<sigma>1 \<preceq> \<sigma>1' \<and> \<sigma>2 \<preceq> \<sigma>2'"
  then obtain x where sub_x:"\<sigma>1 ## x \<and> \<sigma>1 + x = \<sigma>1'" using sep_substate_def by blast
  with a1 obtain y where sub_y:"\<sigma>2 ## y \<and> \<sigma>2 + y = \<sigma>2'" using sep_substate_def by blast    
  have dis_12:"(\<sigma>1,\<sigma>2)##(x,y)" using sub_x sub_y  by (simp add: sep_disj_prod_def)
  have union_12:"(\<sigma>1',\<sigma>2') = (\<sigma>1,\<sigma>2)+(x,y)" using  sub_x sub_y  by (simp add: plus_prod_def)
  show "(\<sigma>1,\<sigma>2) \<preceq> (\<sigma>1',\<sigma>2')" using sep_substate_def dis_12 union_12 by auto
qed

lemma disj_sep_substate:
  "(\<sigma>1,\<sigma>'\<triangleright>\<sigma>1') \<and> (\<sigma>2,\<sigma>''\<triangleright>\<sigma>2')  \<Longrightarrow> 
   (\<sigma>1,\<sigma>2)  \<preceq>  (\<sigma>1',\<sigma>2')"
proof-
assume a1:"(\<sigma>1,\<sigma>'\<triangleright>\<sigma>1') \<and> (\<sigma>2,\<sigma>''\<triangleright>\<sigma>2')"  
  thus "(\<sigma>1,\<sigma>2)  \<preceq>  (\<sigma>1',\<sigma>2')"   
    by (metis substate_prod tern_rel_def sep_substate_disj_add)
qed


lemma sep_tran_disjoint_split:
    "(x , y \<triangleright> (\<sigma>1::('a::heap_sep_algebra, 'a::heap_sep_algebra)prod,\<sigma>2))  \<Longrightarrow>
     (\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')\<Longrightarrow>      
     (\<sigma>1',\<sigma>2') = (((fst (fst x) + fst (fst y) + fst \<sigma>'),snd (fst x) + snd (fst y) + snd \<sigma>'),
                   fst (snd x) + fst (snd y) + fst \<sigma>'', snd (snd x) + snd (snd y) + snd \<sigma>'')"
proof-
  assume a1:"(x, y \<triangleright> (\<sigma>1,\<sigma>2))" 
  then have descomp_sigma:"\<sigma>1 = fst x + fst y \<and> \<sigma>2 = snd x + snd y \<and> fst x ## fst y \<and> snd x ## snd y" 
     by (simp add: tern_rel_def plus_prod_def sep_disj_prod_def)
  assume a2: "(\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')"
  then show "(\<sigma>1',\<sigma>2') =(((fst (fst x) + fst (fst y) + fst \<sigma>'),snd (fst x) + snd (fst y) + snd \<sigma>'),
                   fst (snd x) + fst (snd y) + fst \<sigma>'', snd (snd x) + snd (snd y) + snd \<sigma>'')"
    by (simp add: descomp_sigma plus_prod_def tern_rel_def)           
qed

lemma sep_tran_disjoint_disj1:
   "(x , y \<triangleright> (\<sigma>1::('a::heap_sep_algebra, 'a::heap_sep_algebra)prod,\<sigma>2))  \<Longrightarrow>
     (\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')\<Longrightarrow>   
    (fst (fst x + fst y) ##  fst \<sigma>') 
    \<and> (snd (fst x + fst y) ##  snd \<sigma>')
   \<and> ((fst (snd x + snd y)) ##  fst \<sigma>'')
   \<and> ((snd (snd x + snd y)) ##  snd \<sigma>'')
   "
proof -
 assume a1:"(x, y \<triangleright> (\<sigma>1,\<sigma>2))" 
  then have descomp_sigma:
       "\<sigma>1 = fst x + fst y \<and> \<sigma>2 = snd x + snd y \<and> 
        fst x ## fst y \<and> snd x ## snd y" 
     by (simp add: tern_rel_def plus_prod_def sep_disj_prod_def)
  assume a2: "(\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')"
 then show " (fst (fst x + fst y) ##  fst \<sigma>') 
    \<and> (snd (fst x + fst y) ##  snd \<sigma>')
   \<and> ((fst (snd x + snd y)) ##  fst \<sigma>'')
   \<and> ((snd (snd x + snd y)) ##  snd \<sigma>'')
   "
  by (simp add: descomp_sigma sep_disj_prod_def tern_rel_def) 
qed

lemma sep_tran_disjoint_disj:
   "(x , y \<triangleright> (\<sigma>1::('a::heap_sep_algebra, 'a::heap_sep_algebra)prod,\<sigma>2))  \<Longrightarrow>
     (\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')\<Longrightarrow>   
    (fst (fst x) ##  fst \<sigma>') \<and> (fst (fst y) ## fst \<sigma>')
    \<and> (snd (fst x) ##  snd \<sigma>') \<and> (snd (fst y) ##  snd \<sigma>')
   \<and> (fst (snd x) ##  fst \<sigma>'') \<and> (fst (snd y) ## fst \<sigma>'')
   \<and> (snd (snd x) ##  snd \<sigma>'') \<and> (snd (snd y) ## snd \<sigma>'')
   "
proof -
 assume a1:"(x, y \<triangleright> (\<sigma>1,\<sigma>2))" 
  then have descomp_sigma:
       "\<sigma>1 = fst x + fst y \<and> \<sigma>2 = snd x + snd y \<and> 
        fst x ## fst y \<and> snd x ## snd y" 
     by (simp add: tern_rel_def plus_prod_def sep_disj_prod_def)
  then have sep_comp:"fst (fst x)## fst (fst y) \<and> snd (fst x) ## snd (fst y) \<and>
             fst (snd x)## fst (snd y) \<and> snd (snd x) ## snd (snd y)"
     by (simp add: tern_rel_def plus_prod_def sep_disj_prod_def)   
  assume a2: "(\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')"
  then have  " (fst (fst x + fst y) ##  fst \<sigma>') 
    \<and> (snd (fst x + fst y) ##  snd \<sigma>')
   \<and> ((fst (snd x + snd y)) ##  fst \<sigma>'')
   \<and> ((snd (snd x + snd y)) ##  snd \<sigma>'')
   " using a1 a2 sep_tran_disjoint_disj1 by blast
  then have disjall:" ((fst (fst x)) + (fst (fst y)) ##  fst \<sigma>') 
    \<and> (snd (fst x) + snd( fst y) ##  snd \<sigma>')
   \<and> ((fst (snd x) + fst (snd y)) ##  fst \<sigma>'')
   \<and> ((snd (snd x) + snd (snd y)) ##  snd \<sigma>'')
   " by (simp add: plus_prod_def)
 then show "(fst (fst x) ##  fst \<sigma>') \<and> (fst (fst y) ## fst \<sigma>')
    \<and> (snd (fst x) ##  snd \<sigma>') \<and> (snd (fst y) ##  snd \<sigma>')
   \<and> (fst (snd x) ##  fst \<sigma>'') \<and> (fst (snd y) ## fst \<sigma>'')
   \<and> (snd (snd x) ##  snd \<sigma>'') \<and> (snd (snd y) ## snd \<sigma>'')"
       using sep_comp sep_add_disjD by metis
qed

lemma disj_union_dist1: "(\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2') \<Longrightarrow>
                        ((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>'')\<triangleright> (\<sigma>1',\<sigma>2'))"
unfolding tern_rel_def
by (simp add: plus_prod_def sep_disj_prod_def)

lemma disj_union_dist2: "((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>'')\<triangleright> (\<sigma>1',\<sigma>2')) \<Longrightarrow> 
                         (\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')"
unfolding tern_rel_def
by (simp add: plus_prod_def sep_disj_prod_def)


lemma disj_union_dist: "((\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')) = 
                        ((\<sigma>1,\<sigma>2),(\<sigma>',\<sigma>'')\<triangleright> (\<sigma>1',\<sigma>2'))"
using disj_union_dist1 disj_union_dist2 by blast


lemma sep_tran_eq_y':
    "(x , y \<triangleright> (\<sigma>1::('a::heap_sep_algebra, 'a::heap_sep_algebra)prod,\<sigma>2))  \<Longrightarrow>
     (\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')\<Longrightarrow>      
     \<exists>x' y'. (x' , y' \<triangleright> (\<sigma>1',\<sigma>2')) \<and> (fst y'=snd y')"
proof-
  assume a1:"(x, y \<triangleright> (\<sigma>1,\<sigma>2))" 
  then have descomp_sigma:"\<sigma>1 = fst x + fst y \<and> \<sigma>2 = snd x + snd y \<and> fst x ## fst y \<and> snd x ## snd y" 
     by (simp add: tern_rel_def plus_prod_def sep_disj_prod_def)
  assume a2: "(\<sigma>1 , \<sigma>'\<triangleright> \<sigma>1') \<and> (\<sigma>2 , \<sigma>''\<triangleright> \<sigma>2')"  
  then have "(( fst x + fst y), \<sigma>'\<triangleright> \<sigma>1') \<and> ((snd x + snd y), \<sigma>''\<triangleright> \<sigma>2')"
  using descomp_sigma by auto  
  have descomp_sigma1':"fst \<sigma>1' = fst \<sigma>1 + fst \<sigma>' \<and> 
                            snd \<sigma>1' = snd \<sigma>1 + snd \<sigma>' \<and>
                            fst \<sigma>1 ## fst \<sigma>' \<and> snd \<sigma>1 ## snd \<sigma>'" using a2
    by (auto simp add: tern_rel_def plus_prod_def sep_disj_prod_def)
   have descomp_sigma1':"fst \<sigma>2' = fst \<sigma>2 + fst \<sigma>'' \<and> 
                            snd \<sigma>2' = snd \<sigma>2 + snd \<sigma>'' \<and>
                            fst \<sigma>2 ## fst \<sigma>'' \<and> snd \<sigma>2 ## snd \<sigma>''" 
    using a2
    by (auto simp add: tern_rel_def plus_prod_def sep_disj_prod_def)
  then show "\<exists>x' y'. (x' , y'\<triangleright>(\<sigma>1',\<sigma>2'))  \<and> (fst y'=snd y')"
    by (metis (no_types) eq_fst_iff eq_snd_iff sep_add_zero tern_rel_def sep_disj_zero zero_prod_def)       
qed 


lemma sep_dis_con_eq:
  "x ## y \<and> (h::('a::sep_algebra, 'a::sep_algebra)prod) = x + y \<Longrightarrow> 
   x' ## y' \<and> h = x' + y' \<Longrightarrow> 
   x+y=x'+y'"
by simp

(*
instantiation prod::(heap_sep_algebra_labelled_sequents, heap_sep_algebra_labelled_sequents) heap_sep_algebra_labelled_sequents
begin
instance proof qed  
end
*)

end
