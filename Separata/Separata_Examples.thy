(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory Separata_Examples
imports Main Separata_Pointers 
begin

section {* Some examples. *}

text {* In the sequel we show two proofs for each lemma. 
One with separata and the other one without (if sledgehammer could find it). *}

text {* Let's prove something that abstract separation logic provers struggle to prove. 
This can be proved easily in Isabelle, proof found by Sledgehammer. *}
lemma fm_hard: "((sep_empty imp (p0 \<longrightarrow>* (((p0 ** (p0 \<longrightarrow>* p1)) ** (not p1)) \<longrightarrow>* 
 (p0 ** (p0 ** ((p0 \<longrightarrow>* p1) ** (not p1))))))) imp ((((sep_empty ** p0) ** 
 (p0 ** ((p0 \<longrightarrow>* p1) ** (not p1)))) imp (((p0 ** p0) ** (p0 \<longrightarrow>* p1)) ** 
 (not p1))) ** sep_empty)) h"
by (simp add: semigroup.assoc sep.mult.semigroup_axioms)

lemma "((sep_empty imp (p0 \<longrightarrow>* (((p0 ** (p0 \<longrightarrow>* p1)) ** (not p1)) \<longrightarrow>* 
 (p0 ** (p0 ** ((p0 \<longrightarrow>* p1) ** (not p1))))))) imp ((((sep_empty ** p0) ** 
 (p0 ** ((p0 \<longrightarrow>* p1) ** (not p1)))) imp (((p0 ** p0) ** (p0 \<longrightarrow>* p1)) ** 
 (not p1))) ** sep_empty)) h"
by separata

text {* The following formula can only be proved in partial-deterministic 
separation algebras. 
Sledgehammer took a rather long time to find a proof. *}

lemma "(((not (sep_true \<longrightarrow>* (not sep_empty))) ** 
 (not (sep_true \<longrightarrow>* (not sep_empty)))) imp 
 (not (sep_true \<longrightarrow>* (not sep_empty)))) 
(h::'a::heap_sep_algebra)"
by separata

text {* The following is the axiom of indivisible unit. 
Sledgehammer finds a proof easily. *}

lemma ax_iu: "((sep_empty and (A ** B)) imp A) 
(h::'a::heap_sep_algebra)"
by (metis sep_add_ind_unit sep_conj_def sep_empty_def)

lemma "((sep_empty and (A ** B)) imp A) 
(h::'a::heap_sep_algebra)"
by separata

text {* Below are benchmark formulae drawn from Park et al.'s 
BBI paper. *}

text {* Sledgehammer fails to find a proof in 300s for this one. *}
lemma "(not (((A ** (C \<longrightarrow>* (not ((not (A \<longrightarrow>* B)) ** C)))) and (not B)) ** C)) 
(h::'a::heap_sep_algebra)"
by separata 

text {* Sledgehammer finds a proof easily. *}

lemma "((sep_empty \<longrightarrow>* (not ((not A) ** sep_empty))) imp A) 
(h::'a::heap_sep_algebra)"
using sep_implD by force

lemma "((sep_empty \<longrightarrow>* (not ((not A) ** sep_empty))) imp A) 
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof in 46 seconds. *}

lemma "(A imp (not ((not (A ** B)) and (not (A ** (not B)))))) 
(h::'a::heap_sep_algebra)"
by (smt sep_conj_impl sep_conj_sep_emptyI sep_empty_def)

lemma "(A imp (not ((not (A ** B)) and (not (A ** (not B)))))) 
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer easily finds a proof. *}

lemma "((sep_empty and A) imp (A ** A)) 
(h::'a::heap_sep_algebra)"
  by (metis sep_add_zero sep_conj_def sep_disj_zero sep_empty_def)

lemma "((sep_empty and A) imp (A ** A)) 
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer fails to find a proof in 300s. *}

lemma "(not (((A ** (C \<longrightarrow>* (not ((not (A \<longrightarrow>* B)) ** C)))) and (not B)) ** C)) 
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "((sep_empty \<longrightarrow>* (not ((not A) ** sep_empty))) imp A) 
(h::'a::heap_sep_algebra)"
using sep_implD by force

lemma "((sep_empty \<longrightarrow>* (not ((not A) ** sep_empty))) imp A) 
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "(sep_empty imp ((A ** B) \<longrightarrow>* (B ** A))) 
(h::'a::heap_sep_algebra)"
by (metis abel_semigroup.commute sep.mult.abel_semigroup_axioms sep_conj_empty' sep_conj_sep_impl)

lemma "(sep_empty imp ((A ** B) \<longrightarrow>* (B ** A))) 
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer takes a while to find a proof, although the proof is by smt and is fast. *}

lemma "(sep_empty imp ((A ** (B and C)) \<longrightarrow>* ((A ** B) and (A ** C)))) 
(h::'a::heap_sep_algebra)"
  by (smt lspasl_empl_der lspasl_eq_der2 lspasl_magicr_der lspasl_starl_eq)

lemma "(sep_empty imp ((A ** (B and C)) \<longrightarrow>* ((A ** B) and (A ** C)))) 
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer takes a long time to find a smt proof, but the smt proves it quickly. *}

lemma "(sep_empty imp ((A \<longrightarrow>* (B imp C)) \<longrightarrow>* ((A \<longrightarrow>* B) imp (A \<longrightarrow>* C))))
(h::'a::heap_sep_algebra)"
by (smt sep_add_zero_sym sep_empty_def sep_implD sep_implI)

lemma "(sep_empty imp ((A \<longrightarrow>* (B imp C)) \<longrightarrow>* ((A \<longrightarrow>* B) imp (A \<longrightarrow>* C))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof quickly. *}

lemma "(sep_empty imp (((A imp B) \<longrightarrow>* ((A \<longrightarrow>* A) imp A)) imp (A \<longrightarrow>* A)))
(h::'a::heap_sep_algebra)"
by (simp add: sep_empty_def sep_impl_def)

lemma "(sep_empty imp (((A imp B) \<longrightarrow>* ((A \<longrightarrow>* A) imp A)) imp (A \<longrightarrow>* A)))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds proofs in a while. *}

lemma "((A \<longrightarrow>* B) and (sep_true ** (sep_empty and A)) imp B)
(h::'a::heap_sep_algebra)"
by (metis (no_types, lifting) sep_add_ac(2) sep_add_zero_sym sep_conjD sep_empty_def sep_implD)

lemma "((A \<longrightarrow>* B) and (sep_true ** (sep_empty and A)) imp B)
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds proofs easily. *}

lemma "((sep_empty \<longrightarrow>* (not ((not A) ** sep_true))) imp A)
(h::'a::heap_sep_algebra)"
by (metis sep_add_zero sep_conj_sep_true sep_disj_zero sep_empty_zero sep_implE)

lemma "((sep_empty \<longrightarrow>* (not ((not A) ** sep_true))) imp A)
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer takes a while to find a proof. *}

lemma "(not ((A \<longrightarrow>* (not (A ** B))) and (((not A) \<longrightarrow>* (not B)) and B)))
(h::'a::heap_sep_algebra)"
by (metis sep_add_zero sep_conjI sep_conj_commuteI sep_disj_zero sep_implE)

lemma "(not ((A \<longrightarrow>* (not (A ** B))) and (((not A) \<longrightarrow>* (not B)) and B)))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer takes a long time to find a smt proof. *}

lemma "(sep_empty imp ((A \<longrightarrow>* (B \<longrightarrow>* C)) \<longrightarrow>* ((A ** B) \<longrightarrow>* C)))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds proofs easily. *}

lemma "(sep_empty imp ((A  **  (B ** C)) \<longrightarrow>* ((A ** B) ** C)))
(h::'a::heap_sep_algebra)"
  by (metis sep.left_neutral sep_conj_assoc sep_conj_sep_impl)


lemma "(sep_empty imp ((A  **  (B ** C)) \<longrightarrow>* ((A ** B) ** C)))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds proofs in a few seconds. *}

lemma "(sep_empty imp ((A ** ((B \<longrightarrow>* D) ** C)) \<longrightarrow>* ((A ** (B \<longrightarrow>* D)) ** C)))
(h::'a::heap_sep_algebra)"
by (metis semigroup.assoc sep.left_neutral sep.mult.semigroup_axioms sep_conj_sep_impl)

lemma "(sep_empty imp ((A ** ((B \<longrightarrow>* D) ** C)) \<longrightarrow>* ((A ** (B \<longrightarrow>* D)) ** C)))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer fails to find a proof in 300s. *}

lemma "(not (((A \<longrightarrow>* (not ((not (D \<longrightarrow>* (not (A ** (C ** B))))) ** A))) and C) ** (D and (A ** B))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer takes a while to find a proof. *}

lemma "(not ((C ** (D ** E)) and ((A \<longrightarrow>* (not (not (B \<longrightarrow>* not (D ** (E ** C))) ** A))) ** 
(B and (A ** sep_true)))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer fails to find a proof in 300s. *}

lemma "(not (((A \<longrightarrow>* (not ((not (D \<longrightarrow>* (not ((C ** E) ** (B ** A))))) ** A))) and C) ** (D and (A ** (B ** E)))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "((A ** (B ** (C ** (D ** E)))) imp (E ** (B ** (A ** (C ** D)))))
(h::'a::heap_sep_algebra)"
by (simp add: abel_semigroup.commute sep.mult.abel_semigroup_axioms sep.mult.left_commute)

lemma "((A ** (B ** (C ** (D ** E)))) imp (E ** (B ** (A ** (C ** D)))))
(h::'a::heap_sep_algebra)"
by separata

lemma "((A ** (B ** (C ** (D ** (E ** (F ** G)))))) imp (G ** (E ** (B ** (A ** (C ** (D ** F)))))))
(h::'a::heap_sep_algebra)"
by (simp add: sep.mult.left_commute sep.mult_commute)

lemma "((A ** (B ** (C ** (D ** (E ** (F ** G)))))) imp (G ** (E ** (B ** (A ** (C ** (D ** F)))))))
(h::'a::heap_sep_algebra)"

by separata

text {* Sledgehammer finds a proof in a few seconds. *}

lemma "(sep_empty imp ((A ** ((B \<longrightarrow>* E) ** (C ** D))) \<longrightarrow>* ((A ** D) ** (C ** (B \<longrightarrow>* E)))))
(h::'a::heap_sep_algebra)"
by (metis (no_types, lifting) sep.left_neutral sep.mult_assoc sep.mult_commute sep_conj_sep_impl)

lemma "(sep_empty imp ((A ** ((B \<longrightarrow>* E) ** (C ** D))) \<longrightarrow>* ((A ** D) ** (C ** (B \<longrightarrow>* E)))))
(h::'a::heap_sep_algebra)"
by separata

text {* This is the odd BBI formula that I personally can't 
prove using any other methods. I only know of a derivation in 
my labelled sequent calculus for BBI.  
Sledgehammer takes a while to find a proof. *}

lemma "(not (sep_empty and A and (B ** (not (C \<longrightarrow>* (sep_empty imp A))))))
(h::'a::heap_sep_algebra)"
by (metis (no_types, lifting) sep_conjD sep_empty_def sep_implI)

lemma "(not (sep_empty and A and (B ** (not (C \<longrightarrow>* (sep_empty imp A))))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "((((sep_true imp p0) imp ((p0 ** p0) \<longrightarrow>* ((sep_true imp p0) ** (p0 ** p0)))) imp 
(p1 \<longrightarrow>* (((sep_true imp p0) imp ((p0 ** p0) \<longrightarrow>* (((sep_true imp p0) ** p0) ** p0))) ** p1))))
(h::'a::heap_sep_algebra)"
by (metis (no_types, lifting) sep_conj_assoc sep_conj_def sep_implI)

lemma "((((sep_true imp p0) imp ((p0 ** p0) \<longrightarrow>* ((sep_true imp p0) ** (p0 ** p0)))) imp 
(p1 \<longrightarrow>* (((sep_true imp p0) imp ((p0 ** p0) \<longrightarrow>* (((sep_true imp p0) ** p0) ** p0))) ** p1))))
(h::'a::heap_sep_algebra)"
by separata

text {* The following are some randomly generated BBI formulae. *}

text {* Sledgehammer finds a proof easily. *}

lemma "((((p1 \<longrightarrow>*   p3) \<longrightarrow>*   (p5 \<longrightarrow>*   p2)) imp   ((((p7 **   p4) and   (p3 \<longrightarrow>*   p2)) imp   
((p7 **   p4) and   (p3 \<longrightarrow>*   p2))) \<longrightarrow>*   (((p1 \<longrightarrow>*   p3) \<longrightarrow>*   (p5 \<longrightarrow>*   p2)) **   
(((p4 **   p7) and   (p3 \<longrightarrow>*   p2)) imp   ((p4 **   p7) and   (p3 \<longrightarrow>*   p2)))))))
(h::'a::heap_sep_algebra)"
by (simp add: sep_conj_sep_impl)

lemma "((((p1 \<longrightarrow>*   p3) \<longrightarrow>*   (p5 \<longrightarrow>*   p2)) imp   ((((p7 **   p4) and   (p3 \<longrightarrow>*   p2)) imp   
((p7 **   p4) and   (p3 \<longrightarrow>*   p2))) \<longrightarrow>*   (((p1 \<longrightarrow>*   p3) \<longrightarrow>*   (p5 \<longrightarrow>*   p2)) **   
(((p4 **   p7) and   (p3 \<longrightarrow>*   p2)) imp   ((p4 **   p7) and   (p3 \<longrightarrow>*   p2)))))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "(((((p1 \<longrightarrow>*   (p0 imp   sep_false )) imp   sep_false ) imp   (((p1 imp   sep_false ) imp   
((p0 **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1))) \<longrightarrow>*   ((p1 imp   sep_false ) **   
(p0 **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1)))))) imp   sep_false )) imp   
(((p1 imp   sep_false ) imp   ((p0 **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1))) \<longrightarrow>*   
((p0 **   (p1 imp   sep_false )) **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1))))) imp   
(p1 \<longrightarrow>*   (p0 imp   sep_false )))))
(h::'a::heap_sep_algebra)"
by (metis sep.mult_commute sep_conj_assoc)

lemma "(((((p1 \<longrightarrow>*   (p0 imp   sep_false )) imp   sep_false ) imp   (((p1 imp   sep_false ) imp   
((p0 **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1))) \<longrightarrow>*   ((p1 imp   sep_false ) **   
(p0 **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1)))))) imp   sep_false )) imp   
(((p1 imp   sep_false ) imp   ((p0 **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1))) \<longrightarrow>*   
((p0 **   (p1 imp   sep_false )) **   ((p1 imp   sep_false ) \<longrightarrow>*   (p4 \<longrightarrow>*   p1))))) imp   
(p1 \<longrightarrow>*   (p0 imp   sep_false )))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "(((p0 imp   sep_false ) imp   ((p1 **   p0) \<longrightarrow>*   (p1 **   ((p0 imp   sep_false ) **   
p0)))) imp   ((p0 imp   sep_false ) imp   ((p1 **   p0) \<longrightarrow>*   ((p1 **   p0) **   (p0 imp   
sep_false )))))
(h::'a::heap_sep_algebra)"
by (metis sep.mult_commute sep_conj_assoc)

lemma "(((p0 imp   sep_false ) imp   ((p1 **   p0) \<longrightarrow>*   (p1 **   ((p0 imp   sep_false ) **   
p0)))) imp   ((p0 imp   sep_false ) imp   ((p1 **   p0) \<longrightarrow>*   ((p1 **   p0) **   (p0 imp   
sep_false )))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof in a while. *}

lemma "(sep_empty  imp   ((((p4 **   p1) \<longrightarrow>*   ((p8 **   sep_empty ) \<longrightarrow>*   p0)) imp   
(p1 \<longrightarrow>*   (p1 **   ((p4 **   p1) \<longrightarrow>*   ((p8 **   sep_empty ) \<longrightarrow>*   p0))))) \<longrightarrow>*   
(((p4 **   p1) \<longrightarrow>*   ((p8 **   sep_empty ) \<longrightarrow>*   p0)) imp   (p1 \<longrightarrow>*   (((p1 **   p4) \<longrightarrow>*   
((p8 **   sep_empty ) \<longrightarrow>*   p0)) **   p1)))))
(h::'a::heap_sep_algebra)"
by (simp add: abel_semigroup.commute sep.mult.abel_semigroup_axioms sep_empty_def sep_implI)

lemma "(sep_empty  imp   ((((p4 **   p1) \<longrightarrow>*   ((p8 **   sep_empty ) \<longrightarrow>*   p0)) imp   
(p1 \<longrightarrow>*   (p1 **   ((p4 **   p1) \<longrightarrow>*   ((p8 **   sep_empty ) \<longrightarrow>*   p0))))) \<longrightarrow>*   
(((p4 **   p1) \<longrightarrow>*   ((p8 **   sep_empty ) \<longrightarrow>*   p0)) imp   (p1 \<longrightarrow>*   (((p1 **   p4) \<longrightarrow>*   
((p8 **   sep_empty ) \<longrightarrow>*   p0)) **   p1)))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "((((p3 imp   (p0 \<longrightarrow>*   (p3 **   p0))) imp   sep_false ) imp   (p1 imp   sep_false )) imp   
(p1 imp   (p3 imp   (p0 \<longrightarrow>*   (p0 **   p3)))))
(h::'a::heap_sep_algebra)"
by (metis sep.mult_commute)

lemma "((((p3 imp   (p0 \<longrightarrow>*   (p3 **   p0))) imp   sep_false ) imp   (p1 imp   sep_false )) imp   
(p1 imp   (p3 imp   (p0 \<longrightarrow>*   (p0 **   p3)))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof in a few seconds. *}

lemma "((p7 \<longrightarrow>*   (p4 **   (p6 \<longrightarrow>*   p1))) imp   ((p4 imp   (p1 \<longrightarrow>*   ((sep_empty  **   
p1) **   p4))) \<longrightarrow>*   ((p1 imp   (p4 \<longrightarrow>*   (p4 **   (sep_empty  **   p1)))) **   (p7 \<longrightarrow>*   
((p6 \<longrightarrow>*   p1) **   p4)))))
(h::'a::heap_sep_algebra)"
by (smt abel_semigroup.commute monoid.left_neutral sep.monoid_axioms sep.mult.abel_semigroup_axioms sep_conj_impl sep_conj_sep_impl)

lemma "((p7 \<longrightarrow>*   (p4 **   (p6 \<longrightarrow>*   p1))) imp   ((p4 imp   (p1 \<longrightarrow>*   ((sep_empty  **   
p1) **   p4))) \<longrightarrow>*   ((p1 imp   (p4 \<longrightarrow>*   (p4 **   (sep_empty  **   p1)))) **   (p7 \<longrightarrow>*   
((p6 \<longrightarrow>*   p1) **   p4)))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "(((p2 imp   p0) imp   ((p0 **   sep_true ) \<longrightarrow>*   (p0 **   (sep_true  **   
(p2 imp   p0))))) imp   ((p2 imp   p0) imp   ((sep_true  **   p0) \<longrightarrow>*   
(p0 **   ((p2 imp   p0) **   sep_true )))))
(h::'a::heap_sep_algebra)"
by (simp add: abel_semigroup.commute sep.mult.abel_semigroup_axioms)

lemma "(((p2 imp   p0) imp   ((p0 **   sep_true ) \<longrightarrow>*   (p0 **   (sep_true  **   
(p2 imp   p0))))) imp   ((p2 imp   p0) imp   ((sep_true  **   p0) \<longrightarrow>*   
(p0 **   ((p2 imp   p0) **   sep_true )))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof easily. *}

lemma "((sep_empty  imp   ((p1 \<longrightarrow>*   (((p2 imp   sep_false ) **   p0) **   p8)) \<longrightarrow>*   
(p1 \<longrightarrow>*   ((p2 imp   sep_false ) **   (p0 **   p8))))) imp   ((p0 **   sep_empty ) \<longrightarrow>*   
((sep_empty  imp   ((p1 \<longrightarrow>*   ((p0 **   (p2 imp   sep_false )) **   p8)) \<longrightarrow>*   (p1 \<longrightarrow>*   
((p2 imp   sep_false ) **   (p0 **   p8))))) **   (p0 **   sep_empty ))))
(h::'a::heap_sep_algebra)"
by (metis (no_types, lifting) sep.mult_commute sep_conjI sep_implI)

lemma "((sep_empty  imp   ((p1 \<longrightarrow>*   (((p2 imp   sep_false ) **   p0) **   p8)) \<longrightarrow>*   
(p1 \<longrightarrow>*   ((p2 imp   sep_false ) **   (p0 **   p8))))) imp   ((p0 **   sep_empty ) \<longrightarrow>*   
((sep_empty  imp   ((p1 \<longrightarrow>*   ((p0 **   (p2 imp   sep_false )) **   p8)) \<longrightarrow>*   (p1 \<longrightarrow>*   
((p2 imp   sep_false ) **   (p0 **   p8))))) **   (p0 **   sep_empty ))))
(h::'a::heap_sep_algebra)"
by separata

text {* Sledgehammer finds a proof in a while. *}

lemma "((p0 \<longrightarrow>*   sep_empty ) imp   ((sep_empty  imp   ((sep_empty  **   ((((p8 **   p7) **   
(p8 imp   p4)) \<longrightarrow>*   p8) **   (p2 **   p1))) \<longrightarrow>*   (p2 **   (((p7 **   ((p8 imp   p4) **   
p8)) \<longrightarrow>*   p8) **   p1)))) \<longrightarrow>*   ((sep_empty  imp   (((((p7 **   (p8 **   (p8 imp   p4))) \<longrightarrow>*   
p8) **   sep_empty ) **   (p1 **   p2)) \<longrightarrow>*   (((p7 **   ((p8 imp   p4) **   p8)) \<longrightarrow>*   p8) **   
(p1 **   p2)))) **   (p0 \<longrightarrow>*   sep_empty ))))
(h::'a::heap_sep_algebra)"
  by (smt lspasl_magicr_der lspasl_starr_eq sep_conj_commute sep_conj_left_commute)

lemma "((p0 \<longrightarrow>*   sep_empty ) imp   ((sep_empty  imp   ((sep_empty  **   ((((p8 **   p7) **   
(p8 imp   p4)) \<longrightarrow>*   p8) **   (p2 **   p1))) \<longrightarrow>*   (p2 **   (((p7 **   ((p8 imp   p4) **   
p8)) \<longrightarrow>*   p8) **   p1)))) \<longrightarrow>*   ((sep_empty  imp   (((((p7 **   (p8 **   (p8 imp   p4))) \<longrightarrow>*   
p8) **   sep_empty ) **   (p1 **   p2)) \<longrightarrow>*   (((p7 **   ((p8 imp   p4) **   p8)) \<longrightarrow>*   p8) **   
(p1 **   p2)))) **   (p0 \<longrightarrow>*   sep_empty ))))
(h::'a::heap_sep_algebra)"
by separata

text {* Let's try some examples in real-life applications. 
Below are lemmas used in the seL4 project. *}

text {* From Sep\_Tactic\_Helpers.thy: *}

lemma "((Q \<longrightarrow>* R) \<and>* Q) h \<Longrightarrow> R (h::'a::heap_sep_algebra)"
using sep_conj_sep_impl2 by auto

lemma "((Q \<longrightarrow>* R) \<and>* Q) h \<Longrightarrow> R (h::'a::heap_sep_algebra)"
by separata

lemma "((Q \<longrightarrow>* R) \<and>* Q \<and>* R') s \<Longrightarrow> (R \<and>* R') (s::'a::heap_sep_algebra)"
by (smt semigroup.assoc sep.mult.semigroup_axioms sep_conj_impl1 sep_conj_sep_impl2)

lemma "((Q \<longrightarrow>* R) \<and>* Q \<and>* R') s \<Longrightarrow> (R \<and>* R') (s::'a::heap_sep_algebra)"
by separata

lemma "(sep_empty \<longrightarrow>* P) s \<Longrightarrow> P (s::'a::heap_sep_algebra)"
using sep_conj_sep_emptyI sep_conj_sep_impl2 by blast

lemma "(sep_empty \<longrightarrow>* P) s \<Longrightarrow> P (s::'a::heap_sep_algebra)"
by separata

lemma "(sep_empty \<longrightarrow>* P) s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> Q (s::'a::heap_sep_algebra)"
using sep_implD by force

lemma "(sep_empty \<longrightarrow>* P) s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> Q (s::'a::heap_sep_algebra)"
by separata

lemma " P s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> (sep_empty \<longrightarrow>* Q) (s::'a::heap_sep_algebra)"
by (metis sep_add_zero sep_empty_def sep_implI)

lemma " P s \<Longrightarrow> (\<And>s. P s \<Longrightarrow> Q s) \<Longrightarrow> (sep_empty \<longrightarrow>* Q) (s::'a::heap_sep_algebra)"
by separata

text {* From Sep\_ImpI.thy: *}

lemma "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by (smt abel_semigroup.commute abel_semigroup.left_commute sep.mult.abel_semigroup_axioms sep_conj_sep_impl sep_conj_sep_impl2)

lemma "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by separata

text {* The following formulae from Sep\_Attribs.thy have quantifiers over 
the heap s. We extend separata with simple modalities to solve this 
a la our APLAS2016 paper. *}

lemma "\<lbrakk>(\<And>s. (P \<and>* Q) s \<longrightarrow> R s); P s \<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by (simp add: sep_conj_sep_impl)

lemma "\<lbrakk>(\<And>s. (P \<and>* Q) s \<longrightarrow> R s); P s \<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by separata

lemma "\<lbrakk>\<And>s. P s \<longrightarrow> (Q \<and>* T) s; (P \<and>* (Q \<longrightarrow>* R)) s \<rbrakk> \<Longrightarrow> (T \<and>* R) (s::'a::heap_sep_algebra)"
by (smt abel_semigroup.commute sep.mult.abel_semigroup_axioms sep_conj_impl sep_conj_left_commute sep_conj_sep_impl sep_conj_sep_impl2)

lemma "\<lbrakk>\<And>s. P s \<longrightarrow> (Q \<and>* T) s; (P \<and>* (Q \<longrightarrow>* R)) s \<rbrakk> \<Longrightarrow> (T \<and>* R) (s::'a::heap_sep_algebra)"
by separata

text {* From Sep\_Cancel.thy: *}

lemma "\<lbrakk>(P \<and>* F) s; \<And>s. (Q \<and>* P \<and>* F) s \<longrightarrow> R s\<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by (simp add: sep_conj_commuteI sep_conj_sep_impl)

lemma "\<lbrakk>(P \<and>* F) s; \<And>s. (Q \<and>* P \<and>* F) s \<longrightarrow> R s\<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by separata

lemma "(P \<longrightarrow>* P') s \<Longrightarrow> (\<And>s. ((P \<longrightarrow>* P') \<and>* Q) s \<longrightarrow> (Q') s) \<Longrightarrow> (Q \<longrightarrow>* Q') (s::'a::heap_sep_algebra)"
by (simp add: sep_conj_sep_impl)

lemma "(P \<longrightarrow>* P') s \<Longrightarrow> (\<And>s. ((P \<longrightarrow>* P') \<and>* Q) s \<longrightarrow> (Q') s) \<Longrightarrow> (Q \<longrightarrow>* Q') (s::'a::heap_sep_algebra)"
by separata

lemma "P s \<Longrightarrow> (\<And>s. (P \<and>* Q) s \<longrightarrow> (P \<and>* R) s) \<Longrightarrow> (Q \<longrightarrow>* P \<and>* R) (s::'a::heap_sep_algebra)"
by (simp add: sep_conj_sep_impl)

lemma "P s \<Longrightarrow> (\<And>s. (P \<and>* Q) s \<longrightarrow> (P \<and>* R) s) \<Longrightarrow> (Q \<longrightarrow>* P \<and>* R) (s::'a::heap_sep_algebra)"
by separata

lemma "(\<And>s. T s = (Q \<and>* R) s) \<Longrightarrow> (P \<longrightarrow>* T) s \<Longrightarrow> (P \<longrightarrow>* Q \<and>* R) (s::'a::heap_sep_algebra)"
by presburger

lemma "(\<And>s. T s = (Q \<and>* R) s) \<Longrightarrow> (P \<longrightarrow>* T) s \<Longrightarrow> (P \<longrightarrow>* Q \<and>* R) (s::'a::heap_sep_algebra)"
by separata

text {* From Sep\_MP.thy: *}

lemma "((Q \<longrightarrow>* R) \<and>* Q') s \<Longrightarrow> (\<And>s. Q' s \<Longrightarrow> Q s) \<Longrightarrow> R (s::'a::heap_sep_algebra)"
using sep_conjD sep_implD by blast

lemma "((Q \<longrightarrow>* R) \<and>* Q') s \<Longrightarrow> (\<And>s. Q' s \<Longrightarrow> Q s) \<Longrightarrow> R (s::'a::heap_sep_algebra)"
by separata

lemma "\<lbrakk>((Q \<longrightarrow>* R) \<and>* Q' \<and>* R') s; (\<And>s. Q' s \<Longrightarrow> Q s)\<rbrakk> \<Longrightarrow> (R \<and>* R') (s::'a::heap_sep_algebra)"
by (smt sep_add_assoc sep_conj_def sep_disj_addD1 sep_disj_addD2 sep_disj_addI1 sep_implD)

lemma "\<lbrakk>((Q \<longrightarrow>* R) \<and>* Q' \<and>* R') s; (\<And>s. Q' s \<Longrightarrow> Q s)\<rbrakk> \<Longrightarrow> (R \<and>* R') (s::'a::heap_sep_algebra)"
by separata

lemma "((P \<longrightarrow>* Q) \<and>* R) s \<Longrightarrow> (\<And>s. T s = R s) ==> ((P \<longrightarrow>* Q) \<and>* T) (s::'a::heap_sep_algebra)"
using sep_conj_impl by blast

lemma "((P \<longrightarrow>* Q) \<and>* R) s \<Longrightarrow> (\<And>s. T s = R s) ==> ((P \<longrightarrow>* Q) \<and>* T) (s::'a::heap_sep_algebra)"
by separata

lemma "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by (smt semigroup.assoc sep.mult.semigroup_axioms sep_conj_sep_impl sep_conj_sep_impl2)

lemma "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) (s::'a::heap_sep_algebra)"
by separata

lemma "((Q r \<longrightarrow>* R r) \<and>* Q r) (sep_lift s) \<Longrightarrow> R r ((sep_lift s)::'a::heap_sep_algebra)"
by (metis (full_types) sep_conjD sep_implE)

lemma "((Q r \<longrightarrow>* R r) \<and>* Q r) (sep_lift s) \<Longrightarrow> R r ((sep_lift s)::'a::heap_sep_algebra)"
by separata

text {* From Sep\_ImpI.thy: *}

lemma "(\<And>s. T s = Q s) \<Longrightarrow> ((P \<longrightarrow>* T) \<and>* R) s \<Longrightarrow> ((P \<longrightarrow>* Q) \<and>* R) (s::'a::heap_sep_algebra)"
by presburger

lemma "(\<And>s. T s = Q s) \<Longrightarrow> ((P \<longrightarrow>* T) \<and>* R) s \<Longrightarrow> ((P \<longrightarrow>* Q) \<and>* R) (s::'a::heap_sep_algebra)"
by separata

lemma "(\<And>s. T s = Q s) \<Longrightarrow> ((T \<longrightarrow>* P) \<and>* R) s \<Longrightarrow> ((Q \<longrightarrow>* P) \<and>* R) (s::'a::heap_sep_algebra)"
by presburger

lemma "(\<And>s. T s = Q s) \<Longrightarrow> ((T \<longrightarrow>* P) \<and>* R) s \<Longrightarrow> ((Q \<longrightarrow>* P) \<and>* R) (s::'a::heap_sep_algebra)"
by separata

lemma "(\<And>s. Q s \<Longrightarrow> Q' s)  \<Longrightarrow> (R \<longrightarrow>* R') s  ==>  (Q \<and>* R \<longrightarrow>* Q' \<and>* R') (s::'a::heap_sep_algebra)"
by (smt sep_add_assoc sep_add_commute sep_conj_def sep_disj_addD2 sep_disj_addI2 sep_disj_commuteI sep_impl_def) 

lemma "(\<And>s. Q s \<Longrightarrow> Q' s)  \<Longrightarrow> (R \<longrightarrow>* R') s  ==>  (Q \<and>* R \<longrightarrow>* Q' \<and>* R') (s::'a::heap_sep_algebra)" 
by separata

lemma "(\<And>s. Q s \<Longrightarrow> Q' s) \<Longrightarrow> R' s  ==>   (Q \<longrightarrow>* Q' \<and>* R') (s::'a::heap_sep_algebra)"
by (metis sep_add_commute sep_conj_def sep_disj_commuteI sep_implI)

lemma "(\<And>s. Q s \<Longrightarrow> Q' s) \<Longrightarrow> R' s  ==>   (Q \<longrightarrow>* Q' \<and>* R') (s::'a::heap_sep_algebra)"
by separata

lemma "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) (s::'a::heap_sep_algebra) "
by (smt sep_conj_assoc sep_conj_sep_impl sep_conj_sep_impl2)

lemma "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) (s::'a::heap_sep_algebra) "
by separata

lemma " (\<And>s. ((Q' \<and>* R) imp ((P \<longrightarrow>* R') \<and>* Q' \<and>* R'' )) s) \<Longrightarrow> 
((Q' \<and>* R) s \<Longrightarrow> (\<And>s. (Q' imp Q) s) \<Longrightarrow> ((P \<longrightarrow>* (Q \<and>* R')) \<and>* R'') (s::'a::heap_sep_algebra))"
by (smt sep_conj_assoc sep_conj_commute sep_conj_impl sep_conj_sep_impl sep_conj_sep_impl2)

lemma " (\<And>s. ((Q' \<and>* R) imp ((P \<longrightarrow>* R') \<and>* Q' \<and>* R'' )) s) \<Longrightarrow> 
((Q' \<and>* R) s \<Longrightarrow> (\<And>s. (Q' imp Q) s) \<Longrightarrow> ((P \<longrightarrow>* (Q \<and>* R')) \<and>* R'') (s::'a::heap_sep_algebra))"  
by (prep,try_lsfasl_boxl,(invert|struct)+)

text {* Examples that separata struggles to prove and starforce can solve it. 
Sledgehammer also couldn't find any working proof. *}

lemma "(h1,h2\<triangleright>h3) \<Longrightarrow> (h4,h5\<triangleright>h1) \<Longrightarrow> (h6,h7\<triangleright>h2) \<Longrightarrow> (h8,h9\<triangleright>h6) \<Longrightarrow> (h10,h11\<triangleright>h8) \<Longrightarrow>
(A h4) \<Longrightarrow> (B h5) \<Longrightarrow> (C h10) \<Longrightarrow> (D h11) \<Longrightarrow> (E h9) \<Longrightarrow> (F h7) \<Longrightarrow> 
(((((B ** E) ** (A ** D)) ** C) ** F) h3)"
by starforce   

lemma "(E \<and>* F \<and>* (Bar \<and>* Q \<and>* R \<longrightarrow>* B) \<and>* Bar \<and>* A \<and>* R \<and>* Q) s \<Longrightarrow> (A \<and>* F \<and>* B \<and>* E) (s::'a::heap_sep_algebra)"
by starforce
    
lemma "X \<Longrightarrow> (E \<and>* F \<and>* G \<and>* (Bar \<and>* Q \<and>* R \<longrightarrow>* B) \<and>* Bar \<and>* (G \<and>* H \<longrightarrow>* I) \<and>* H \<and>* (F \<and>* E \<longrightarrow>* Q) \<and>* A \<and>* R) s \<Longrightarrow> 
(A \<and>* B \<and>* I) (s::'a::heap_sep_algebra)"  
by starforce  
  
text {* Below are some examples with the |-> predicate. *}  

context reynolds_algebra
begin  
  
text {* Sledgehammer find a proof quickly. *}  
  
lemma "(((e1 \<mapsto> e2) and sep_empty) imp sep_false) (h)"  
by sepointer 

text {* Sledgehammer find a proof quickly. *}    
  
lemma "((e1 \<mapsto> e2) imp not ((not sep_empty) ** (not sep_empty))) (h)"
by sepointer      
  
text {* Sledgehammer find a proof quickly. *}    
  
lemma "((e1 \<mapsto> e2) ** (e3 \<mapsto> e4)) (h) \<Longrightarrow> \<not>(e1 = e3)"    
by sepointer
  
text {* Sledgehammer find a proof quickly. *}    
  
lemma "((e1 \<mapsto> e2) and (e3 \<mapsto> e4)) (h) \<Longrightarrow> (e1 = e3) \<and> (e2 = e4)"    
  by sepointer  

text {* Sledgehammer find a proof quickly, but using the lemmas we
developed in our tactics. *}     
    
lemma "(not ((x \<mapsto> y) \<longrightarrow>* not (z \<mapsto> w)) imp (x eq z) and (y eq w) and sep_empty) h"      
  by sepointer

text {* The following are benchmark formulae from Hou's APLAS paper. *}  
  
text {* Sledgehammer couldn't find proofs in 300s. *}    
  
lemma "(((sep_true \<longrightarrow>* (((k \<mapsto> cd) \<longrightarrow>* (l \<mapsto> ab)) imp (l \<mapsto> ab))) imp (l \<mapsto> ab))) h"  
by sepointer

text {* Sledgehammer find a proof quickly. *}      
  
lemma "(((EXS x2. ((EXS x1. ((x2 \<mapsto> x1) imp sep_false)) imp sep_false)) imp 
(EXS x3. (x3 \<mapsto> ab)))) h"    
by sepointer  
  
text {* Sledgehammer find a proof quickly, but using the lemmas we
developed in our tactics. *}      
  
lemma "((((sep_empty imp sep_false) imp sep_false) imp 
((EXS x1. ((x1 \<mapsto> ab) ** sep_true)) imp sep_false))) h"    
by sepointer  
    
text {* Sledgehammer couldn't find proofs in 300s. *}      
    
lemma "((((e1 \<mapsto> e2) ** not ((e3 \<mapsto> e4) ** sep_true)) and ((e3 \<mapsto> e4) ** sep_true))
 imp (e1 eq e3)) h"    
  by sepointer
    
text {* Sledgehammer finds a proof after a while. *}    
  
lemma "((not (((l1 \<mapsto> p) ** (l2 \<mapsto> q)) \<longrightarrow>* (not (l3 \<mapsto> r)))) imp
(not ((l1 \<mapsto> p) \<longrightarrow>* (not (not ((l2 \<mapsto> q) \<longrightarrow>* (not (l3 \<mapsto> r))))))))  h"
by sepointer 
  
text {* Sledgehammer finds a proof after a while. *}     
  
lemma "((not ((l1 \<mapsto> p) \<longrightarrow>* (not (not ((l2 \<mapsto> q) \<longrightarrow>* (not (l3 \<mapsto> r))))))) imp
(not (((l1 \<mapsto> p) ** (l2 \<mapsto> q)) \<longrightarrow>* (not (l3 \<mapsto> r))))) h"  
by sepointer
  
end  
  
lemma "((A ** sep_empty) imp (A ** sep_true)) (s::'a::heap_sep_algebra)"  
by separata  
      
end