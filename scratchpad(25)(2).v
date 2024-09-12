Require Import Coq.Program.Equality.
Require Import Arith. 

Section General_Results.

(*Some general results to facilitate some proofs:*)

(*sigma_proof := Given an element of a type verifying a certain proposition, builds the image of such element in the corresponding sigma type*)

Definition sigma_proof {A:Type} {Propos : A -> Prop} (a:A) (proof : Propos a) :{a:A| Propos a }.
split with a. apply proof.
Defined.

Definition convertibility {A B: Type} (proof: A = B) (a:A) (b:B): Prop.
rewrite <- proof in b.
apply (a = b).
Defined.

(*Some natural numbers base properties made defined so that they are not opaque:*)

Lemma add_0_r_bis  (n: nat) : n + 0 = n.
induction n. + reflexivity.
  + simpl. rewrite IHn; reflexivity.
Defined.

Lemma add_succ_r_bis (n m :nat) :  n + S m = S (n + m).
induction n. + simpl. reflexivity.
+ simpl. rewrite IHn. reflexivity.
Defined.

Lemma add_l_cancel_bis (n m : nat) (proof : n + m = m) : n = 0.
induction m. + rewrite (add_0_r_bis n) in proof; apply proof.
+ rewrite add_succ_r_bis in proof. inversion proof. apply (IHm H0).
Defined.

Lemma add_1_r_bis (n:nat) : n + 1 = S n.
rewrite (add_succ_r_bis n 0). rewrite add_0_r_bis . reflexivity.
Defined.

Lemma le_n_plus_trans_bis (n m p: nat) (proof : n <= m): n <= p + m.
induction p. + simpl; apply proof.
+ simpl. apply le_S ; apply IHp.
Defined.

Lemma add_assoc_bis (n m p:nat) : n + (m + p) = n + m + p.
induction n. + simpl; reflexivity.
+ simpl. rewrite IHn; reflexivity.
Defined. 

Lemma sus_0_r_bis (n:nat) : n - 0 = n.
induction n; trivial.
Defined.

Definition add_S_sus_cancel (n m:nat) : S n - S m = n - m.
simpl; reflexivity.
Defined.

Definition sus_0_id (n: nat) : n - n = 0.
induction n. + simpl. reflexivity.
+ simpl. apply IHn.
Defined.

Definition add_comm_bis (n m : nat) : n + m = m + n.
induction m. + simpl. apply add_0_r_bis.
+ simpl. rewrite <- IHm. apply add_succ_r_bis.
Defined.

(*Decidability of nat:*)

Definition pred_bis (n : nat) := match n with
  | 0 => 0
  | S p => p
  end.

Lemma pred_equality (n m : nat) (proof: n = m) : pred_bis n = pred_bis m.
rewrite proof. reflexivity.
Defined.

Lemma nat_decidability (n m : nat) : n = m \/ n <> m.
dependent induction n; destruct m.
+ left. reflexivity.
+ right. discriminate.
+ right. discriminate.
+ destruct IHn with m. - left. f_equal. apply H. - right. intro. destruct H. apply pred_equality in H0. simpl in H0. apply H0.
Defined.

Lemma pred_sus_is_sus_succ_bis (n m:nat) : pred_bis (n-m) = n - (S m).
dependent induction n. + simpl; reflexivity.
+ destruct m. - simpl. symmetry. apply sus_0_r_bis.
- simpl. apply (IHn m).
Defined.

Lemma S_pred_can_be_id (n: nat) (proof : exists p, n = S p) : S (pred_bis n) = n.
destruct proof. rewrite H. simpl; reflexivity.
Defined.

Lemma sus_lt_is_zero (n m : nat) (proof: n <= m) : n - m = 0.
induction m. + inversion proof. simpl; reflexivity. 
+ inversion proof.
* apply sus_0_id.
* rewrite <- pred_sus_is_sus_succ_bis. rewrite IHm. - simpl; reflexivity.
- apply H0.
Defined.

End General_Results.


(*PART I*)

(*This parts defined the foundations of the constructions in this work: simplices, cubes and words.*)

Section Simplices_and_Cubes_Construction.

(*There is a natural inductive construction of simplices and cubes, cf. ??? :*)

Inductive simplicial_generator:Type :=
  |simpl_base
  |simpl_plus : simplicial_generator -> simplicial_generator
  |simpl_zero : simplicial_generator -> simplicial_generator.

Inductive cubical_generator:Type :=
  |cubic_base
  |cubic_minus: cubical_generator -> cubical_generator
  |cubic_plus: cubical_generator -> cubical_generator
  |cubic_zero: cubical_generator -> cubical_generator.

(*We define some operations on simplices first:*)

(*We distinguish length, which is the distance from the base, from depth, which is the amount of zeros, representing dimension:*)

Fixpoint simplicial_generator_length (t:simplicial_generator) := match t with
  |simpl_base => 1
  |simpl_plus t' => S (simplicial_generator_length t')
  |simpl_zero t' => S (simplicial_generator_length t')
  end.

Fixpoint simplicial_generator_depth (t: simplicial_generator) := match t with
  |simpl_base => 0
  |simpl_plus t' => simplicial_generator_depth t'
  |simpl_zero t' => S (simplicial_generator_depth t')
  end.
  
(*Iteration of the plus constructor:*)

Fixpoint simpl_plus_iter (m:nat) (t: simplicial_generator) := match m with
  | 0 => t
  | S p => simpl_plus_iter p (simpl_plus t)
  end. 

(*A face map will replace a zero with a plus:*)

Fixpoint simpl_face_map_S_aux (m:nat) (s s': simplicial_generator) := match s with
  |simpl_base => s'
  |simpl_plus t => simpl_face_map_S_aux m t (simpl_plus s')
  |simpl_zero t => match m with
      | 0 => simpl_face_map_S_aux 0 t (simpl_zero s')
      | 1 => simpl_face_map_S_aux 0 t (simpl_plus s')
      | S p => simpl_face_map_S_aux p t (simpl_zero s')
    end
  end.
 
Definition simpl_face_map_S (m:nat) (s : simplicial_generator) := simpl_face_map_S_aux 0 (simpl_face_map_S_aux (S m) s simpl_base) simpl_base.

Fixpoint simpl_face_map_0_aux (m:nat) (s s': simplicial_generator) := match s with
  |simpl_base => s'
  |simpl_plus t => simpl_face_map_0_aux m t (simpl_plus s')
  |simpl_zero t => match m with
      | 0 => s'
      | S p => simpl_face_map_0_aux p t (simpl_zero s')
    end
  end.

Definition simpl_face_map_0 (s:simplicial_generator) := simpl_face_map_S_aux 0 (simpl_face_map_0_aux (pred_bis (simplicial_generator_depth s)) s simpl_base) simpl_base.

Definition simpl_face_map (m:nat) (s:simplicial_generator) := match m with
  |0 => simpl_face_map_0 s
  |S p => simpl_face_map_S p s
  end.

(*We define a special type of generator, called a principal generator, defined as an iteration of simpl_zero*)

Fixpoint principal_simplicial_generator (n:nat):= match n with
  | 0 => simpl_base
  | S p => simpl_zero (principal_simplicial_generator p)
  end.

(*We define similar operations on cubes:*)

(*Length and depth are differently initialized in the cubes, as cubic_base is meaningless as a cube*)

Fixpoint cubical_generator_length (c:cubical_generator) := match c with
  |cubic_base => 0
  |cubic_minus c' => S (cubical_generator_length c')
  |cubic_plus c' => S (cubical_generator_length c')
  |cubic_zero c' => S (cubical_generator_length c')
  end.

Fixpoint cubical_generator_depth (c: cubical_generator) := match c with
  |cubic_base => 0
  |cubic_minus c' => cubical_generator_depth c'
  |cubic_plus c' => cubical_generator_depth c'
  |cubic_zero c' => S (cubical_generator_depth c')
  end.

(*Iteration of the minus and plus constructors*)

Fixpoint cubic_minus_iter (m:nat) (c: cubical_generator) := match m with
  | 0 => c
  | S p => cubic_minus_iter p (cubic_minus c)
  end.
  
Fixpoint cubic_plus_iter (m:nat) (c: cubical_generator) := match m with
  | 0 => c
  | S p => cubic_plus_iter p (cubic_plus c)
  end.

(*Cubical faces will replace a zero with either plus or minus:*)

Fixpoint cubic_face_map_plus_aux (m:nat) (c c': cubical_generator) := match c with
  |cubic_base => c'
  |cubic_minus d => cubic_face_map_plus_aux m d (cubic_minus c')
  |cubic_plus d => cubic_face_map_plus_aux m d (cubic_plus c')
  |cubic_zero d => match m with
      | 0 => cubic_face_map_plus_aux 0 d (cubic_zero c')
      | 1 => cubic_face_map_plus_aux 0 d (cubic_plus c')
      | S p => cubic_face_map_plus_aux p d (cubic_zero c')
    end
  end.

Definition cubic_face_map_plus (m:nat) (c : cubical_generator) := cubic_face_map_plus_aux 0 (cubic_face_map_plus_aux (S m) c cubic_base) cubic_base.

Fixpoint cubic_face_map_minus_aux (m:nat) (c c': cubical_generator) := match c with
  |cubic_base => c'
  |cubic_minus d => cubic_face_map_minus_aux m d (cubic_minus c')
  |cubic_plus d => cubic_face_map_minus_aux m d (cubic_plus c')
  |cubic_zero d => match m with
      | 0 => cubic_face_map_minus_aux 0 d (cubic_zero c')
      | 1 => cubic_face_map_minus_aux 0 d (cubic_minus c')
      | S p => cubic_face_map_minus_aux p d (cubic_zero c')
    end
  end.

Definition cubic_face_map_minus (m:nat) (c : cubical_generator) := cubic_face_map_minus_aux 0 (cubic_face_map_minus_aux (S m) c cubic_base) cubic_base.

(*Cubical principal generators:*)

Fixpoint principal_cubical_generator (n : nat) := match n with
  |0 => cubic_base
  |S p => cubic_zero (principal_cubical_generator p)
  end.
  
(*An useful identity:*)  

Lemma depth_lt_length (c : cubical_generator) : cubical_generator_depth c <= cubical_generator_length c.
induction c.
+ simpl. trivial.
+ simpl. apply (le_S _ _ IHc).
+ simpl. apply (le_S _ _ IHc).
+ simpl. apply (le_n_S _ _ IHc).
Defined.

(*Some examples:*)

Compute simplicial_generator_length (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

Compute simplicial_generator_depth (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

Compute simpl_face_map 3 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

Compute simpl_face_map 0 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

Compute simpl_face_map 1 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

Compute simpl_face_map 2 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

Compute cubical_generator_length (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubical_generator_depth (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_plus 3 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_plus 0 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_plus 1 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_plus 2 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_minus 3 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_minus 0 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_minus 1 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

Compute cubic_face_map_minus 2 (cubic_zero (cubic_minus (cubic_minus (cubic_plus (cubic_zero (cubic_plus (cubic_zero cubic_base))))))).

End Simplices_and_Cubes_Construction.

Section Symbolic_Strings.

(*We give ourselves two symbols, plus and minus, with whom we create strings and operations on them:*)

Inductive symbols : Type :=
|plus
|minus.

(*We proof that the comparison of two such symbols is decidable:*)

Lemma symbols_decidable (v w: symbols) : (v = w) \/ (v <> w).
dependent destruction v; dependent destruction w.
+ left. reflexivity.
+ right. discriminate.
+ right. discriminate.
+ left. reflexivity.
Defined.

(*Strings are inductively defined dependent types, built from nat and symbols, much like vectors:*)

Inductive string : nat -> Type :=
  |Empty_string : string 0
  |cons_str : forall {n:nat} (v:symbols), string n -> string (S(n)).

(*We have a predecessor-like function for strings:*)

Definition string_tail {m:nat} (s : string m) : string (pred_bis m) := match s with
  |Empty_string => Empty_string
  |cons_str v t => t
  end.

Lemma string_tail_eq {m:nat} (s t : string m) (proof : s = t): string_tail s = string_tail t.
rewrite proof. reflexivity.
Defined.

(*We proof some similar decidability statements on strings:*)

Lemma string_divergence {m:nat} (v w: symbols)(s t: string m)(proof: v <> w) : cons_str v s <> cons_str w t. 
intro. destruct proof. injection H as H'; apply H'.
Defined.

Lemma string_divergence2 {m:nat} (v: symbols) (s t: string m)(proof : s <> t) : cons_str v s <> cons_str v t.
intro. destruct proof. apply string_tail_eq in H. simpl in H. apply H.
Defined.

Lemma string_decidable {m : nat} (s t: string m) : (s = t) \/ (s <> t).
induction s ; dependent induction t.
+ left. reflexivity.
+ assert (v = v0 \/ v <> v0). - apply symbols_decidable. 
- destruct H. * rewrite H. destruct IHs with t. ** left. rewrite H0 ; reflexivity.
** right. apply string_divergence2 ; apply H0.
* right. apply string_divergence ; apply H.
Defined.

(*A 0-string is empty; a non-zero-string can be decomposed in a symbol and a string:*)

Definition zero_string_is_empty (s:string 0) : s = Empty_string := match s with
  |Empty_string => eq_refl
  end.


Definition non_zero_string_pop {n:nat}(s: string (S n)) := match s with
  |cons_str v w => (v,w)
  end.

(*A string can be built from its pop:*)

Lemma non_zero_string_pop_identity {n:nat} (s:string (S n)) : s = cons_str (fst (non_zero_string_pop s)) (snd (non_zero_string_pop s)).
dependent destruction s. simpl; reflexivity.
Defined.

(*We can recover a string's length:*)

Definition string_length {m:nat} (s: string m) := m.


(*And we can also extract the last symbol and the head of a non-empty string :*)

Definition string_head {m:nat} (s: string (S m)) : string m.
induction m. 
+ apply Empty_string.
+ dependent destruction s. apply (cons_str v (IHm s)).
Defined.

Lemma string_head_identity {m:nat} (s: string (S m)) (v:symbols) : string_head (cons_str v s) = cons_str v (string_head s).
simpl. unfold block. unfold solution_left. unfold eq_rect_r. simpl. f_equal.
Defined.

Definition string_last {m:nat} (s: string (S m)) : symbols.
induction m. 
+ dependent destruction s. apply v.
+ dependent destruction s. apply (IHm s).
Defined.


Lemma string_last_identity {m:nat} (s: string (S m)) (v:symbols) : string_last (cons_str v s) = string_last s.
simpl. unfold block. unfold solution_left. unfold eq_rect_r. simpl. reflexivity.
Defined.

Fixpoint string_last_rebuild_aux {m:nat} (s: string m) (v:symbols) := match s with
| Empty_string => cons_str v Empty_string
| cons_str v' s' => cons_str v' (string_last_rebuild_aux s' v)
end.

Lemma string_last_rebuild {m:nat} (s: string (S m)) : s = string_last_rebuild_aux (string_head s) (string_last s).
induction m. + dependent destruction s. rewrite (zero_string_is_empty s). simpl. unfold block. unfold solution_left. unfold eq_rect_r. simpl; reflexivity.
+ dependent destruction s. rewrite string_head_identity. rewrite string_last_identity. simpl. rewrite <- (IHm s); reflexivity.
Defined.

(*A string can be reversed:*)

Definition string_reversal_aux {n m:nat} (s : string n)  (s' : string m) : string (string_length s + string_length s').
unfold string_length. dependent induction n.
+ simpl. apply s'.
+ dependent destruction s. simpl. rewrite <- add_succ_r_bis. apply (IHn (S m) s (cons_str v s')).
Defined.

Definition string_reversal {n:nat} (s: string n): string n.
rewrite <- add_0_r_bis. apply (string_reversal_aux s Empty_string).
Defined.

Lemma string_reversal_length {m:nat} (s : string m) : string_length s = string_length (string_reversal s).
unfold string_length. reflexivity.
Defined.


Lemma string_reversal_aux_last {n m:nat} (s : string (S n))  (s' : string (S m)) : string_last (string_reversal_aux s s') = string_last s'.
dependent induction n.
+ dependent destruction s. rewrite (zero_string_is_empty s). replace (string_reversal_aux (cons_str v Empty_string) s') with (cons_str v s').
- apply string_last_identity.
- simpl. unfold solution_left. unfold eq_rect_r. simpl. reflexivity.
+ dependent destruction s. assert (string_last (string_reversal_aux s (cons_str v s')) = string_last s').
- apply (IHn _ s (cons_str v s')).
- rewrite <- H. assert (string_length (cons_str v s) + string_length s' =
 string_length s + string_length (cons_str v s')). * unfold string_length. simpl. f_equal. rewrite <- add_succ_r_bis. reflexivity.
* unfold string_reversal_aux. unfold block. Admitted.

Lemma string_reversal_first_to_last {m:nat} (s : string m) (v: symbols) : string_last (string_reversal (cons_str v s)) = v.
unfold string_reversal. induction m. + simpl. unfold solution_left. unfold eq_rect_r. simpl. reflexivity.
+ Admitted.

Lemma string_reversal_involution_aux {m: nat} (s: string m) (v:symbols): string_reversal (string_reversal (cons_str v s)) = cons_str v (string_reversal (string_reversal s)).
dependent induction m.
+ rewrite (zero_string_is_empty s). unfold string_reversal. simpl. unfold solution_left. unfold eq_rect_r. simpl. reflexivity.
+ dependent destruction s. Admitted.

Lemma string_reversal_involution {m:nat} (s: string m) : string_reversal (string_reversal s) = s.
dependent induction m.
+ rewrite (zero_string_is_empty s). unfold string_reversal. simpl; reflexivity.
+ dependent destruction s. rewrite string_reversal_involution_aux. f_equal. 
apply IHm.
Defined.


(*
Lemma string_reversal_single_symbol (v: symbols) : string_reversal (cons_str v Empty_string) = cons_str v Empty_string.
simpl; reflexivity.
Defined.
*)


(*
Lemma string_reversal_decomposition {m: nat} (s: string (S m)) :string_reversal (string_head s) = string_tail (string_reversal s).
assert (exists s', string_head s = s').
+ exists (string_head s). reflexivity.
+ destruct H. dependent induction x.
- dependent destruction s. rewrite (zero_string_is_empty s). simpl; reflexivity.
- dependent destruction s. rewrite string_head_identity in H. 
induction (string_head s).
+ dependent destruction s. rewrite (zero_string_is_empty s). simpl; reflexivity.
+ 

dependent induction m. + dependent destruction s. rewrite (zero_string_is_empty s). simpl; reflexivity.
+ dependent destruction s. rewrite string_head_identity. 

Lemma string_reversal_involution {n:nat} (s: string n): string_reversal (string_reversal s) = s.
dependent induction n. 
+ rewrite (zero_string_is_empty s). simpl; reflexivity.
+ dependent destruction s.

Lemma string_reversal_involution_aux {m:nat} (s: string m) (v w x: symbols) :cons_str v ( string_reversal (string_reversal (cons_str w s))) = cons_str v (cons_str w s) /\ ( string_reversal (string_reversal (cons_str x  s))) = cons_str x s.
dependent induction m. + rewrite (zero_string_is_empty s). simpl; auto.
+ dependent destruction s.
split. - 
- f_equal. destruct IHm with s w v. apply H.
- replace (cons_str v0 (cons_str v s)) with (cons_str v0 (string_reversal (string_reversal (cons_str v s)))).  
2: { f_equal.  destruct IHm with s v. apply H0. } 

Lemma string_reversal_involution_aux {m:nat} (s: string m) (v:symbols): string_reversal (string_reversal s) = s /\  (string_reversal (string_reversal (cons_str v s))) = cons_str v s .
dependent induction m. + rewrite (zero_string_is_empty s); simpl; auto.
+ split. - dependent destruction s. destruct IHm with s v. apply H0.
-  

 2: { dependent destruction s. 
+ split. - dependent destruction s. destruct IHm with s v.

 dependent destruction s. dependent induction s.
- simpl; reflexivity. -

assert (string_reversal (string_reversal (cons_str v s)) = cons_str v s \/  string_reversal (string_reversal (cons_str v s)) <> cons_str v s).
- apply string_decidable.
- destruct H.
* apply H.
*

 assert (cons_str v (string_reversal (string_reversal s)) = cons_str v s).
** f_equal; auto.
** 



Lemma string_reversal_involution_aux {m:nat} (s: string m) (v: symbols) : cons_str v (string_reversal (string_reversal s)) = cons_str v s.
dependent induction m.
+ rewrite (zero_string_is_empty s); simpl; reflexivity. + dependent destruction s.
assert (string_reversal (string_reversal s ) = s).
- apply .

dependent destruction s. dependent induction m.
- rewrite (zero_string_is_empty s). simpl; reflexivity.
- dependent destruction s.


<- IHm.


Lemma string_reversal_involution {m:nat} (s: string m) : string_reversal (string_reversal s) = s.
induction s. + simpl; reflexivity.
+ assert (string_reversal (string_reversal (cons_str v s)) = cons_str v s \/  string_reversal (string_reversal (cons_str v s)) <> cons_str v s).
- apply string_decidable.
- destruct H.
* apply H.
* assert (cons_str v (string_reversal (string_reversal s)) = cons_str v s).
** f_equal; auto.
** 
*)
Lemma string_reversal_first {m:nat} (s: string (S m)) (v: symbols) : fst (non_zero_string_pop (string_reversal (cons_str v s))) = fst (non_zero_string_pop (string_reversal s)) .
dependent destruction s. dependent induction m.
+ rewrite (zero_string_is_empty s). simpl; reflexivity.
+ Admitted.

Lemma string_reversed_first_is_last {m:nat} (s: string m) (v:symbols): fst (non_zero_string_pop (string_reversal (cons_str v s))) = string_last (cons_str v s) .
dependent induction m. + rewrite (zero_string_is_empty s). simpl. unfold block. unfold solution_left. unfold eq_rect_r. simpl; reflexivity.
+ dependent destruction s. rewrite string_last_identity. rewrite <- IHm. apply string_reversal_first.
Defined.

Lemma string_reversal_head_last {m:nat} (s: string (S m)) : string_reversal s = cons_str (string_last s) (string_reversal (string_head s)).
induction m. + dependent destruction s. rewrite (zero_string_is_empty s). simpl. unfold block. unfold solution_left. unfold eq_rect_r. simpl; reflexivity.
+ dependent destruction s. rewrite (non_zero_string_pop_identity (string_reversal (cons_str v s))). f_equal.
- apply string_reversed_first_is_last.
- rewrite string_head_identity. Admitted.


Lemma string_reversed_reversed_snd_pop_is_tail {m:nat} (s:string (S m)) : (snd (non_zero_string_pop (string_reversal s))) = string_reversal (string_tail s).
induction m. + dependent destruction s. rewrite (zero_string_is_empty s). simpl. reflexivity.
+ Admitted. 

Fixpoint add_m_pluses_at_start_string {n: nat} (m : nat) (s: string n) : string (m + n) := match m with
  | 0 => s
  | S p => cons_str plus (add_m_pluses_at_start_string p s)
  end.

(*TODO*)

(*Some examples:*)
  
Check Empty_string.

Check cons_str plus Empty_string.

(*cubical_three := the string ++, which will be the vertex 3 in the cubical faces*)

Definition cubical_three := cons_str plus (cons_str plus Empty_string).

Check cubical_three.
  
Compute string_reversal (cons_str plus (cons_str plus (cons_str minus Empty_string))).

End Symbolic_Strings.


Section Symbolic_Words.

(*Words are similarly built, based on nat and strings. Morally, the constructor cons_word adds a 0 between two strings:*)

Inductive word : nat -> Type :=
  |null_word : forall {m:nat} (s: string m), word 0
  |cons_word : forall {n m:nat} (s: string m), word n -> word (S(n)).

(*There are three lengths associated to a word:*)

(*cubical_dimension := the amount of zeros *)

Definition cubical_dimension {m:nat} (w:word m) := m.

(*simplicial_dimension := the amount of zeros after the first one, for a word with at least one zero*)

Definition simplicial_dimension {m:nat} (w:word (S(m))) := m.

(*total_length := the addition of the length of all strings in the word, and the zeros*)

Fixpoint total_length {m:nat} (w:word m):= match w with
  |null_word s => string_length s
  |cons_word s w' => S(string_length s) + (total_length w')
  end.

(*Properties of total_length:*)

Lemma length_zero_is_empty (w:word 0) (proof: total_length w = 0): w = null_word Empty_string.
dependent destruction w. simpl in proof. unfold string_length in proof. dependent destruction s.
+ reflexivity. + discriminate.
Defined.

Lemma length_is_gt_word_lenght {n :nat} (w:word n) : n <= total_length w.
dependent induction w. + simpl. unfold string_length. apply Nat.le_0_l.
+ simpl. apply le_n_S. apply le_n_plus_trans_bis ; apply IHw.
Defined.

(*It will be useful to have access to the length of the first and last string appearing in a word:*)

Definition word_first_length {n:nat} (w: word n):= match w with
  | null_word s => string_length s
  | cons_word s w' => string_length s
  end.

Fixpoint word_last_length {n:nat} (w: word n) := match w with
  | null_word s => string_length s
  | cons_word s w' => word_last_length w'
  end.

Lemma word_first_length_identity {n m p:nat} (s: string m) (s':string p) (w:word n) : word_first_length (cons_word s w) = word_first_length (cons_word s (cons_word s' w)).
simpl. reflexivity.
Defined.

Lemma word_last_length_identity {n m:nat}(s: string m) (w: word  n) : word_last_length w = word_last_length (cons_word s w).
simpl. reflexivity.
Defined.

(*We can recover the first and last string of a word:*)

Definition word_first_pop {n:nat} (w: word n) : string (word_first_length w).
destruct w. + apply s.
+ apply s.
Defined.

Definition word_last_pop {n:nat} (w:word n) : string (word_last_length w).
induction w. + simpl. unfold string_length. apply s.
+ simpl. apply IHw.
Defined.

(*We have two ways of recomposing a zero-word:*)

Lemma null_word_pop_identity (w : word 0) : w = null_word (word_first_pop w) /\ w = null_word (word_last_pop w).
dependent destruction w. auto.
Defined. 

(*We can find the word tailing and heading of a non-zero-word:*)

Definition word_tail {n:nat} (w: word n) : word (pred_bis n) := match w with
  | null_word s => null_word Empty_string   
  | cons_word s w' => w'
   end.

Definition word_head {n:nat} (w: word n) : word (pred_bis n).
induction w. + simpl. apply (null_word Empty_string).
+ induction w. - simpl. apply (null_word s).
- simpl. apply (cons_word s IHw).
Defined.

(*We want some operations on the first string of a word:*)

(*first_string_replace := replace the first string by a given string*)

Definition first_string_replace {n m:nat} (w:word n) (s: string m) := match w with
  |null_word s' => null_word s
  |cons_word s' w' => cons_word s w'
  end.

Lemma first_string_replace_identity_aux {n m : nat} (w:word n)(s: string m) : string (word_first_length (first_string_replace w s)).
assert (m = word_first_length (first_string_replace w s)). + destruct w. - simpl. reflexivity.
- simpl. reflexivity.
+ simpl. rewrite <- H. apply s.
Defined.

Lemma first_string_replace_identity {n m:nat} (w: word n)(s: string m) : first_string_replace_identity_aux w s = word_first_pop (first_string_replace w s).
destruct w. + simpl. unfold first_string_replace_identity_aux. simpl. reflexivity.
+ simpl. unfold first_string_replace_identity_aux. simpl. reflexivity.
Defined. 

(*add_m_?_at_start := add an arbitrary number of the same symbol at the beginning of the first string of a word*)

Fixpoint add_m_pluses_at_start {n:nat} (m:nat) (w:word n): word n := match m with
  |0 => w
  |S p => let IHm := add_m_pluses_at_start p w in (first_string_replace IHm (cons_str plus (word_first_pop IHm)))
  end.

Fixpoint add_m_minus_at_start {n:nat} (m:nat) (w:word n): word n := match m with
  |0 => w
  |S p => let IHm := add_m_minus_at_start p w in (first_string_replace IHm (cons_str minus (word_first_pop IHm)))
  end.
  
  
Lemma add_m_pluses_at_start_0_identity {n:nat} (m:nat) (proof : m = 0) (w: word n) : add_m_pluses_at_start m w = w.
rewrite proof. simpl. reflexivity.
Defined.

Lemma add_m_minus_at_start_0_identity {n:nat} (m:nat) (proof : m = 0) (w: word n) : add_m_minus_at_start m w = w.
rewrite proof. simpl. reflexivity.
Defined.

(*We can reverse words:*)

Fixpoint word_reversal_aux {n m:nat} (w : word n)  (w' : word m) : word (n + m):=
match w with
  | null_word s => first_string_replace w' s
  | cons_word s v => cons_word s (word_reversal_aux v w')
  end.

Definition word_reversal {n:nat} (w: word n) : word n.
induction w. + apply (null_word (string_reversal s)).
+ rewrite <- add_1_r_bis. apply (word_reversal_aux IHw (cons_word (Empty_string)(null_word (string_reversal s)))).
Defined.

Lemma a_word_is_a_reverse {n:nat} (w: word n) : exists w', w' = word_reversal w.
dependent induction n. + dependent destruction w. exists (null_word (string_reversal s)). simpl; reflexivity.
+ dependent destruction w. simpl.  
Admitted.

Lemma word_reversal_involution {n:nat} (w: word n) : word_reversal (word_reversal w) = w.
dependent induction n. - dependent destruction w. simpl. rewrite string_reversal_involution. reflexivity.
- Admitted.

(*We can concatenate words with an extra zero between them:*)

Fixpoint word_concatenate_zero {n m: nat} (w: word n) (w': word m): word (S (n+m)):= match w with
  |null_word s => (cons_word s w')
  |cons_word s x => cons_word s (word_concatenate_zero x w')
  end.

Lemma word_concatenate_zero_first_length {n m : nat} (w:word n) (w' : word m): word_first_length w = word_first_length (word_concatenate_zero w w').
destruct w ; simpl; reflexivity.
Defined.

Lemma word_concatenate_zero_last_length {n m:nat} (w:word n)(w':word m) : word_last_length w' = word_last_length (word_concatenate_zero w w').
induction w. + simpl; reflexivity.
+ simpl. apply IHw.
Defined.

Lemma word_concatenate_zero_total_length {n m: nat} (w:word n)(w':word m): total_length (word_concatenate_zero w w') = S (total_length w + total_length w').
induction w. + simpl. reflexivity.
+ simpl. rewrite IHw. rewrite add_succ_r_bis. rewrite add_assoc_bis. reflexivity.
Defined.

(*A word is the cons of its first string pop and its tail:*)

Lemma non_zero_word_identity_tail {n:nat} (w : word (S n)) : w = cons_word (word_first_pop w) (word_tail w).
dependent destruction w. simpl. reflexivity.
Defined.

(*And more generally, we want to be able to split a non-zero word along a zero into two recomposable parts:*)

Definition non_zero_word_split_aux {n p:nat} (w: word n) (w': word p) (m:nat) : word (p+m) * word (n - m).
induction m. + rewrite sus_0_r_bis. rewrite add_0_r_bis. apply ((w',w)).
+ destruct IHm. split. - rewrite add_succ_r_bis. apply (cons_word (word_first_pop w1) w0).
- rewrite <- pred_sus_is_sus_succ_bis. apply (word_tail w1).
Defined.

Definition non_zero_word_split {n:nat} (w:word (S n)) (m : nat) := let p := non_zero_word_split_aux w (null_word Empty_string) m in (word_tail (word_reversal (fst p)),snd p).

(*If m is zero or one over the length of w, we recover the word and the empty word. For values in that interval, the total length of w is one more than the addition of length of the split:*)

Lemma non_zero_word_split_zero {n:nat} (w: word (S n)) : total_length (fst (non_zero_word_split w 0)) = 0.
simpl. unfold string_length. reflexivity.
Defined.

Lemma non_zero_word_split_S_dim {n:nat} (w: word (S n)) : total_length (snd (non_zero_word_split w (S (S n)))) = 0.
induction n. + simpl. dependent destruction w. dependent destruction w. simpl. unfold string_length. reflexivity.
+ Admitted. 

(*TODO solve this issue*)

(*TODO
Lemma word_reversal_identity {n:nat} (w: word (S n)) : 
*)

(*And reversed words keep all lengths:*)

Lemma reversed_cubical_dimension {n:nat} (w: word n) : cubical_dimension w = cubical_dimension (word_reversal w).
unfold cubical_dimension. reflexivity.
Defined.

Lemma reversed_simplicial_dimension {n:nat} (w: word (S n)) : simplicial_dimension w = simplicial_dimension w.
unfold simplicial_dimension. reflexivity.
Defined.

(*TODO 

Lemma first_reversed_is_last {n:nat} (w: word n) : word_last_length w = word_first_length (word_reversal w).
induction w.
+ simpl. apply string_reversal_length.
+ simpl.

Lemma reversed_word_first_length_identity {n:nat} (w: word n) : word_first_length w = string_length (word_string_pop w).
destruct w. + simpl. reflexivity.
+ simpl. reflexivity.
Defined.

Lemma reversed_word_string_pop {n m:nat} (s: string m) (w: word n) : string_length (word_string_pop (word_reversal w)) = string_length (word_string_pop (word_reversal (cons_word s w))).
unfold word_reversal.


induction n.
+ dependent destruction w. simpl. apply string_reversal_length.
+ dependent destruction w. rewrite word_last_length_identity. rewrite (IHn (word_tail (cons_word s w))).
rewrite reversed_word_first_length_identity. rewrite reversed_word_first_length_identity. simpl.

induction w.
- simpl. reflexivity.
- simpl.

*)
Lemma reversed_total_length {n:nat} (w: word n) : total_length w = total_length (word_reversal w).
induction w. + simpl. unfold string_length. reflexivity.
+ Admitted.
(*TODO Reversal Stuff*)

(*Some examples:*)

Check null_word cubical_three.

(*word_example_1 := ++0+++*)

Definition word_example_1:= cons_word cubical_three (null_word (cons_str plus cubical_three)).
Check word_example_1.

Compute total_length (cons_word Empty_string (null_word Empty_string)).

Compute word_tail word_example_1.  

Compute total_length word_example_1.

Compute cubical_dimension (null_word cubical_three).

Compute cubical_dimension word_example_1.

Fail Compute simplicial_dimension (zero_word cubical_three).

Compute simplicial_dimension word_example_1.

Compute word_reversal word_example_1.

Compute word_reversal (cons_word (cons_str minus Empty_string) word_example_1).

Compute non_zero_word_split (cons_word (cons_str plus Empty_string) (cons_word cubical_three (cons_word (cons_str minus Empty_string) (cons_word cubical_three (null_word (cons_str plus Empty_string)))))) 3.

Compute non_zero_word_split (cons_word (cons_str plus Empty_string) (cons_word cubical_three (cons_word (cons_str minus Empty_string) (cons_word cubical_three (null_word (cons_str plus Empty_string)))))) 0.

(*TODO more examples*)

End Symbolic_Words.


Section Principal_Cells.

(*We call some specific words principal cells: *)

Fixpoint principal_cell_m (m:nat) := match m with
  |0 => null_word Empty_string
  |S p => cons_word Empty_string (principal_cell_m p)
  end.

(*The m principal cell is of total length m:*)

Lemma length_principal_is_m (m:nat) : total_length (principal_cell_m m) = m.
induction m. + simpl. unfold string_length. reflexivity.
+ simpl. rewrite IHm. reflexivity.
Defined.

(*This characterizes principal cells: *)

Lemma length_is_word_length_implies_principal {n:nat} (w: word n) (proof : total_length w = n) : w = principal_cell_m n.
induction n. + simpl. apply (length_zero_is_empty w proof).
+ dependent destruction w. simpl in proof. inversion proof. assert (total_length w = n).
- apply Nat.le_antisymm. * apply Nat.eq_le_incl in H0. apply (Nat.le_trans (total_length w) (string_length s + total_length w) n).
** apply Nat.le_add_l. ** apply H0.
* apply (length_is_gt_word_lenght w).
- apply (IHn w) in H as H1. rewrite H in H0. apply (add_l_cancel_bis (string_length s) n) in H0. rewrite H1. simpl. induction m.
* rewrite (zero_string_is_empty s). reflexivity.
* dependent destruction s. unfold string_length in H0. discriminate H0.
Defined.

(*** This proof might be done a bit easier, but its elements are roughly these ***)

(*The above allows for the following test:*)

Definition is_principal {n:nat} (w: word n) := total_length w = n.

(*Some examples:*)

Compute principal_cell_m 2.

Compute is_principal (null_word Empty_string).

Compute is_principal (cons_word (cons_str plus Empty_string) (null_word Empty_string)).

Compute is_principal (principal_cell_m 3).

End Principal_Cells.


Section Positive_words.

(*A positive string is a non-negative string, that is a string with a proof of its non-negativity:*)

Fixpoint is_positive_string {n:nat} (s : string n) {struct s}:= match s with
  | Empty_string => True
  | cons_str v s' => v = plus /\ is_positive_string s'
  end.

Definition positive_string {n : nat} := {s: string n | is_positive_string s}.

(*The operations on strings preserve positivity:*)

Lemma string_tail_mono {n:nat} (s: @positive_string n) : is_positive_string (string_tail (proj1_sig s)).
destruct s. simpl. destruct x. + simpl. apply i.
+ simpl. destruct i. apply H0.
Defined.

Lemma string_pop_mono {n:nat} (s: @positive_string (S n)) : let s' := non_zero_string_pop (proj1_sig s) in fst s' = plus /\ is_positive_string (snd s').
destruct s. simpl. dependent destruction x. simpl. destruct i. split.
+ apply H. + apply H0.
Defined.

Lemma string_last_mono {n:nat} (s: @positive_string (S n)) : string_last (proj1_sig s) = plus.
destruct s. simpl. induction n. + dependent destruction x. destruct i. simpl. unfold solution_left. unfold eq_rect_r. unfold eq_rect.
simpl. apply H.
+ dependent destruction x. rewrite string_last_identity. destruct i. apply (IHn x H0).
Defined.

Lemma string_reversal_mono {n:nat} (s: @positive_string n) : is_positive_string (string_reversal (proj1_sig s)).
destruct s. simpl. induction n. + dependent destruction x. simpl; trivial.
+ dependent destruction x. rewrite (non_zero_string_pop_identity (string_reversal (cons_str v x)) ) . split.
- rewrite string_reversed_first_is_last. replace (cons_str v x) with (proj1_sig (sigma_proof (cons_str v x) i)).
* apply string_last_mono. * simpl. reflexivity.
- rewrite string_reversed_reversed_snd_pop_is_tail. simpl. apply IHn. destruct i. apply H0.
Defined.

(*Likewise, we define positive words as words having a proof of non_negativity:*)

Fixpoint is_positive_word {n:nat} (w: word n):= match w with
  | null_word s => is_positive_string s
  | cons_word s' w' => is_positive_string s' /\ is_positive_word w'
  end.

Definition positive_word {n: nat} := {w: word n | is_positive_word w}.


(*And operations on positive words preserve positivity:*)

Lemma word_first_pop_mono {n:nat} (w: @positive_word n) : is_positive_string (word_first_pop (proj1_sig w)).
destruct w. simpl. destruct x.
+ simpl. simpl in i. apply i.
+ simpl. destruct i. apply H.
Defined.

Lemma word_tail_mono {n:nat} (w: @positive_word (S n)) : is_positive_word (word_tail (proj1_sig w)).
destruct w. simpl. dependent destruction x. simpl. destruct i. apply H0.
Defined.

Lemma first_string_replace_mono {n m:nat} (w: @positive_word n) (s: @positive_string m) : is_positive_word (first_string_replace (proj1_sig w) (proj1_sig s)).
destruct w; destruct s. simpl. destruct x. + simpl. apply i0.
+ simpl. split. - apply i0. - destruct i. apply H0.
Defined.

Lemma add_m_pluses_at_start_mono {n : nat} (m:nat) (w: @positive_word n) : is_positive_word (add_m_pluses_at_start m (proj1_sig w)).
induction m. + simpl. apply (proj2_sig w).
+ simpl. assert (is_positive_string (cons_str plus (word_first_pop (add_m_pluses_at_start m (proj1_sig w))))). 2: {   replace (cons_str plus (word_first_pop (add_m_pluses_at_start m (proj1_sig w)))) with (proj1_sig (sigma_proof (cons_str plus (word_first_pop (add_m_pluses_at_start m (proj1_sig w))))  H ) ).
2: { simpl; reflexivity. } apply (first_string_replace_mono (sigma_proof _ IHm) (sigma_proof _ _)). } split; trivial. apply (word_first_pop_mono (sigma_proof _ IHm) ).
Defined.

Lemma word_reversal_mono {n:nat} (w: @positive_word n) : is_positive_word (word_reversal (proj1_sig w)).
Admitted.

(*TODO reversalmono*)


(*A principal cell is always positive:*)

Lemma principal_is_positive (m:nat) : is_positive_word (principal_cell_m m).
induction m. + simpl; trivial.
+ simpl. auto.
Defined.

Lemma principal_implies_positive {n:nat}(w: word n) : is_principal w -> is_positive_word w.
intro. apply length_is_word_length_implies_principal in H. rewrite H. apply principal_is_positive.
Defined.

(*An operation to add pluses to a word up to a certain total length:*)

Definition plus_filling {n:nat} (m:nat) (w : @positive_word n) : @positive_word n := 
(sigma_proof (add_m_pluses_at_start  (m - (total_length (proj1_sig w))) (proj1_sig w)) (add_m_pluses_at_start_mono (m - (total_length (proj1_sig w))) w)).


(*Some examples:*)

Compute is_positive_string (cons_str plus Empty_string).

Compute is_positive_string (cons_str plus (cons_str plus Empty_string)).

Definition cubical_three_is_positive : is_positive_string cubical_three.
simpl. auto.
Qed.

Definition cubical_three_is_in_positive : @positive_string 2.
apply (sigma_proof cubical_three cubical_three_is_positive).
Defined.

Compute (proj1_sig cubical_three_is_in_positive, proj2_sig cubical_three_is_in_positive).

Definition word_example_1_is_positive : is_positive_word word_example_1.
simpl. auto.
Qed.

Definition word_example_1_in_positive := sigma_proof word_example_1 word_example_1_is_positive.

Compute plus_filling 10 word_example_1_in_positive.

End Positive_words.

Section Simplicial_words.

(*A simplicial generator can be sent to an m word with m>= 1:*)

Fixpoint simplicial_to_m_word_aux (t:simplicial_generator) : word (S (simplicial_generator_depth t)) := match t with
  | simpl_base => (cons_word Empty_string (null_word Empty_string))
  | simpl_plus t' => add_m_pluses_at_start 1 (simplicial_to_m_word_aux t')
  | simpl_zero t' => cons_word Empty_string (simplicial_to_m_word_aux  t')
  end.

Definition simplicial_to_m_word (m:nat) (t:simplicial_generator) : word (S (simplicial_generator_depth t)) := let w := (word_reversal (simplicial_to_m_word_aux t)) in add_m_pluses_at_start (m - (total_length w)) w.

(*A word coming from a simplicial generator is positive:*)

Lemma simplicial_word_is_positive_aux (t:simplicial_generator) : is_positive_word (simplicial_to_m_word_aux t).
induction t.
+ simpl; auto.
+ simpl. assert (is_positive_string (cons_str plus (word_first_pop (simplicial_to_m_word_aux t)))).
- simpl. split; auto. apply (word_first_pop_mono (sigma_proof _ IHt)).
- apply (first_string_replace_mono (sigma_proof _ IHt) (sigma_proof _ H)).
+ simpl. split; auto.
Defined.  

Lemma simplicial_word_is_positive (t: simplicial_generator) {m:nat} : is_positive_word (simplicial_to_m_word m t).
unfold simplicial_to_m_word.  assert (is_positive_word (word_reversal (simplicial_to_m_word_aux t))).
+ apply (word_reversal_mono (sigma_proof (simplicial_to_m_word_aux t) (simplicial_word_is_positive_aux t))).
+ apply (add_m_pluses_at_start_mono ( m - total_length (word_reversal (simplicial_to_m_word_aux t))) (sigma_proof _ H)).
Defined. 

Definition simplicial_to_positive_m_word (m:nat) (t:simplicial_generator) := sigma_proof (simplicial_to_m_word m t) (simplicial_word_is_positive t).

(*Conversely, we want to biuld the corresponding simplicial generator from a given positive m word:*)

Fixpoint m_word_to_simplicial_aux_1 {m:nat} (s: string m) (t: simplicial_generator) := match s with
  | Empty_string => t
  | cons_str v s' => m_word_to_simplicial_aux_1 s' (simpl_plus t)
  end.

Fixpoint m_word_to_simplicial_aux_2 {n:nat} (w: word n) (t : simplicial_generator) := match w with
  | null_word s' => m_word_to_simplicial_aux_1 s' t
  | cons_word Empty_string w' => m_word_to_simplicial_aux_2 w' (simpl_zero t)
  | cons_word s' w' => m_word_to_simplicial_aux_2 w' (simpl_zero (m_word_to_simplicial_aux_1 s' t))
  end.

Fixpoint m_word_to_simplicial_aux_3 (t: simplicial_generator) (m:nat) := match t with
  | simpl_base => simpl_base
  | simpl_plus t' => simpl_plus (m_word_to_simplicial_aux_3 t' m)
  | simpl_zero t' => match m with
      |0 => simpl_base
      |S p => simpl_zero (m_word_to_simplicial_aux_3 t' p)
      end
  end.
  
Lemma m_word_to_simplicial_aux_1_comm {m:nat} (v: symbols) (s: string m) (t: simplicial_generator): m_word_to_simplicial_aux_1 (cons_str v s) t = simpl_plus (m_word_to_simplicial_aux_1 s t).
 dependent induction m. + rewrite (zero_string_is_empty s). simpl. reflexivity. 
+ dependent destruction s. replace (m_word_to_simplicial_aux_1 (cons_str v (cons_str v0 s)) t) with (m_word_to_simplicial_aux_1 (cons_str v0 s) (simpl_plus t)).
- apply IHm. - simpl. reflexivity.
Defined. 

Lemma m_word_to_simplicial_aux_3_comm (t: simplicial_generator) (m:nat) : m_word_to_simplicial_aux_3 (simpl_zero t) (S m) = simpl_zero (m_word_to_simplicial_aux_3 t m).
trivial.
Defined.

Definition ex1 := m_word_to_simplicial_aux_2 (cons_word Empty_string (null_word cubical_three)) (simpl_base).

Definition ex2 := m_word_to_simplicial_aux_2 (cons_word Empty_string (cons_word (cons_str plus Empty_string) (null_word cubical_three))) (simpl_base).

Definition ex3 := m_word_to_simplicial_aux_2 (cons_word (cons_str plus Empty_string) (cons_word Empty_string (cons_word cubical_three (null_word Empty_string)))) simpl_base.

Compute ex1.

Compute m_word_to_simplicial_aux_3 ex1 0.

Compute ex2.

Compute m_word_to_simplicial_aux_3 ex2 1.

Compute ex3.

Compute m_word_to_simplicial_aux_3 ex3 2.

Definition positive_m_word_to_simplicial {n:nat} (w: @positive_word (S n)) := let w0 := proj1_sig w in m_word_to_simplicial_aux_3 (m_word_to_simplicial_aux_2 w0 simpl_base) (simplicial_dimension w0).

Compute positive_m_word_to_simplicial word_example_1_in_positive.

Compute positive_m_word_to_simplicial (simplicial_to_positive_m_word 5 (simpl_plus (simpl_zero simpl_base) )).

Compute positive_m_word_to_simplicial (simplicial_to_positive_m_word  7 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base)))))).

Compute positive_m_word_to_simplicial (simplicial_to_positive_m_word  5 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base)))))).

(*Going back and forth we can get back where we started:*)

Lemma simplicial_back_to_simplicial {m:nat} (t:simplicial_generator) : positive_m_word_to_simplicial (simplicial_to_positive_m_word m t) = t.
Admitted.

Lemma TODO_positive_word_back_to_positive_word_aux {n:nat} (w: @positive_word (S n)): S n = S (simplicial_generator_depth (positive_m_word_to_simplicial w)) .
Admitted.

Lemma positive_word_back_to_positive_word_aux {n:nat} (w: @positive_word (S n)) : @positive_word (S n).
assert (S n = S (simplicial_generator_depth (positive_m_word_to_simplicial w)) ).
2: { rewrite H. apply ( simplicial_to_positive_m_word (S n) (positive_m_word_to_simplicial w)). }
apply TODO_positive_word_back_to_positive_word_aux.
Defined.

Lemma positive_word_back_to_positive_word {n:nat} (w: @positive_word (S n)) : w = positive_word_back_to_positive_word_aux (w).
Admitted.

(*TODO identity_lemmas*)

(*Principal cells are associated to principal generators:*)
  
Lemma principal_simplicial_generator_depth (n:nat): simplicial_generator_depth (principal_simplicial_generator n) = n.
induction n. + simpl; reflexivity.
+ simpl. rewrite IHn; reflexivity.
Defined.

Lemma principal_simplicial_total_length (n: nat) : let t:= principal_simplicial_generator n in total_length (proj1_sig (simplicial_to_positive_m_word (simplicial_generator_depth t) t)) = S n.
simpl. unfold simplicial_to_m_word. rewrite add_m_pluses_at_start_0_identity. + rewrite <- reversed_total_length.
 induction n.
- simpl. unfold string_length ; reflexivity.
- simpl. rewrite IHn; reflexivity.
+ rewrite <- reversed_total_length. induction n.
- simpl; reflexivity.
- simpl; apply IHn.
Defined.

Lemma principal_simplicial_sent_to_principal_cell (n:nat) : let t:= principal_simplicial_generator n in proj1_sig (simplicial_to_positive_m_word (simplicial_generator_depth t) t) = principal_cell_m (S (simplicial_generator_depth t)).
apply length_is_word_length_implies_principal. rewrite principal_simplicial_total_length. rewrite principal_simplicial_generator_depth. reflexivity.
Defined.


Lemma first_string_replace_mono_back {n m} {w: word n} {s: string m} (proof : is_positive_word (first_string_replace w s)) : is_positive_word (word_tail w) /\ is_positive_string s.
destruct w.
+ simpl. simpl in proof. split; auto.
+ simpl in proof. destruct proof. split. - simpl. apply H0. - apply H.
Defined.

Lemma first_and_tail_positive_imply_positive {n} {w: word n} (proof1: is_positive_string (word_first_pop w)) (proof2: is_positive_word (word_tail w)): is_positive_word w.
destruct w.
+ simpl. simpl in proof1. apply proof1.
+ simpl. split. - simpl in proof1. apply proof1. - simpl in proof2. apply proof2.
Defined.

Lemma simplicial_dimension_is_depth (s: simplicial_generator) : simplicial_generator_depth s = simplicial_dimension (proj1_sig (simplicial_to_positive_m_word (simplicial_generator_depth s) s)).
simpl. unfold simplicial_dimension. reflexivity.
Defined.

Lemma simplicial_depth_is_dimension {n:nat} (w: @positive_word (S n)) : simplicial_dimension (proj1_sig w) = simplicial_generator_depth (positive_m_word_to_simplicial w).
unfold simplicial_dimension. destruct w. dependent destruction x.
dependent induction x.
+ unfold positive_m_word_to_simplicial. simpl. induction s.
- unfold simplicial_dimension. induction s0.
* simpl; reflexivity. *  rewrite m_word_to_simplicial_aux_1_comm. simpl. apply IHs0.
simpl. split; auto. destruct i. destruct H0. apply H1.
- unfold simplicial_dimension. rewrite m_word_to_simplicial_aux_1_comm. 
Admitted.

(*
unfold simplicial_dimension. destruct w. induction n.
+ dependent destruction x.
unfold positive_m_word_to_simplicial. simpl. destruct s.
- unfold simplicial_dimension. dependent destruction x. simpl. induction s.
* simpl; reflexivity. * rewrite m_word_to_simplicial_aux_1_comm. simpl. apply IHs.
destruct i. simpl. split; trivial. destruct H0. apply H1.
- unfold simplicial_dimension. dependent destruction x. simpl. induction s0.
* simpl; reflexivity. * rewrite m_word_to_simplicial_aux_1_comm. simpl. apply IHs0.
destruct i. destruct H. destruct H0. simpl. auto.
+ dependent destruction x. unfold positive_m_word_to_simplicial. unfold simplicial_dimension.
unfold positive_m_word_to_simplicial in IHn. unfold simplicial_dimension in IHn. simpl. induction s.
- dependent destruction x. induction s.
* simpl.
- unfold simplicial_dimension.
*)

(*Some examples:*)

Compute simplicial_to_m_word 5 (simpl_plus (simpl_zero simpl_base) ).

Compute simplicial_to_m_word 7 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

Compute simplicial_to_m_word 5 (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).

End Simplicial_words.


Section Cubical_words.

(*A cubical generator can be sent to a word:*)

Fixpoint cubical_to_m_word_aux (c: cubical_generator) : word (cubical_generator_depth c)  := match c with 
  | cubic_base => null_word Empty_string
  | cubic_minus c' => let d := (cubical_to_m_word_aux c') in first_string_replace d (cons_str minus (word_first_pop d))
  | cubic_plus c' => let d := (cubical_to_m_word_aux c') in first_string_replace d (cons_str plus (word_first_pop d))
  | cubic_zero c' => cons_word Empty_string (cubical_to_m_word_aux c')
end.

Compute cubical_to_m_word_aux (cubic_plus (cubic_zero (cubic_zero (cubic_minus (cubic_plus (cubic_plus (cubic_zero (cubic_minus cubic_base)))))))).

Definition cubical_to_m_word (m:nat) (c: cubical_generator) := add_m_minus_at_start (m - (cubical_generator_length c)) (word_reversal (cubical_to_m_word_aux c)).

Compute cubical_to_m_word 0 (cubic_plus (cubic_zero (cubic_zero (cubic_minus (cubic_plus (cubic_plus (cubic_zero (cubic_minus cubic_base)))))))).

Fixpoint m_word_to_cubical_aux1 {m: nat} (s: string m) (c:cubical_generator) := match s with
  | Empty_string => c
  | cons_str minus s' => cubic_minus (m_word_to_cubical_aux1 s' c)
  | cons_str plus s' => cubic_plus (m_word_to_cubical_aux1 s' c)
  end.

Fixpoint m_word_to_cubical_aux_2 {n: nat} (w: word n) := match w with
  | null_word s => m_word_to_cubical_aux1 s cubic_base
  | cons_word s w' => m_word_to_cubical_aux1 s (cubic_zero (m_word_to_cubical_aux_2 w'))
  end.

Definition m_word_to_cubical {n:nat} (w:word n) := m_word_to_cubical_aux_2 (word_reversal w).

Compute m_word_to_cubical (cons_word (cons_str minus Empty_string) (cons_word Empty_string (cons_word cubical_three (null_word Empty_string)))).

Compute m_word_to_cubical (cons_word  Empty_string (cons_word Empty_string (cons_word cubical_three (null_word Empty_string)))).

Compute m_word_to_cubical (cons_word  Empty_string (cons_word Empty_string (cons_word cubical_three (null_word (cons_str minus Empty_string))))).

Lemma cubical_to_cubical (c: cubical_generator) : c = m_word_to_cubical (cubical_to_m_word (cubical_generator_length c) c).
unfold cubical_to_m_word. unfold m_word_to_cubical. rewrite sus_0_id. simpl. rewrite word_reversal_involution. induction c.
+ simpl; reflexivity.
+ simpl; induction (cubical_to_m_word_aux c); simpl; simpl in IHc; rewrite IHc; reflexivity.
+ simpl; induction (cubical_to_m_word_aux c); simpl; simpl in IHc; rewrite IHc; reflexivity.
+ simpl; rewrite <- IHc; reflexivity.
Defined.

Lemma TODO_word_back_to_word_aux {n:nat} (w:word n) : n = cubical_generator_depth (m_word_to_cubical w).
Admitted.

Definition word_back_to_word_aux {n:nat} (w: word n) : word n.
assert (n= (cubical_generator_depth (m_word_to_cubical w))). 2: { rewrite H. apply (cubical_to_m_word n (m_word_to_cubical w)). }
apply TODO_word_back_to_word_aux.
Defined.

Lemma word_back_to_word {n:nat} (w: word n) : w = word_back_to_word_aux w.
Admitted.

(*TODO cubical to word and back*)


Lemma principal_cubical_generator_depth (n:nat) : cubical_generator_depth (principal_cubical_generator n) = n.
induction n. + simpl; reflexivity.
+ simpl. rewrite IHn; reflexivity.
Defined.

Lemma principal_cubical_total_length (n: nat) : let c:= principal_cubical_generator n in  total_length (cubical_to_m_word (cubical_generator_depth c) c) = n.
simpl. unfold cubical_to_m_word. rewrite add_m_minus_at_start_0_identity. + rewrite <- reversed_total_length.
induction n.
- simpl. unfold string_length ; reflexivity.
- simpl. rewrite IHn; reflexivity.
+ induction n.
- simpl; reflexivity.
- simpl; apply IHn.
Defined.

Lemma principal_cubical_sent_to_principal_cell (n:nat) : let c := principal_cubical_generator n in cubical_to_m_word (cubical_generator_depth c) c = principal_cell_m (cubical_generator_depth c). 
simpl. apply length_is_word_length_implies_principal. rewrite principal_cubical_total_length. rewrite principal_cubical_generator_depth. reflexivity.
Defined.

End Cubical_words.

(*PART II*)

(*What we have so far is a way of going back and forth from simplicial generators to positive words and from cubical generators to words.
This part exploits ways of going from positive words to words to show paths bewteen simplicial generators and cubical generators.*)

Section Slice.

(*The slice on words takes a word and, if it is positive and has one zero, sends it to the corresponding positive word:*)

Definition word_slice {n:nat} (w : word (S n)) (proof: is_positive_word w):= sigma_proof w proof. 

(*A cubical generator with at least one zero and no minuses, which we will call a strictly positive cubical generator, produces such a word:*)

Fixpoint has_at_least_one_zero (c: cubical_generator) := match c with
  | cubic_base => False
  | cubic_minus c' => has_at_least_one_zero c'
  | cubic_plus c' => has_at_least_one_zero c'
  | cubic_zero c' => True
  end.

Fixpoint is_positive_cubical_generator (c: cubical_generator) := match c with
  | cubic_base => False
  | cubic_minus c' => False
  | cubic_plus c' => is_positive_cubical_generator c' \/ c' = cubic_base
  | cubic_zero c' => is_positive_cubical_generator c' \/ c' = cubic_base
  end.
  
Definition strictly_positive_cubical_generator := {c: cubical_generator | has_at_least_one_zero c /\ is_positive_cubical_generator c }.

Lemma strictly_positive_cubical_generator_depth (c: strictly_positive_cubical_generator) : exists p, cubical_generator_depth (proj1_sig c) = S p.
destruct c. simpl. induction x. + destruct a. simpl in H. destruct H.
+ destruct a. simpl in H0. destruct H0.
+ destruct a. simpl in H. simpl in H0. destruct H0.
- simpl. apply IHx. split; trivial.
- rewrite H0 in H. simpl in H. destruct H.
+ simpl. exists (cubical_generator_depth x); reflexivity.
Defined.

(*Non-null principal cubical generators are an example:*)

Lemma non_null_principal_is_strictly_positive_cubical (n:nat) : {c: cubical_generator | has_at_least_one_zero c /\ is_positive_cubical_generator c }.
apply (sigma_proof (principal_cubical_generator (S n))). split.
+ simpl; trivial.
+ induction n. - simpl. right; reflexivity.
- destruct IHn. * simpl. left. left. apply H.
* simpl. left. right. apply H.
Defined.

(*The slice is the operation that sends a strictly positive cubical generator to a simplicial generator through a word, in a way that decreases the dimension. We can of course come back too:*)

Definition generator_slice (c: strictly_positive_cubical_generator) : simplicial_generator.
apply (@positive_m_word_to_simplicial (pred_bis (cubical_generator_depth (proj1_sig c)))).
rewrite S_pred_can_be_id. 2:{ apply strictly_positive_cubical_generator_depth. } 
apply (sigma_proof (cubical_to_m_word (cubical_generator_depth (proj1_sig c)) (proj1_sig c))).
destruct c. simpl. induction x.
+ simpl; reflexivity.
+ destruct a. simpl in H0. destruct H0.
+ simpl. unfold cubical_to_m_word. assert (cubical_generator_depth x - cubical_generator_length (cubic_plus x) = 0).
- apply sus_lt_is_zero. simpl. apply le_S. apply depth_lt_length.
- rewrite H. simpl. assert (is_positive_word ((first_string_replace (cubical_to_m_word_aux x)  (cons_str plus (word_first_pop (cubical_to_m_word_aux x)))))).
2: { apply (word_reversal_mono (sigma_proof _ H0)). }
assert (is_positive_word (cubical_to_m_word_aux x)).
* unfold cubical_to_m_word in IHx. rewrite (sus_lt_is_zero _ _ (depth_lt_length _)) in IHx. simpl in IHx.
rewrite <- word_reversal_involution. assert (has_at_least_one_zero x /\ is_positive_cubical_generator x).
** split. 1: { destruct a. simpl in H0. apply H0. } destruct a. simpl in H1. destruct H1. 1:{ apply H1. } rewrite H1 in H0. simpl in H0. destruct H0.  
** apply (word_reversal_mono (sigma_proof _ (IHx H0))).
* assert (is_positive_string (cons_str plus (word_first_pop (cubical_to_m_word_aux x)))).
** split; trivial. apply (word_first_pop_mono (sigma_proof _ H0 )).
** apply (first_string_replace_mono (sigma_proof _ H0 ) (sigma_proof _ H1)).
+ simpl. unfold cubical_to_m_word. rewrite (sus_lt_is_zero (S (cubical_generator_depth x)) (cubical_generator_length (cubic_zero x))).
2: { simpl. apply (le_n_S _ _ (depth_lt_length x)). }
unfold add_m_minus_at_start. assert (is_positive_word (cubical_to_m_word_aux (cubic_zero x))).
2: { apply (word_reversal_mono (sigma_proof _ H)). } dependent induction x. 4:{ assert (is_positive_word (cubical_to_m_word_aux (cubic_zero x))).
2: { simpl in H. simpl. destruct H; split; auto. } assert (has_at_least_one_zero (cubic_zero x) /\ is_positive_cubical_generator (cubic_zero x) ).
+ simpl; split; auto. destruct a. simpl in H0. destruct H0.
* apply H0. * discriminate H0.
+ apply IHx0 in H. unfold cubical_to_m_word in H. rewrite (sus_lt_is_zero _ _ (depth_lt_length (cubic_zero x))) in H. unfold add_m_minus_at_start in H. 
rewrite <- word_reversal_involution. apply (word_reversal_mono (sigma_proof _ H)). }
- simpl; auto.
- destruct a. simpl in H0. destruct H0. * destruct H0. * discriminate H0. 
- assert (is_positive_word (cubical_to_m_word_aux (cubic_plus x))).
2:{ simpl in H. simpl. split; auto. } simpl. assert (is_positive_word (cubical_to_m_word_aux (cubic_zero x))).
2: { simpl in H. destruct H. assert (is_positive_string (cons_str plus (word_first_pop (cubical_to_m_word_aux x)))).
+ simpl; split; auto. apply (word_first_pop_mono (sigma_proof _ H0)).
+ apply (first_string_replace_mono (sigma_proof _ H0) (sigma_proof _ H1)). }
apply IHx. 
* split ; simpl; auto. destruct a. simpl in H0. destruct H0. ** apply H0. ** discriminate H0.
* simpl in IHx0. intro. assert (has_at_least_one_zero x /\ (is_positive_cubical_generator x \/ x = cubic_base)).
** destruct a0. split; trivial. left ; apply H0.
** apply IHx0 in H. unfold cubical_to_m_word in H. rewrite sus_lt_is_zero in H. 2: { simpl. apply le_S. apply depth_lt_length. } 
simpl in H. unfold cubical_to_m_word. rewrite (sus_lt_is_zero _ _ (depth_lt_length _)). simpl.
assert (is_positive_word (word_reversal (word_reversal (first_string_replace (cubical_to_m_word_aux x) (cons_str plus (word_first_pop (cubical_to_m_word_aux x))))))).
*** apply (word_reversal_mono (sigma_proof _ H)). *** rewrite word_reversal_involution in H0. apply first_string_replace_mono_back in H0.
destruct H0. simpl in H1. destruct H1. apply (word_reversal_mono (sigma_proof _  (first_and_tail_positive_imply_positive H2 H0))).
Defined.

Definition example_spc : strictly_positive_cubical_generator.
apply (sigma_proof (cubic_plus (cubic_zero (cubic_zero (cubic_plus (cubic_plus (cubic_zero (cubic_base)))))))).
split. + simpl; trivial.
+ simpl ; auto. left. left. left. left. left. right. trivial.
Defined.

Compute (generator_slice example_spc).

Lemma generator_slice_depth_coincidence (c: strictly_positive_cubical_generator) : cubical_generator_depth (proj1_sig c) = S (simplicial_generator_depth (generator_slice c)).
Admitted.

Definition cubical_to_simplicial_depth_change (c: strictly_positive_cubical_generator): word (S (simplicial_generator_depth (generator_slice c))).
rewrite <- generator_slice_depth_coincidence. apply (cubical_to_m_word (cubical_generator_depth (proj1_sig c))).
Defined.

Lemma generator_slice_word_coincidence (c: strictly_positive_cubical_generator) : cubical_to_simplicial_depth_change c = proj1_sig ( simplicial_to_positive_m_word (cubical_generator_depth (proj1_sig c)) (generator_slice c)).
simpl. Admitted.

Definition depth_lt_length_simplicial (s: simplicial_generator) : S (simplicial_generator_depth s) <= simplicial_generator_length s.
induction s. + simpl; auto.
+ simpl. apply (le_S _ _ IHs).
+ simpl. apply (le_n_S _ _ IHs).
Defined.

Lemma first_replace_is_pop_tail {n m:nat} (w: word (S n)) (s: string m) : first_string_replace w s = cons_word s (word_tail w).
dependent destruction w. simpl; auto.
Defined.

Lemma total_length_is_first_and_tail {n:nat} (w: word (S n)) : total_length w = S (word_first_length w + (total_length (word_tail w))).
dependent destruction w. simpl; auto.
Defined.

Lemma length_simplicial_to_m_word (s: simplicial_generator) : total_length (simplicial_to_m_word_aux s) = simplicial_generator_length s.
induction s. + simpl; auto.
+ simpl. rewrite first_replace_is_pop_tail. simpl. rewrite <- IHs. rewrite total_length_is_first_and_tail; auto.
+ simpl. rewrite IHs; auto.
Defined.

Lemma m_word_to_cubical_aux_2_mono {n:nat} (w: word n)(proof: is_positive_cubical_generator (m_word_to_cubical_aux_2 w)) : is_positive_word w .
induction w. 
- simpl. simpl in proof. induction s. * simpl; auto. * simpl. simpl in proof. destruct v.
** simpl in proof. split; trivial. destruct proof. *** apply (IHs H). *** induction s. -- simpl; trivial. -- simpl in H. destruct v; discriminate.
** simpl in proof. destruct proof.
- simpl. simpl in proof. induction s. * simpl in proof. split; simpl; trivial. destruct proof. ** apply (IHw H). ** destruct w.
-- simpl in H. induction s. --- simpl; trivial. --- simpl in H. destruct v ; discriminate.
-- simpl in H. destruct s. --- simpl in H; discriminate. ---  destruct v; simpl in H; discriminate.
* simpl in proof. destruct v. simpl in proof. destruct proof. ** apply IHs in H. destruct H.  split; simpl; auto. 
** destruct s. *** simpl in H; discriminate. *** destruct v; simpl in H; discriminate. 
** simpl in proof. destruct proof.
Defined.

Lemma m_word_to_cubical_aux_2_mono_back {n:nat} (w: word n)(proof: is_positive_word w) : is_positive_cubical_generator (m_word_to_cubical_aux_2 w) \/ m_word_to_cubical_aux_2 w = cubic_base.
induction w. + induction s. - simpl. right; auto.
- destruct v. * simpl. left. simpl in IHs. simpl in proof. destruct proof. apply (IHs H0).
* simpl in proof. destruct proof; discriminate.
+ simpl. induction s. - simpl. left. simpl in proof. destruct proof. apply (IHw H0). 
- destruct v. * simpl. left. apply IHs. simpl. simpl in proof. destruct proof. destruct H. auto.
* simpl in proof. destruct proof. destruct H; discriminate.
Defined.

Lemma generator_slice_inverse_aux (s: simplicial_generator) (proof: is_positive_cubical_generator (m_word_to_cubical_aux_2 (simplicial_to_m_word_aux s))) : is_positive_cubical_generator (m_word_to_cubical_aux_2 (word_tail (simplicial_to_m_word_aux s))) \/ m_word_to_cubical_aux_2 (word_tail (simplicial_to_m_word_aux s)) = cubic_base.
destruct s.
+ simpl. right. reflexivity.
+ simpl. rewrite first_replace_is_pop_tail. simpl. apply m_word_to_cubical_aux_2_mono in proof.
simpl in proof. rewrite first_replace_is_pop_tail in proof. simpl in proof. destruct proof.
apply (m_word_to_cubical_aux_2_mono_back _ H0).
+ simpl. simpl in proof. apply proof.
Defined. 

Definition generator_slice_inverse (s: simplicial_generator) : strictly_positive_cubical_generator.
apply (sigma_proof (m_word_to_cubical (simplicial_to_m_word (S (simplicial_generator_depth s)) s))). unfold simplicial_to_m_word.
assert (S (simplicial_generator_depth s) - total_length (word_reversal (simplicial_to_m_word_aux s)) = 0).
+ rewrite <- reversed_total_length. rewrite length_simplicial_to_m_word. apply (sus_lt_is_zero _ _ (depth_lt_length_simplicial _)).
+ rewrite H. unfold add_m_pluses_at_start. unfold m_word_to_cubical. rewrite word_reversal_involution.

dependent induction s. 
- simpl; auto.
- simpl. rewrite first_replace_is_pop_tail. simpl. split.
* induction (word_first_pop (simplicial_to_m_word_aux s)).
** simpl; auto. ** destruct v; simpl; apply IHs0.
* assert (is_positive_string (word_first_pop (simplicial_to_m_word_aux s))).
1:{ apply (word_first_pop_mono (sigma_proof _ (simplicial_word_is_positive_aux _))). }
 induction (word_first_pop (simplicial_to_m_word_aux s)).
** simpl. left. apply generator_slice_inverse_aux. destruct IHs. 2:{  apply H2. }
rewrite <- reversed_total_length. rewrite length_simplicial_to_m_word. apply (sus_lt_is_zero _ _ (depth_lt_length_simplicial _)). 
**  simpl. destruct v. -- simpl. left. apply IHs0. simpl in H0. destruct H0. apply H1.
-- simpl in H0. destruct H0. discriminate.
- simpl. split; trivial. apply m_word_to_cubical_aux_2_mono_back. apply simplicial_word_is_positive_aux.
Defined.
 
Lemma generator_slice_inversion_cubical (c: strictly_positive_cubical_generator) : proj1_sig c = proj1_sig (generator_slice_inverse (generator_slice (sigma_proof (proj1_sig c) (proj2_sig c) ))).
destruct c. simpl. Admitted.

Lemma generator_slice_inversion_simplicial (s: simplicial_generator) : s = generator_slice (generator_slice_inverse s).
Admitted.

(*TODO Inversions*)

End Slice.

Section Projection.

(*The projection on words takes a word and sends it to a lower dimensional positive word, in a non-injective manner:*)

Fixpoint string_projection_aux {n m:nat} (s: string n) (s': string m) := match s with
  | Empty_string => string_length s'
  | cons_str minus s'' => string_projection_aux s'' Empty_string
  | cons_str plus s'' => string_projection_aux s'' (cons_str plus s')
  end.

Definition string_projection {n m : nat} (s: string n) := add_m_pluses_at_start_string (string_projection_aux s Empty_string) Empty_string.

(*Fixpoint word_projection_aux {n m:nat} (w : word n) (w' : word m) := match w with
  | null_word s => 

Fixpoint word_projection {n:nat} (m:nat) (w : word n) := match w with
  | null_word s => add_m_minus_at_start m (cons_word Empty_string (null_word (word_projection_aux s)))
  | 
*)

(*TODO Projections*)

End Projection.

(*PART III*)

Section Orientations.

Definition 

End Orientations.

Section Simplicial_Orientals.

End Simplicial_Orientals.

Section Cubical_Orientals.

End Cubical_Orientals.






(*


Definition sub_word_aux {n m:nat} (w: word (S n)) (proof: total_length w <= m) : total_length (snd (non_zero_word_pop w)) <= (m - (S (word_first_length w))).
dependent destruction w. unfold word_first_length. unfold string_length. rewrite non_zero_word_pop_identity2. simpl. apply Nat.le_add_le_sub_l. simpl in proof. trivial.
Qed.

Definition sub_word {n m:nat} (w: word (S n)) (proof: total_length w <= m) : {x : word n | total_length x <= (m - (S (word_first_length w)))} :=
sigma_proof (snd (non_zero_word_pop w)) (sub_word_aux w proof).

Lemma six_leq_nine : 6 <= 9.
auto.
Qed.

Lemma sub_word_example_1 : proj1_sig (sub_word word_example_1 six_leq_nine) = zero_word (cons_str plus cubical_three).
unfold sub_word. unfold proj1_sig. unfold sigma_proof. unfold word_example_1. rewrite non_zero_word_pop_identity2_right.
trivial.
Qed. 



Compute simplicial_to_m_word_aux (simpl_plus (simpl_zero simpl_base) ).

Compute simplicial_to_m_word_aux (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).



Compute simplicial_to_m_word_aux (simpl_plus (simpl_zero simpl_base) ).

Compute word_reversal (m_simplicial_to_word_aux (simpl_plus (simpl_zero simpl_base) )).

Compute m_simplicial_to_word_aux (simpl_zero (simpl_plus (simpl_plus (simpl_zero (simpl_plus simpl_base))))).


(*TRY to fail*)
  



(* m_simplicial_to_word manages to send a simplicial generator in \mathcal{O}_n to a word of lenght m*)


unfold m_simplicial_to_word. assert ( is_positive_word (word_reversal (m_simplicial_to_word_aux t))).
2: { assert (word_reversal (m_simplicial_to_word_aux t) = proj1_sig (sigma_proof (word_reversal (m_simplicial_to_word_aux t)) H )) .
+ trivial.
+ rewrite H0. apply add_m_pluses_mono. }
dependent induction t.
+ simpl. auto.
+ simpl. Admitted.

(*word_reversal_is_mono ; m_simplicial_to_word_aux_is_mono*)


(*SUB_POSITIVE BROKE WITH NEW DEF ON IS_POSITIVE*)
Definition sub_positive_is_positive {n:nat} (w: @positive_word (S n)) {proof : 2 <= total_length (proj1_sig w)} : is_positive_word (snd (non_zero_word_pop (proj1_sig w))).
destruct w. simpl. dependent destruction x. rewrite non_zero_word_pop_identity2_right. dependent destruction string. + simpl in i. dependent destruction x.
- dependent destruction string. * simpl in proof. unfold string_length in proof. apply le_S_n in proof. apply Arith_prebase.le_n_0_eq_stt in proof. discriminate proof.
* Admitted. (* apply i.
- apply i.
+ simpl in i. destruct i. apply i0.
Defined.*)


(*apply sub_positive_is_positive. 
- dependent destruction w. simpl in H. dependent destruction x. rewrite non_zero_word_pop_identity2_right in H.
apply (left_simplicial_iteration m (IHn (sigma_proof x H))).
Defined. *)

(*SUB_POSITIVE BROKE WITH NEW DEF ON IS_POSITIVE*)


*)


(*-----------------------------------------

0 ->  source 0 := -; target 0 := +  || 0 : word 1 => - : word 0
-0+ => source -0+ := --+ ; target -0+ := -++ || -0+ : word 1 => --+ : word 0

source : word (S n) -> {word n | P n}

target_simplicial 000 : ((00+ , +00), proof: source 00+ = target +00)

target_cubique 000 : ((00+ , 0-0 , +00), proof : source 00+ = target 0-0)

target_X 000 : (..., x, ...) 

x => proof : source 00+ = target +00.

source 00+ = target +00

---------------------------------------------*)

(*(*Sigma T-types that differ at the base differ:*)

Definition sigmaT_proj1_contradiction {A:Type} {map: A -> Type } (a b : {x : A & map x} ) (proof : (projT1 a) <> (projT1 b)) : a <> b.
dependent destruction a. dependent destruction b. intro. destruct proof. simpl. apply (projT1_eq H).
Defined.

(*Likewise, sigma T-types that differ at the fiber, differ*)

Definition sigmaT_proj2_contradiction {A:Type} {map: A -> Type} (a b : {x : A & map x}) (proof : map (projT1 a) <> map (projT1 b)) : a <> b.
dependent destruction a. dependent destruction b. simpl in proof. intro. destruct proof. apply projT1_eq in H. simpl in H. rewrite H. reflexivity.
Defined.
*)



(*
Fixpoint word_to_m_simplicial_aux {n m: nat} (w: @positive_word n) (proof : total_length (proj1_sig w) <= m) (t:simplicial_generator) : simplicial_generator :=
match (proj1_sig (plus_filling w proof)) with
  | zero_word s => left_simplicial_iteration (string_length s) t
  | cons_word s w' => let y:= sub_word (cons_word s w') proof in left_simplicial_iteration (string_length s) (simpl_zero (word_to_m_simplicial_aux (proj1_sig y) (proj2_sig y)  t))
  end.
*)

(*
(*We define thus the product of nat with itself n times. clear_1 and clear_2 are identifying families of projections.*)

Fixpoint word (n:nat) := match n with
  |0 => fun m:nat_multiset 0 => non_zero_string (clear_1 m)
  |S(p) => fun m:nat_multiset (S p) => prod  (non_zero_string (clear_1 m)) (word p (@clear_2 p m))
  end.

(*We define a word as the concatenation of strings, morally separated by a zero*)

Definition word_example_1 : word 2 (2,(3,4)).
Proof.
simpl. split. + apply (cons_str plus (cons_str plus Empty_string)).
+ split. - apply (cons_str plus (cons_str plus (cons_str plus Empty_string))).
- apply (cons_str plus (cons_str plus (cons_str plus (cons_str plus Empty_string)))).
Defined.

(*We have constructed the word ++0+++0++++ .*)

*)
 
(*

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Inductive non_zero_symbols : Type :=
|plus
|minus.

(*The above defines the + and - symbols used in words*)

Inductive non_zero_string : nat -> Type :=
  |Empty_string : non_zero_string 0
  |cons_str : forall {n:nat} (s:non_zero_symbols), non_zero_string n -> non_zero_string (S(n)).

(*Inspired on the vector definition, we consider a string of non-zero characters with its length, with a zero string being
an empty string*)

Check Empty_string.

Check cons_str plus Empty_string.

Definition cubical_three := cons_str plus (cons_str plus Empty_string).
Check cubical_three.

(*cubical_three is the string ++, which represents 3 in the cubical faces*)

Definition zero_symbol : Type.
Proof.
apply True.
Qed.

(*I assume using True for the zero_symbol won't cause issues. Maybe False is a better option?*)

Inductive word : nat -> Type :=
  |zero_word : forall {m:nat} (string:non_zero_string m), word 0
  |cons_word : forall {n m:nat} (string: non_zero_string m), word n -> word (S(n)).

(*A word is either: a string containing no zeros; zeros separated by non-zero strings. The natural number thus gives
precisely the dimension in the cubical case*)

Check zero_word cubical_three.

(*This is ++*)

Definition word_example_1:= cons_word cubical_three (zero_word (cons_str plus cubical_three)).
Check word_example_1.
(*This is ++0+++*)

Definition string_length {m:nat} (s: non_zero_string m) := m.


Fixpoint total_length {m:nat} (w:word m):= match w with
  |zero_word s => string_length s
  |cons_word s w' => S(string_length s) + (total_length w')
  end.
  
Compute total_length (zero_word cubical_three).

Compute total_length word_example_1.

Definition cubical_word_dimension {m:nat} (w:word m) := m.

Compute cubical_word_dimension (zero_word cubical_three).

Compute cubical_word_dimension word_example_1.

Definition simplicial_word_dimension {m:nat} (w:word (S(m))) := m.

Fail Compute simplicial_word_dimension (zero_word cubical_three).

Compute simplicial_word_dimension word_example_1.

Inductive simplicial_generator:Type :=
  |simpl_base
  |simpl_left_branch : simplicial_generator -> simplicial_generator
  |simpl_right_branch : simplicial_generator -> simplicial_generator.

Inductive cubical_generator:Type :=
  |cubic_base
  |cubic_left_branch: cubical_generator -> cubical_generator
  |cubic_right_branch: cubical_generator -> cubical_generator
  |cubic_diagonal_branch: cubical_generator -> cubical_generator.

Fixpoint pos_proof {n:nat} := match n with
  |0 => cons_str plus Empty_string
  |S(m) => cons_str plus (pos_proof)
  end.
  
Compute @pos_proof 5.

Class positive_string {n:nat} := {string: non_zero_string (S(n)); positive_proof : string = pos_proof}.

#[refine] Instance positive_example : positive_string := {string := cubical_three}.
Proof.
simpl. reflexivity.
Defined.

#[refine] Instance positive_example_2 : positive_string :={string := ((cons_str plus cubical_three))}.
Proof.
simpl. reflexivity.
Defined.


Fixpoint nat_prod (n:nat) := match n with
  |0 => nat
  |S(p) => prod nat (nat_prod p)
  end.

Definition clear_i {n:nat} (m:nat_prod n) : nat. 
Proof.
induction n. + apply m. + destruct m. apply n0.
Defined.


Definition example_clear: clear_i ((2,3):nat_prod 1) = 2.
Proof.
simpl. reflexivity.
Qed.
  
Definition clear_j {n:nat} : ((nat_prod (S(n)) -> nat_prod n)) := fun m:nat_prod (S n) => snd m.  

Fixpoint positive_string_prod (n:nat) := match n with
  |0 => fun m:nat_prod 0 => @positive_string (clear_i m)
  |S(p) => fun m:nat_prod (S p) => prod  (@positive_string(clear_i m)) (@positive_string_prod p (@clear_j p m))
  end.
  
Definition pos_word_proof {n:nat} (m: nat_prod n):positive_string_prod n m -> word n.
Proof.
intro. induction n. + apply (@zero_word (S m)). destruct H. apply string0.
+ apply (@cons_word n (S (clear_i m))). - destruct H. apply p.
- destruct H. apply IHn in p0. apply p0.
Defined.


Definition clear_k {n:nat} (m:nat_prod n) (s: positive_string_prod n m) : @positive_string (clear_i m).
Proof.
induction n. + apply s. + destruct s. apply p.
Defined.

Definition example_2 : pos_word_proof (1:nat_prod 0) (positive_example : positive_string_prod 0 1 ) = zero_word (cubical_three).
simpl. auto. 
Qed.

Class positive_word {n:nat} (pos_word : word n) := {multi: nat_prod n ; l:positive_string_prod n multi ; positive_proof_word : pos_word = pos_word_proof multi l}.

Instance positive_word_example : positive_word word_example_1.
Proof. split with (1,2)  (positive_example, positive_example_2).
simpl. unfold word_example_1. reflexivity.
Qed.

Fixpoint weight_multiset (n:nat):= match n with
  |0 => fun (m:nat_prod 0) => S(clear_i m)
  |S(p) => fun (m:nat_prod (S p)) => S(S(clear_i m)) + weight_multiset p (clear_j m)
  end.

Compute weight_multiset 1 (3,2).

Lemma positive_word_length {n:nat}(w: word n)(p: positive_word w): total_length w = weight_multiset n p.(multi).

destruct p. rewrite positive_proof_word0. simpl.
induction w. + reflexivity.
+ destruct multi0. destruct l0. simpl in p0. assert (w = pos_word_proof n1 p0). 
- inversion positive_proof_word0. apply inj_pair2_eq_dec in H2. * apply H2.
* apply eq_nat_dec.
- apply (IHw n1 p0) in H. simpl. rewrite H. reflexivity.
Defined.

Fixpoint iterate_plus (m:nat) (s: simplicial_generator):= match m with
  |0 => s
  |S(p) => simpl_left_branch (iterate_plus p s)
  end.

Compute iterate_plus 3 (simpl_right_branch simpl_base).

Lemma length_limit: forall (n:nat) (w':word(S n)), total_length w' > 1.
Proof.
Admitted.




Definition word_to_simplicial_m_generator (m:nat) {n:nat}(w: word (S n))(size_proof : total_length w = S(m))(positive_proof : positive_word w) : simplicial_generator.
Proof.
induction n.
+ apply (iterate_plus m simpl_base).
+ inversion w. induction m. 
- assert (total_length w > 1).
* apply length_limit.
* Admitted.

*)

Definition Saved : 0 = 0.
auto.
Qed.

