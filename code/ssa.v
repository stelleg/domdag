Require Import 
  Unicode.Utf8 
  Relations
  Equalities
  List
. 
Import ListNotations. 
Infix "∈" := In (at level 30). 
Notation "x '∉' y" := (¬ In x y) (at level 30). 
Set Implicit Arguments. 

Definition domain {a b} := map (@fst a b). 

Section ssa. 
Variable (label instr var : Type). 
Definition dec_eq a := ∀ x y : a, {x = y} + {x <> y}. 
Variable (var_eq : dec_eq var). 
Variable (label_eq : dec_eq label). 
Variable (entry : label).

Inductive term : Type := 
  | ret : term
  | jump : label → term
  | br : var → label → label → term
  .

Inductive bb : Type := 
  | bbinstr : instr → bb → bb
  | bbterm : term → bb
  . 

(* Every funcion must have an entry basic block *)
Definition function := list (label * bb). 

Fixpoint getTerm (b: bb) : term := match b with
  | bbinstr _ b' => getTerm b'
  | bbterm t => t
  end.

Definition outEdges (b : bb) : list label := match getTerm b with
  | jump l => [l]
  | br _ l l' => [l; l']
  | ret => []
  end.

Variable function_entry : ∀ f : function, entry ∈ domain f. 
Variable closed : ∀ (f : function) x y b, (x, b) ∈ f → y ∈ outEdges b → y ∈ domain f.

Definition cfg (f: function) : relation label := λ x y, ∃ b,
  (x, b) ∈ f ∧ y ∈ outEdges b. 

Definition path := list label. 

(* All paths start at entry, and are represented in reverse list order *) 
Fixpoint cfg_valid (p:path) f := match p with 
  | [] => False
  | [b] => b = entry
  | x::bs => match bs with
    | y::bs' => cfg f x y ∧ cfg_valid bs f
    | _ => False 
    end
  end.

Fixpoint ds_valid (p:path) f vs := match p with
  | [] => False
  | [b] => b = entry
  | x::bs => ∃ b, (x,b) ∈ f ∧ match bs with
    | y::bs' => match getTerm b with
      | ret => False
      | jump l => l = y ∧ ds_valid bs f vs
      | br v tb fb => (tb = y ∧ (v, false) ∉ vs ∧ ds_valid bs f ((v,true)::vs) ∨ 
                       fb = y ∧ (v, true) ∉ vs ∧ ds_valid bs f ((v,false)::vs))
      end
    | _ => False
    end
  end.

Inductive pathind (f : function) : label → Prop := 
  | entrypath : pathind f entry
  | jumppath : ∀ l l', 
      cfg f l l' → 
      pathind f l → 
      pathind f l'.

Inductive cfg_valid_ind : list label → function → Prop :=
  | cfg_head : ∀ f, cfg_valid_ind [entry] f 
  | cfg_tail : ∀ x y f ls, 
    cfg f x y → 
    cfg_valid_ind (y::ls) f → 
    cfg_valid_ind (x::y::ls) f.

Inductive ds_valid_ind : path → function → list (var*bool) → Prop :=
  | ds_head : ∀ f vs, ds_valid_ind [entry] f vs 
  | ds_jump : ∀ f vs x y bb ls, 
      (x, bb) ∈ f → getTerm bb = jump y →
      ds_valid_ind (y::ls) f vs →
      ds_valid_ind (x::y::ls) f vs
  | ds_brt : ∀ f v vs x tb fb bb ls, 
      (x, bb) ∈ f → getTerm bb = br v tb fb → (v,false) ∉ vs →
      ds_valid_ind (tb::ls) f ((v,true)::vs) →
      ds_valid_ind (x::tb::ls) f vs
  | ds_brf : ∀ f v vs x tb fb bb ls, 
      (x, bb) ∈ f → getTerm bb = br v tb fb → (v,true) ∉ vs →
      ds_valid_ind (fb::ls) f ((v,false)::vs) →
      ds_valid_ind (x::fb::ls) f vs
.

Lemma ds_valid_cfg : ∀ p f vs, ds_valid_ind p f vs → cfg_valid_ind p f.
intros. induction H. 
  - constructor. 
  - constructor. unfold cfg. exists bb0. split; auto. unfold outEdges. rewrite
    H0. unfold In; auto. assumption. 
  - constructor. unfold cfg. exists bb0. split; auto. unfold outEdges. rewrite
    H0. unfold In; auto. assumption. 
  - constructor. unfold cfg. exists bb0. split; auto. unfold outEdges. rewrite
    H0. unfold In; auto. assumption. 
Qed. 

Inductive before : label → label → path → Prop :=
  | before_head : ∀ x y p, before x y (x::p)
  | before_tail : ∀ x y z p, z ≠ y → before x y p → before x y (z::p).

Definition dominates (a b : label) (valid : path → Prop) : Prop := 
  ∀ p, valid p → b ∈ p → before a b p. 

Lemma cfg_dominates_ds : ∀ f a b vs, 
  dominates a b (λ p, cfg_valid_ind p f) →
  dominates a b (λ p, ds_valid_ind p f vs).
intros. unfold dominates in *. intros. apply ds_valid_cfg in H0. apply H;
assumption. Qed. 

(*
Inductive in_path (f:function) : ∀ l l', path f l' → Prop := 
  | entry_in : ∀ l' p, @in_path f entry l' p
  | jump_in : ∀ l0 l1 l2 cfgp p', 
      @in_path f l0 l1 p' → 
      @in_path f l0 l2 (jumppath cfgp p').
*)

(*
(* Data sensitive paths *)
Inductive ds_path (f : function) : label → list (var * bool) → Prop :=
  | entrydspath : ∀ vs, ds_path f entry vs
  | jumpdspath : ∀ l l' bb vs, 
      (l, bb) ∈ f → getTerm bb = jump l' → 
      ds_path f l vs → 
      ds_path f l' vs
  | brtrue : ∀ l lt lf bb v vs, 
    (l, bb) ∈ f → 
    getTerm bb = br v lt lf →
    (v, false) ∉ vs →
    ds_path f l vs →
    ds_path f lt ((v,true)::vs)
  | brfalse : ∀ l lt lf bb v vs, 
    (l, bb) ∈ f → 
    getTerm bb = br v lt lf →
    (v, true) ∉ vs →
    ds_path f l vs →
    ds_path f lf ((v,false)::vs)
 . 

Inductive in_ds_path (f:function) : ∀ l l' vs, ds_path f l' vs → Prop := 
  | entryds_in : ∀ l' p vs, @in_ds_path f entry l' p vs
  | jumpds_in : ∀ l0 l1 l2 bb pr1 pr2 vs p', 
      @in_ds_path f l0 l1 vs p' → 
      @in_ds_path f l0 l2 vs (jumpdspath bb pr1 pr2 p')
  | brtrue_in : ∀ v l0 l1 lf l2 bb pr1 pr2 vs pr3 p', 
      @in_ds_path f l0 l1 vs p' → 
      @in_ds_path f l0 l2 ((v,true)::vs) (@brtrue f l1 l2 lf bb v vs pr1 pr2 pr3 p')
  | brfalse_in : ∀ v l0 l1 lt l2 bb pr1 pr2 vs pr3 p', 
      @in_ds_path f l0 l1 vs p' → 
      @in_ds_path f l0 l2 ((v,false)::vs) (@brfalse f l1 lt l2 bb v vs pr1 pr2 pr3 p')
  .

Definition ds_dominates (f : function) (a b : label) : Prop :=
  ∀ (p:ds_path f b []), in_ds_path a p. 

Definition ds_path_path : ∀ f l vs (p : ds_path f l vs),
  { p':path f l | ∀ a, in_ds_path a p → in_path a p'}.
induction p. 
  - apply entrypath. 
  - apply jumppath with (l:=l); auto. 
    + unfold cfg. exists bb0. split; auto. unfold outEdges. rewrite H0. unfold
      In. auto.  
  - apply jumppath with (l:=l); auto. 
    + unfold cfg. exists bb0. split; auto. unfold outEdges. rewrite H0. unfold
      In.  auto. 
  - apply jumppath with (l:=l); auto. 
    + unfold cfg. exists bb0. split; auto. unfold outEdges. rewrite H0. unfold
      In.  auto. 
Qed. 

Lemma path_in_ds_path : ∀ f l a (p : ds_path f l []), in_ds_path a p → 
  in_path a (ds_path_path p).
intros. induction H. 
  - constructor. 
  - simpl. unfold ds_path_path.

Lemma ds_path_cfg : ∀ p f vs, ds_valid p f vs → cfg_valid p f. 
intros. 
induction p. auto. destruct p. inversion H. simpl. auto. inversion H. destruct
H0. simpl. split. unfold cfg. exists x. split; auto. unfold outEdges. destruct
(getTerm x) eqn:gt. inversion H1. destruct H1. subst. unfold In. apply
or_introl. auto. destruct H1. destruct H1. subst. unfold In. apply or_introl.
auto. destruct H1. subst. unfold In. apply or_intror. auto. apply IHp. destruct
(getTerm x). inversion H1. destruct H1. auto. destruct H1; destruct H1; destruct
H2; auto. subst. simpl in H3. destruct p; auto. destruct H3. destruct H1. simpl.
exists x0.  H. onstructor.   
Lemma dominates_ds_dominates : ∀ f a b, dominates f a b → ds_dominates f a b.
intros. 
unfold dominates in *. unfold ds_dominates. intros. induction H with
(p:=(ds_path_path p)). constructor. switch. specialize (H (ds_path_path
p)). induction H. constructor. unfold cfg in cfgp. destruct cfgp. unfold
outEdges in H0. destruct H0. destruct (getTerm x) eqn:term. inversion H1. eapply
jumpdspath in p. . generalize dependent a. generalize dependent vs.  induction H; auto; intros. constructor. inversion p. subst. apply IHin_path. constructor.  simpl. apply ds_path_path in p.  in H.  
apply H in H0. assumption . 
Qed. 
*)

(* TODO: Need better inducive proof structures to prove this *)
Lemma tree_sufficient : ∀ f a b c,  
  dominates a c (λ p, cfg_valid_ind p f) → 
  dominates b c (λ p, cfg_valid_ind p f) → 
  dominates a b (λ p, cfg_valid_ind p f) ∨ 
  dominates b a (λ p, cfg_valid_ind p f).
intros. unfold dominates.    


intros.
unfold dominates in *. constructor. 
f_equal. 
Admitted.

Lemma 



End ssa. 

