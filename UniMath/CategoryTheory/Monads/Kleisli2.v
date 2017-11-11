(* ============================================================================================= *)
(** * Kleisli Monads                                                                             *)
(*                                                                                               *)
(* Contents:                                                                                     *)
(*                                                                                               *)
(*         - Theory of monads based on the haskell-style bind operartor.                         *)
(*         - Category of Kleisli monads [category_Kleisli C] on [C]                              *)
(*         - Forgetful functor [forgetfunctor_Kleisli] from monads to endofunctors on [C]        *)
(*                                                                                               *)
(* Written by: Marco Maggesi (2017)                                                              *)
(*                                                                                               *)
(* ============================================================================================= *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Monads.Monads.
Section Kleisli_precategory.

Local Open Scope cat.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(* --------------------------------------------------------------------------------------------- *)
(* ** Definition of Kleisli monad.                                                               *)
(* --------------------------------------------------------------------------------------------- *)


(* ----- Datatype for Kleisli data ----- *)
Definition Kleisli_Data {C : precategory} (F : C → C): UU :=
  (∏ a : C, a --> F a) × (∏ a b : C, (a --> F b) → (F a --> F b)).

(* ----- Projections ----- *)
Definition η {C : precategory} {F : C → C} (K : Kleisli_Data F) : ∏ a : C, a --> F a := pr1 K.

Definition bind {C : precategory} {F : C → C} (K : Kleisli_Data F) {a b : C} :
  C⟦a,F b⟧ → C⟦F a,F b⟧ := pr2 K a b.

Definition Kleisli_Laws {C : precategory} {T : C → C} (K : Kleisli_Data T) :=
  (∏ a b (f : C⟦a,T b⟧) c (g : C⟦b,T c⟧), bind K g ∘ bind K f = bind K (bind K g ∘ f)) ×
  (∏ a b (f : C⟦a,T b⟧), bind K f ∘ η K a = f) ×
  (∏ a, bind K (η K a) = identity (T a)).

Lemma isaprop_Kleisli_Laws {C : precategory}
        (hs : has_homsets C) {T : C → C} (K : Kleisli_Data T) :
  isaprop (Kleisli_Laws K).
Proof.
  repeat apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Qed.

Definition bind_bind {C : precategory} {T : C → C} {K : Kleisli_Data T} :
  Kleisli_Laws K
  → (∏ a b (f : C⟦a,T b⟧) c (g : C⟦b,T c⟧), bind K g ∘ bind K f = bind K (bind K g ∘ f)) :=
  pr1.

Definition bind_η {C : precategory} {T : C → C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  (∏ a b (f : C⟦a,T b⟧), bind K f ∘ η K a = f):= pr1 (pr2 H).

Definition η_bind {C : precategory} {T : C → C} {K : Kleisli_Data T} (H : Kleisli_Laws K) :
  (∏ a, bind K (η K a) = identity (T a)) := pr2 (pr2 H).

Definition Kleisli (C : precategory) : UU :=
  ∑ (T : C → C) (K : Kleisli_Data T), Kleisli_Laws K.

Coercion kleisly_data {C : precategory} (T : Kleisli C) : Kleisli_Data (pr1 T) := pr1 (pr2 T).

Coercion kleisly_laws {C : precategory} (T : Kleisli C) : Kleisli_Laws T := pr2 (pr2 T).

Definition map {C:precategory} {T: C->C}(K: Kleisli_Data T){a b: C}(f: a-->b): T(a)-->T(b) := bind K (η K b ∘ f).

Lemma map_id {C:precategory} {T: C->C}{K: Kleisli_Data T}(H: Kleisli_Laws K): ∏ a:C, map K (identity a) = identity (T a).
Proof.
  intro.
  unfold map.
  rewrite id_left.
  apply η_bind.
  apply H.
Qed.

Lemma map_map{C:precategory} {T: C->C}{K: Kleisli_Data T}(H:Kleisli_Laws K):∏(a b c: C) (f: a-->b) (g:b-->c), map K (g ∘ f) = map K g ∘ map K f.
Proof.
  intros.
  unfold map.
  rewrite bind_bind.
  do 2 rewrite <- assoc.
  rewrite bind_η.
  apply idpath.
  assumption. assumption.
Qed.

Lemma map_bind{C:precategory} {T: C->C}{K: Kleisli_Data T}(H:Kleisli_Laws K) : ∏ (a b c: C) (f:b-->c) (g:a--> T b), (map K f) ∘ (bind K g) = (bind K (map K f ∘ g)).
Proof.
  intros.
  unfold map.
  rewrite (bind_bind H).
     apply idpath.
Qed.

Lemma bind_map{C:precategory} {T: C->C}{K: Kleisli_Data T}(H:Kleisli_Laws K) : ∏ (a b c: C) (f:b-->T c) (g:a-->b), (bind K f) ∘ (map K g) = (bind K (f ∘ g)).
Proof.
  intros.
  unfold map.
  rewrite (bind_bind H).
  rewrite <- assoc.
  rewrite bind_η.
  apply idpath.
  apply H.
Qed.

Lemma map_η{C:precategory} {T: C->C}{K: Kleisli_Data T}(H:Kleisli_Laws K) : ∏ (a b: C) (f: a --> b), map K f ∘ η K a = η K b ∘ f.
Proof.
  intros.
  unfold map.
  rewrite (bind_η H).
  apply idpath.
  Qed.

Definition kleisli_functor_data {C:precategory} {T: C->C}(K: Kleisli_Data T): functor_data C C := mk_functor_data T (@map C T K).

Definition is_functor_kleisli{C:precategory} {T: C->C}{K: Kleisli_Data T}(H: Kleisli_Laws K) : is_functor(kleisli_functor_data K) := map_id H ,, map_map H.

Definition kleisli_functor{C: precategory} (K: Kleisli C) : functor C C :=  mk_functor (kleisli_functor_data K) (is_functor_kleisli K).

(*
Definition kleisli_μ {C: precategory} (K: Kleisli C) : K □ K ⟹ K.
Proof.
  refine ((λ x:C, bind K (identity (K x))) ,, _ ).
  unfold is_nat_trans. intros. simpl.
  rewrite (map_bind K).
  rewrite (bind_map K).
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Defined.*)

Lemma is_nat_trans_η {C: precategory}(K: Kleisli C): is_nat_trans (functor_identity C) (kleisli_functor K) (η K).
Proof.
  unfold is_nat_trans.
  simpl. intros. rewrite (map_η K). apply idpath.
Qed.

Definition nat_trans_η {C: precategory}(K: Kleisli C) : functor_identity C ⟹ kleisli_functor K := (η K ,, is_nat_trans_η K).




(* --------------------------------------------------------------------------------------------- *)
(* ** Morphims of Kleisli monads.                                                                *)
(* --------------------------------------------------------------------------------------------- *)

Definition Kleisli_Mor_laws {C : precategory} {T T' : C → C}
             (α : ∏ a : C, T a --> T' a) (K : Kleisli_Data T) (K' : Kleisli_Data T') : UU :=
  (∏ a : C, α a ∘ η K a = η K' a) ×
  (∏ (a b : C) (f : C⟦a,T b⟧), bind K' (α b ∘ f) ∘ α a = α b ∘ (bind K f)).

Lemma isaprop_Kleisli_Mor_laws {C : precategory} (hs : has_homsets C) {T T' : C → C}
        (α : ∏ a : C, T a --> T' a) (K : Kleisli_Data T) (K' : Kleisli_Data T') :
  isaprop (Kleisli_Mor_laws α K K').
Proof.
  apply isapropdirprod; repeat (apply impred_isaprop; intros); apply hs.
Qed.

Definition Kleisli_Mor {C : precategory} (T T' : Kleisli C) : UU :=
  ∑ (α : ∏ a : C, pr1 T a --> pr1 T' a), Kleisli_Mor_laws α T T'.

(* Non funziona! *)

Definition nat_trans_from_kleisli_mor {C : precategory}
           {T T' : Kleisli C} (s : Kleisli_Mor T T') :
  ∏ a : C, pr1 T a --> pr1 T' a := pr1 s.

Definition Kleisli_Mor_η {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  ∏ a : C, η T a · nat_trans_from_kleisli_mor  α a = η T' a :=
  pr1 (pr2 α).

Definition Kleisli_Mor_bind {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  (∏ (a b : C) (f : C⟦a,pr1 T b⟧), bind T' (nat_trans_from_kleisli_mor α b ∘ f) ∘ nat_trans_from_kleisli_mor α a = nat_trans_from_kleisli_mor α b ∘ (bind T f)) :=
  pr2 (pr2 α).

Definition Kleisli_Mor_equiv {C : precategory} (hs : has_homsets C) {T T' : Kleisli C}
           (α β : Kleisli_Mor T T') :
  α = β ≃ (nat_trans_from_kleisli_mor α = nat_trans_from_kleisli_mor β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_Kleisli_Mor_laws, hs.
Defined.

Lemma is_nat_trans_kleisli_mor{C : precategory}{T T' : Kleisli C} (α : Kleisli_Mor T T') : is_nat_trans (kleisli_functor T) (kleisli_functor T') (nat_trans_from_kleisli_mor α).
Proof.
  unfold is_nat_trans. intros. simpl.
  unfold map.
  rewrite <- (Kleisli_Mor_bind α).
  rewrite <- assoc.
  rewrite (Kleisli_Mor_η α).
  apply idpath.
Qed.

Definition nat_trans_kleisli_mor {C : precategory}{T T' : Kleisli C} (α : Kleisli_Mor T T') : nat_trans (kleisli_functor T) (kleisli_functor T') := mk_nat_trans (kleisli_functor T) (kleisli_functor T') (nat_trans_from_kleisli_mor α) (is_nat_trans_kleisli_mor α).

Lemma Kleisli_Mor_eq {C : precategory}(hs: has_homsets C){T T' : Kleisli C}(α α' : Kleisli_Mor T T') :
  nat_trans_from_kleisli_mor α  = nat_trans_from_kleisli_mor α' -> α = α'.
Proof.
  intros.
  apply subtypeEquality'.
  + assumption.
  + apply isaprop_Kleisli_Mor_laws.
    apply hs.
Qed.
(* --------------------------------------------------------------------------------------------- *)
(* Identity morphism.                                                                            *)
(* --------------------------------------------------------------------------------------------- *)


Lemma Kleisli_identity_laws {C : precategory} (T : Kleisli C) :
  Kleisli_Mor_laws (λ a : C, identity (pr1 T a)) T T.
Proof.
  split; intros a; simpl.
  - apply id_right.
  - intros. repeat rewrite id_right; apply id_left.
Qed.

Definition Kleisli_identity {C : precategory} (T : Kleisli C) : Kleisli_Mor T T :=
  (λ a : C, identity (pr1 T a)),, Kleisli_identity_laws T.

(* --------------------------------------------------------------------------------------------- *)
(* Composition of morphisms.                                                                     *)
(* --------------------------------------------------------------------------------------------- *)

Lemma Kleisli_composition_laws {C : precategory} {T T' T'' : Kleisli C}
        (α : Kleisli_Mor T T') (α' : Kleisli_Mor T' T'') :
  Kleisli_Mor_laws (λ a : C, (nat_trans_from_kleisli_mor α a) · (nat_trans_from_kleisli_mor α' a)) T T''.
Proof.
  split; intros; simpl.
  - rewrite assoc.
    set (H := Kleisli_Mor_η α). rewrite H.
    apply Kleisli_Mor_η.
  - pathvia (nat_trans_from_kleisli_mor α a · (nat_trans_from_kleisli_mor α' a · bind T'' ((f · nat_trans_from_kleisli_mor α b) · nat_trans_from_kleisli_mor α' b))).
    * repeat rewrite assoc; apply idpath.
    * rewrite (Kleisli_Mor_bind α').
      rewrite assoc. rewrite (Kleisli_Mor_bind α).
      apply pathsinv0. apply assoc.
Qed.

Definition Kleisli_composition {C : precategory} {T T' T'' : Kleisli C}
           (α : Kleisli_Mor T T') (α' : Kleisli_Mor T' T'') :
  Kleisli_Mor T T'' :=
  (λ a : C, (nat_trans_from_kleisli_mor α a) · (nat_trans_from_kleisli_mor α' a)),, Kleisli_composition_laws α α'.

(* --------------------------------------------------------------------------------------------- *)
(* Precategory of Kleisli monads.                                                                *)
(* --------------------------------------------------------------------------------------------- *)

Definition precategory_Kleisli_ob_mor (C : precategory) : precategory_ob_mor :=
  precategory_ob_mor_pair (Kleisli C) Kleisli_Mor.

Definition precategory_Kleisli_Data (C : precategory) : precategory_data :=
  precategory_data_pair (precategory_Kleisli_ob_mor C)
                        (@Kleisli_identity C)
                        (@Kleisli_composition C).

Lemma precategory_Kleisli_axioms (C : precategory) (hs : has_homsets C) :
  is_precategory (precategory_Kleisli_Data C).
Proof.
  repeat split; simpl; intros.
  - apply (invmap (Kleisli_Mor_equiv hs _ _ )).
    apply funextsec. intros x. apply id_left.
  - apply (invmap (Kleisli_Mor_equiv hs _ _ )).
    apply funextsec. intros x. apply id_right.
  - apply (invmap (Kleisli_Mor_equiv hs _ _ )).
    apply funextsec. intros x. apply assoc.
Qed.

Definition precategory_Kleisli (C : precategory) (hs : has_homsets C) : precategory :=
  precategory_Kleisli_Data C,, precategory_Kleisli_axioms C hs.

Lemma has_homsets_Kleisli (C : category) : has_homsets (precategory_Kleisli C (homset_property C)).
Proof.
  intros F G; simpl.
  unfold Kleisli_Mor.
  apply isaset_total2 .
  apply impred_isaset.
  intro; apply C.
  intros.
  Search isaprop isaset.
  apply isasetaprop.
  apply isaprop_Kleisli_Mor_laws.
  apply C.
Qed.

Definition category_Kleisli (C : category) : category :=
  precategory_Kleisli C (homset_property C),, has_homsets_Kleisli C.
(*Set Printing Coercions.*)
Definition forgetfunctor_Kleisli (C : category) :
  functor (category_Kleisli C) (functor_category C C).
Proof.
  use mk_functor.
  - simpl.
    use mk_functor_data.
    + simpl.
      exact (λ K: Kleisli C, kleisli_functor K).
    + simpl. intros T T' K.
      exact  (nat_trans_kleisli_mor K).
  -(*Sarebbe opportuno usare abstract*) split.
    + red. intros. simpl. apply nat_trans_eq.
      * apply C.
      * intros; apply idpath.
    + unfold functor_compax. simpl. intros. apply nat_trans_eq.
      * apply C.
      * intros. apply idpath.
Defined.
(*Set Printing Coercions.*)
Lemma forgetKleisli_faithful C : faithful (forgetfunctor_Kleisli C).
Proof.
  intros K K'.
  simpl.
  apply isinclbetweensets.
  - apply isaset_total2.
    + apply impred_isaset.
      intros. apply C.
    + intros. apply isasetaprop. apply isaprop_Kleisli_Mor_laws. apply C.
  - apply isaset_nat_trans. apply C.
  - intros f g p.
    apply Kleisli_Mor_eq.
    + apply C.
    + apply funextsec. intro X. change(pr1 (nat_trans_kleisli_mor f) X = pr1 (nat_trans_kleisli_mor g) X).
      rewrite p.
      apply idpath.
Qed.

(*Monad from Kleisli*)


Definition kleisli_μ {C: precategory} (K: Kleisli C) : kleisli_functor K □ kleisli_functor K ⟹ kleisli_functor K.
Proof.
  refine ((λ x:C, bind K (identity (kleisli_functor K x))) ,, _ ).
  unfold is_nat_trans. intros. simpl.
  rewrite (map_bind K).
  rewrite (bind_map K).
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Defined.



Definition Kleisli_Monad_data {C: precategory}(T: Kleisli C) : Monad_data C.
Proof.
  unfold Monad_data.
  exact (((kleisli_functor T) ,, kleisli_μ T ) ,, nat_trans_η T  ).
Defined.

Lemma Monad_laws_kleisli_monad_data {C : precategory}(T : Kleisli C) : (Monad_laws (Kleisli_Monad_data T)).
Proof.
unfold Monad_laws.
simpl.
split.
+ split. intros. apply (bind_η T). intros. rewrite (bind_map T).
  rewrite id_right.
  apply (η_bind T).
+ intros. rewrite (bind_map T). rewrite id_right.
  rewrite (bind_bind T). rewrite id_left.
  apply idpath.
Qed.

Definition Monad_from_Kleisli{C: precategory}(T: Kleisli C) : Monad C :=
  (Kleisli_Monad_data T ,, Monad_laws_kleisli_monad_data T).

Lemma Monad_Mor_laws_Kleisli_Mor{C: precategory}{T T': Kleisli C}(α: Kleisli_Mor T T') : Monad_Mor_laws (T:=Monad_from_Kleisli T)(T':=Monad_from_Kleisli T')(nat_trans_kleisli_mor α).
Proof.
  split.
  +  intros. simpl.
     rewrite <- assoc.
     rewrite (bind_map T').
     rewrite id_right.
     rewrite <- (Kleisli_Mor_bind α).
     rewrite id_left.
     apply idpath.
  + intros. simpl. apply Kleisli_Mor_η.
Qed.

Definition Monad_Mor_from_Kleisli_Mor{C: precategory}{T T': Kleisli C}(α: Kleisli_Mor T T') : Monad_Mor (Monad_from_Kleisli T) (Monad_from_Kleisli T') := (nat_trans_kleisli_mor α ,, Monad_Mor_laws_Kleisli_Mor α).

Definition functor_data_monad_from_kleisli(C: precategory)(hs: has_homsets C): functor_data (precategory_Kleisli C hs) (precategory_Monad C hs).
Proof.
  refine (@mk_functor_data(precategory_Kleisli C hs) (precategory_Monad C hs) (λ T: Kleisli C, Monad_from_Kleisli T) _).
  intros.
  apply Monad_Mor_from_Kleisli_Mor.
  exact X.
Defined.

Lemma is_functor_monad_from_kleisli{C: precategory}(hs: has_homsets C): is_functor (functor_data_monad_from_kleisli C hs).
Proof.
  split.
  + red. simpl.
    intros.
    unfold Monad_Mor_from_Kleisli_Mor.
    apply subtypeEquality'.
  - simpl. apply subtypeEquality'.
    * simpl. apply funextsec. intro x. apply idpath.
    * apply isaprop_is_nat_trans.
      assumption.
  - apply isaprop_Monad_Mor_laws.
    assumption.

    + red. simpl. intros. apply subtypeEquality'.
  - simpl. apply subtypeEquality'.
    * simpl. apply funextsec. intro x. apply idpath.
    * apply isaprop_is_nat_trans.
      assumption.
  - apply isaprop_Monad_Mor_laws.
    assumption.
Qed.

Definition functor_Monad_from_Kleisli{C: precategory}(hs: has_homsets C) : functor (precategory_Kleisli C hs) (precategory_Monad C hs) := ((functor_data_monad_from_kleisli C hs) ,, is_functor_monad_from_kleisli hs).

Definition Monad_Kleisli_data{C:precategory}(M: Monad_data C) : Kleisli_Data M.
Proof.
  unfold Kleisli_Data.
  split.
  - exact (Monads.η M).
  - intros a b f.
    exact ((Monads.μ M) b ∘ # M f).
Defined.

Lemma Monad_Kleisli_laws{C:precategory}(M: Monad C) : Kleisli_Laws (Monad_Kleisli_data M).
 (* Set Printing Coercions.
  Set Printing Implicit.*)
Proof.
  split.
  - simpl. intros. rewrite assoc. rewrite (functor_comp M).
    rewrite assoc4. set (H := Monad_law5 (T:=M) g). simpl in H.
    rewrite <- H. rewrite functor_comp. do 2 rewrite <- assoc4.
    set (H2 := Monad_law3 (T:=M) c). simpl in H2.
    repeat rewrite <- assoc. rewrite <- H2. apply idpath.

  - split.
    + simpl. intros. rewrite assoc. set (H := Monad_law4 (T:= M) f).
      simpl in H. rewrite H. rewrite <- assoc.
      set (H2 := Monad_law1 (T:=M) b). simpl in H2.
      rewrite H2. apply id_right.
    + intros. simpl. apply Monad_law2.
Qed.

Definition Kleisli_from_Monad {C : precategory}(M : Monad C) : Kleisli C :=
  ((λ x, M x) ,, Monad_Kleisli_data M ,, Monad_Kleisli_laws M).

Lemma Kleisli_Mor_law_from{C : precategory} {M M' : Monad C}(α : Monad_Mor M M'): Kleisli_Mor_laws (λ x : C, α x) (Kleisli_from_Monad M) (Kleisli_from_Monad M').
Proof.
  split.
  - simpl. intros. apply Monad_Mor_η.
  - simpl. intros. rewrite functor_comp. repeat rewrite assoc.
    set (H := nat_trans_ax α). simpl in H. rewrite <- H. rewrite assoc4.
    rewrite <-H. rewrite <- assoc4. set (H2 :=  Monad_Mor_μ α b).
    simpl in H2. repeat rewrite <- assoc. rewrite H2.
    repeat rewrite assoc. repeat rewrite assoc4. rewrite H.
    apply idpath.
Qed.

Definition Kleisli_Mor_from_Monad_Mor{C : precategory} {M M' : Monad C}(α : Monad_Mor M M') : Kleisli_Mor (Kleisli_from_Monad M) (Kleisli_from_Monad M').
Proof.
  refine ((λ x:C, α x) ,, _).
  apply Kleisli_Mor_law_from.
Defined.
Require Import UniMath.CategoryTheory.catiso.

Lemma Kleisli_data_eq {C : precategory}{F : C → C}(K K' : Kleisli_Data F) :  (∏ a:C, η K a = η K' a) → (∏ (a b : C) (f: a --> F b), bind K f = bind K' f) → K = K'.
Proof.
  intros. apply dirprod_paths.
  - change (η K = η K'). apply funextsec. intro a. apply X.
  - apply funextsec. intro a. apply funextsec. intro b. apply funextfun.
    intro f. apply X0.
Qed.

(*Lemma Kleisli_eq {C : precategory}(T T' : Kleisli C) : (∏ a:C, pr1 T a = pr1 T' a) → (∏ (a b:C) (f:ab), bind T f = bind T' f (b:=b)) → (∏ a:C, η T a = η T' a).
Proof.*)

Lemma lem1{C : precategory}(T : Kleisli C) : Monad_Kleisli_data (Kleisli_Monad_data T) = T.
Proof.
  apply pair_path_in2.
  simpl. apply funextsec. intro a. apply funextsec. intro b.
    apply funextfun. intro f. abstract (simpl; rewrite (bind_map T);
    rewrite id_right; apply idpath).
Defined.

Lemma hmpt1{C : precategory}(hs: has_homsets C)(T : Kleisli C) : Kleisli_from_Monad ( Monad_from_Kleisli T) = T.
Proof.
  unfold Monad_from_Kleisli. unfold Kleisli_from_Monad. simpl. destruct T as (F , (K , L)). simpl. change (λ x:C, F x) with F. apply (pair_path_in2). apply subtypeEquality'.
  2: apply (isaprop_Kleisli_Laws hs K).
  simpl. apply (lem1 (F,, K,, L)).
Defined.

Lemma is_catiso{C:precategory}(hs:has_homsets C) : is_catiso(functor_Monad_from_Kleisli hs).
Proof.
  unfold is_catiso.
  split.
  - unfold fully_faithful.
    simpl.
    intros.
    apply (set_bijection_to_weq).
    2: apply isaset_Monad_Mor; assumption.
    + split.
      * intros. set (y':= (Kleisli_Mor_from_Monad_Mor y)).
        set (Ha:= hmpt1 hs a). set (Hb:= hmpt1 hs b).
        set (y'':= transportf (λ a,  Kleisli_Mor  a (Kleisli_from_Monad (Monad_from_Kleisli b)))  Ha y'). simpl in y''.
        set (y''':= transportf (λ b,  Kleisli_Mor  a b)  Hb y'').
        simpl in y'''.
        refine (y''' ,, _).
        apply subtypeEquality'.
        2: apply isaprop_Monad_Mor_laws; assumption.
        simpl.
        apply (nat_trans_eq hs).
        destruct y as (y , Hy).
        simpl in y'.
        simpl in y''.
        intros. simpl.
        destruct y as (f , h).
        simpl.
        simpl in y'.
        Print nat_trans_eq.








End Kleisli_precategory.
