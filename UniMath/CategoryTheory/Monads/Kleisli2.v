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

Coercion kleisli_functor_data {C:precategory} {T: C->C}(K: Kleisli_Data T): functor_data C C := mk_functor_data T (@map C T K).

Coercion is_functor_kleisli{C:precategory} {T: C->C}{K: Kleisli_Data T}(H: Kleisli_Laws K) : is_functor(kleisli_functor_data K) := map_id H ,, map_map H.
(*Proof.
  Search (dirprod).
  Check pr1.
  refine (tpair _ _  _).
  unfold functor_idax.
  simpl.
  exact (map_id H).
  exact (map_map H).
Defined.
Print is_functor_kleisli.*)

Coercion kleisli_functor{C: precategory} (K: Kleisli C) : functor C C :=  mk_functor K K.

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
(*
Coercion nat_trans_from_kleisli_mor {C : precategory}
           (T T' : Kleisli C) (s : Kleisli_Mor T T') :
  ∏ a : C, pr1 T a --> pr1 T' a := pr1 s.
 *)

Definition Kleisli_Mor_η {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  ∏ a : C, η T a · pr1 α a = η T' a :=
  pr1 (pr2 α).

Definition Kleisli_Mor_bind {C : precategory} {T T' : Kleisli C} (α : Kleisli_Mor T T') :
  (∏ (a b : C) (f : C⟦a,pr1 T b⟧), bind T' (pr1 α b ∘ f) ∘ pr1 α a = pr1 α b ∘ (bind T f)) :=
  pr2 (pr2 α).

Definition Kleisli_Mor_equiv {C : precategory} (hs : has_homsets C) {T T' : Kleisli C}
           (α β : Kleisli_Mor T T') :
  α = β ≃ (pr1 α = pr1 β).
Proof.
  apply subtypeInjectivity; intro a.
  apply isaprop_Kleisli_Mor_laws, hs.
Defined.

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
  Kleisli_Mor_laws (λ a : C, (pr1 α a) · (pr1 α' a)) T T''.
Proof.
  split; intros; simpl.
  - rewrite assoc.
    set (H := Kleisli_Mor_η α). rewrite H.
    apply Kleisli_Mor_η.
  - pathvia (pr1 α a · (pr1 α' a · bind T'' ((f · pr1 α b) · pr1 α' b))).
    * repeat rewrite assoc; apply idpath.
    * rewrite (Kleisli_Mor_bind α').
      rewrite assoc. rewrite (Kleisli_Mor_bind α).
      apply pathsinv0. apply assoc.
Qed.

Definition Kleisli_composition {C : precategory} {T T' T'' : Kleisli C}
           (α : Kleisli_Mor T T') (α' : Kleisli_Mor T' T'') :
  Kleisli_Mor T T'' :=
  (λ a : C, (pr1 α a) · (pr1 α' a)),, Kleisli_composition_laws α α'.

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

Definition forgetfunctor_Kleisli (C : category) :
  functor (category_Kleisli C) (functor_category C C).
Proof.
  use mk_functor.
  - simpl.
    use mk_functor_data.
    + simpl.
      exact (λ K: Kleisli C, kleisli_functor K).
    +
simpl. intros a b K.    
    apply (λ K, kleisli_functor_data K).
  - use mk_functor_data.
    + exact (fun M => pr1 M:functor C C).
    + exact (fun M N f => pr1 f).
  - abstract (split; red; intros;  reflexivity).
Defined.

Lemma forgetKleisli_faithful C : faithful (forgetfunctor_Kleisli C).
Proof.
  intros M N.
  apply isinclpr1.
  intros α.
  apply isaprop_Kleisli_Mor_laws.
  apply homset_property.
Qed.

End Kleisli_precategory.
