From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)

Section Transformer.
  Definition sumt (R:Type) : (Type -> Type) -> Type -> Type :=
    fun m A => m (R + A:Type).
  Definition mult (R:Type) (idx:R) (op:Monoid.law idx)
  : (Type -> Type) -> Type -> Type :=
    fun m A => m (R * A:Type).
  Definition appt (R:Type) : (Type -> Type) -> Type -> Type :=
    fun m A => R -> m A.
  Definition statet (R:Type) : (Type -> Type) -> Type -> Type :=
    fun m A => R -> m (R * A:Type).
End Transformer.

(* ********************* *)

Module Pure.
  Definition Eta (m:Type -> Type) := forall A, A -> m A.

  Record class_of (m:Type -> Type) :=
    Class {
        eta : Eta m;
      }.

  Section ClassDef.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation pureMap := map.
    Notation Eta := Eta.
    Definition eta T := (eta (class T)).
  End Exports.
End Pure.
Import Pure.Exports.

Section Pure_lemma.
  Variable (m:pureMap).
  Let eta := eta m.
End Pure_lemma.

Definition eq_pureMap (m:Type -> Type) (c d:Pure.class_of m) :=
  forall A, @eta (Pure.Pack c) A =1 @eta (Pure.Pack d) _.

Section Pure_canonicals.
  (* id *)
  Definition id_pure_class_of : Pure.class_of id := Pure.Class (fun A x => x).
  Definition id_pureMap : pureMap :=
    Eval hnf in @Pure.Pack id id_pure_class_of.

  (* comp *)
  Definition comp_pure_class_of (m n:pureMap) :
    Pure.class_of (fun A => m (n A)) :=
    Pure.Class (fun _ => (@eta m _ \o @eta n _)).
  Definition comp_pureMap (m n:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (fun A => m (n A)) (comp_pure_class_of m n).

  Lemma eta_comp m n :
    @eta (comp_pureMap m n) = fun _ => @eta m _ \o @eta n _.
  Proof. done. Qed.

  (* option *)
  Definition option_pure_class_of : Pure.class_of option :=
    Pure.Class (@Some).
  Canonical option_pureMap : pureMap :=
    Eval hnf in @Pure.Pack option option_pure_class_of.

  Lemma eta_option : @eta option_pureMap = @Some.
  Proof. done. Qed.

  (* seq *)
  Definition seq_pure_class_of : Pure.class_of seq :=
    Pure.Class (fun _ x => [:: x]).
  Canonical seq_pureMap : pureMap :=
    Eval hnf in @Pure.Pack seq seq_pure_class_of.

  Lemma era_seq : @eta seq_pureMap = (fun _ x => [:: x]).
  Proof. done. Qed.

  (* sumt *)
  Definition sumt_pure_class_of R (m:pureMap) : Pure.class_of (sumt R m) :=
    Pure.Class (fun _ x => eta m (inr x)).
  Canonical sumt_pureMap R (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (sumt R m) (sumt_pure_class_of R m).

  (* mult *)
  Definition mult_pure_class_of R (idx:R) (op:Monoid.law idx) (m:pureMap)
    : Pure.class_of (mult op m) :=
    Pure.Class (fun _ x => eta _ (idx,x)).
  Canonical mult_pureMap a (idx:a) (op:Monoid.law idx) (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (mult op m) (mult_pure_class_of op m).

  (* appt *)
  Definition appt_pure_class_of R (m:pureMap) : Pure.class_of (appt R m) :=
    Pure.Class (fun _ x _ => eta _ x).
  Canonical appt_pureMap R (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (appt R m) (appt_pure_class_of R m).

  (* statet *)
  Definition statet_pure_class_of R (m:pureMap) : Pure.class_of (statet R m) :=
    Pure.Class (fun _ x r => eta _ (r,x)).
  Canonical statet_pureMap R (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (statet R m) (statet_pure_class_of R m).
End Pure_canonicals.

(* ********************* *)

Module Functor.
  Definition Functor (m:Type -> Type) := forall A B, (A -> B) -> m A -> m B.

  Record class_of (m:Type -> Type) :=
    Class {
        functor : Functor m;
        _: forall A B (f g:A -> B), f =1 g -> functor f =1 functor g;
        _: forall A x, functor (@id A) x = x;
        _: forall A B C (f:B -> C) (g:A -> B) x,
            functor (f \o g) x = functor f (functor g x)
      }.

  Section ClassDef.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation functorMap := map.
    Notation Functor := Functor.
    Definition functor T := (functor (class T)).
  End Exports.
End Functor.
Import Functor.Exports.

Section Functor_lemma.
  Variable (m : functorMap).

  Lemma eq_functor : forall A B (f g:A -> B),
      f =1 g -> @functor m _ _ f =1 functor g.
  Proof. by case : m => func []. Qed.

  Lemma functor_id : forall A (x:m A), functor (@id A) x = x.
  Proof. by case : m => func []. Qed.

  Lemma functorD : forall A B C (f:B -> C) (g:A -> B) (x:m A),
      functor (f \o g) x = functor f (functor g x).
  Proof. by case : m => func []. Qed.

  Lemma eq_functor_id A (f:A -> A) :
    f =1 id -> @functor m _ _ f =1 id.
  Proof. move /eq_functor => e x. by rewrite e functor_id. Qed.
End Functor_lemma.

Definition eq_functorMap (m:Type -> Type) (c d:Functor.class_of m) :=
  forall A B,
    @functor (Functor.Pack c) A B =2 @functor (Functor.Pack d) _ _.

Section Functor_canonicals.
  (* id *)
  Definition id_functor_class_of : Functor.class_of id.
  Proof. exact : (@Functor.Class _ (fun _ _ => id)). Defined.
  Definition id_functorMap : functorMap :=
    Eval hnf in @Functor.Pack id id_functor_class_of.

  (* comp *)
  Definition comp_functor_class_of (m n:functorMap) :
    Functor.class_of (fun A => m (n A)).
  Proof.
    apply : (@Functor.Class _ (fun _ _ => @functor m _ _ \o @functor n _ _))
    =>[A B f g fg|A x|A B C f g x]/=.
    - by do 2! apply : eq_functor.
    - apply : eq_functor_id. exact : functor_id.
    - rewrite -functorD. apply : eq_functor => y. exact : functorD.
  Defined.
  Definition comp_functorMap (m n:functorMap) : functorMap :=
    Eval hnf in @Functor.Pack (fun A => m (n A)) (comp_functor_class_of m n).

  Lemma functor_comp m n :
    @functor (comp_functorMap m n) =
    fun _ _ => @functor m _ _ \o @functor n _ _.
  Proof. done. Qed.

  (* option *)
  Definition option_functor_class_of : Functor.class_of option.
  Proof.
    apply : (@Functor.Class
               _ (fun _ _ f o => if o is Some x then Some (f x) else None))
    =>[A B f g fg [x|]|A [x|]|A B C f g [x|]]//.
      by rewrite fg.
  Defined.
  Canonical option_functorMap : functorMap :=
    Eval hnf in @Functor.Pack option option_functor_class_of.

  Lemma functor_option :
    @functor option_functorMap =
    fun _ _ f o => if o is Some x then Some (f x) else None.
  Proof. done. Qed.

  Lemma seq_functor_class_of : Functor.class_of seq.
  Proof.
    apply : (@Functor.Class _ (@map)).
    - exact : eq_map.
    - exact : map_id.
    - exact : map_comp.
  Defined.
  Canonical seq_functorMap : functorMap :=
    Eval hnf in @Functor.Pack seq seq_functor_class_of.

  Lemma functor_seq : @functor seq_functorMap = @map.
  Proof. done. Qed.

  (* sumt *)
  Definition sumt_functor_class_of R (m:functorMap):
    Functor.class_of (sumt R m).
  Proof.
    apply : (@Functor.Class
               _ (fun _ _ f => functor (fun x => match x with
                                                 | inl a => inl a
                                                 | inr x => inr (f x)
                                                 end)))
    =>[A B f g fg|A x|A B C f g x]/=.
    - apply : eq_functor =>[[|x]]//. by rewrite fg.
    - by apply : eq_functor_id =>[[]].
    - rewrite -functorD. by apply : eq_functor =>[[]].
  Defined.
  Canonical sumt_functorMap R (m:functorMap) : functorMap :=
    Eval hnf in @Functor.Pack (sumt R m) (sumt_functor_class_of R m).

  Lemma functor_sumt R m:
    @functor (sumt_functorMap R m) =
    fun _ _ f => functor (fun x => match x with
                                   | inl a => inl a
                                   | inr x => inr (f x)
                                   end).
  Proof. done. Qed.

  (* mult *)
  Definition mult_functor_class_of R (idx:R) (op:Monoid.law idx) (m:functorMap):
    Functor.class_of (mult op m).
  Proof.
    apply : (@Functor.Class
               _ (fun _ _ f => functor (fun rx => match rx with
                                                    (r,x) => (r,f x)
                                                  end)))
    =>[A B f g fg|A x|A B C f g x].
    - apply : eq_functor =>[[r x]]. by rewrite fg.
    - by apply : eq_functor_id =>[[]].
    - rewrite -functorD. by apply : eq_functor =>[[]].
  Defined.
  Canonical mult_functorMap R (idx:R) (op:Monoid.law idx) (m:functorMap) :
    functorMap :=
    Eval hnf in @Functor.Pack (mult op m) (mult_functor_class_of op m).

  Lemma functor_mult R (idx:R) (op:Monoid.law idx) m:
    @functor (mult_functorMap op m) =
    fun _ _ f => functor (fun rx => match rx with (r,x) => (r,f x) end).
  Proof. done. Qed.

  (* appt *)
  (* needed functional extensionality *)
(*
  Definition appt_functor_class_of R (m:functorMap):
    Functor.class_of (appt R m).
  Proof.
    apply : (@Functor.Class _ (fun _ _ f xf x => functor f (xf x)))
    =>[A B f g fg xf||].
*)
End Functor_canonicals.

(* ********************* *)

Module PFunctor.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          pBase : Pure.class_of m;
          fBase : Functor.class_of m
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (pBase class).
    Definition functorMap := Functor.Pack (fBase class).
  End ClassDef.

  Module Exports.
    Coercion pBase : class_of >-> Pure.class_of.
    Coercion fBase : class_of >-> Functor.class_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Notation pfunctorMap := map.
  End Exports.
End PFunctor.
Import PFunctor.Exports.

Section PFunctor_lemma.
  Variable (m : pfunctorMap).
End PFunctor_lemma.

Definition eq_pfunctorMap (m:Type -> Type) (c d:PFunctor.class_of m) :=
  eq_pureMap c d /\ eq_functorMap c d.

Section PFunctor_canonicals.
  (* id *)
  Definition id_pfunctor_class_of : PFunctor.class_of id :=
    PFunctor.Class id_pure_class_of id_functor_class_of.
  Definition id_pfunctorMap : pfunctorMap :=
    Eval hnf in @PFunctor.Pack id id_pfunctor_class_of.

  (* comp *)
  Definition comp_pfunctor_class_of (m n:pfunctorMap) :
    PFunctor.class_of (fun A => m (n A)) :=
    PFunctor.Class (comp_pure_class_of m n) (comp_functor_class_of m n).
  Definition comp_pfunctorMap (m n:pfunctorMap) : pfunctorMap :=
    Eval hnf in @PFunctor.Pack (fun A => m (n A)) (comp_pfunctor_class_of m n).

  (* option *)
  Definition option_pfunctor_class_of : PFunctor.class_of option :=
    PFunctor.Class option_pure_class_of option_functor_class_of.
  Canonical option_pfunctorMap : pfunctorMap :=
    Eval hnf in @PFunctor.Pack option option_pfunctor_class_of.

  (* seq *)
  Definition seq_pfunctor_class_of : PFunctor.class_of seq :=
    PFunctor.Class seq_pure_class_of seq_functor_class_of.
  Canonical seq_pfunctorMap : pfunctorMap :=
    Eval hnf in @PFunctor.Pack seq seq_pfunctor_class_of.

  (* sumt *)
  Definition sumt_pfunctor_class_of R (m:pfunctorMap) :
    PFunctor.class_of (sumt R m) :=
    PFunctor.Class (sumt_pure_class_of R m) (sumt_functor_class_of R m).
  Canonical sumt_pfunctorMap R (m:pfunctorMap): pfunctorMap :=
    Eval hnf in @PFunctor.Pack (sumt R m) (sumt_pfunctor_class_of R m).

  (* mult *)
  Definition mult_pfunctor_class_of R (idx:R) (op:Monoid.law idx)
             (m:pfunctorMap) : PFunctor.class_of (mult op m) :=
    PFunctor.Class (mult_pure_class_of op m) (mult_functor_class_of op m).
  Definition mult_pfunctorMap R (idx:R) (op:Monoid.law idx) (m:pfunctorMap)
    : pfunctorMap :=
    Eval hnf in @PFunctor.Pack (mult op m) (mult_pfunctor_class_of op m).
End PFunctor_canonicals.

(* ********************* *)

Module Applicative.
  Definition Applicative (m:Type -> Type)
    := forall A B, m (A -> B) -> m A -> m B.

  Record mixin_of (m:pfunctorMap) :=
    Mixin {
        applicative : Applicative m;
        _: forall A B (f:A -> B),
            applicative (eta _ f) =1 functor f;
        _: forall A B C (f g:A -> B -> C),
            f =2 g ->
            forall x, applicative (functor f x) =1 applicative (functor g x);
        _: forall A B C D (f g:A -> B -> C -> D),
            (forall x, f x =2 g x) ->
            forall x y, applicative (applicative (functor f x) y)
                        =1 applicative (applicative (functor g x) y);
        _: forall A B C (f:m (B -> C)) (g:m (A -> B)) x,
            applicative (applicative (applicative (eta _ comp) f) g) x =
            applicative f (applicative g x);
        _: forall A B (f:A -> B) x,
            applicative (eta _ f) (eta m x) = eta _ (f x);
        _: forall A B (f:m (A -> B)) x,
            applicative f (eta _ x) = functor (@^~ x) f
      }.

  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : PFunctor.class_of m;
          mixin : mixin_of (PFunctor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Notation applicativeMap := map.
    Notation Applicative := Applicative.
    Definition applicative T := (applicative (class T)).
  End Exports.
End Applicative.
Import Applicative.Exports.

Section Applicative_lemma.
  Variable (m:applicativeMap).
  Let eta := eta m.

  Lemma applicative_etal A B (f:A -> B) :
    applicative (eta f) =1 functor f.
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Lemma applicativeA A B C :
    forall (f:m (B -> C)) (g:m (A -> B)) x,
      applicative (applicative (applicative (eta comp) f) g) x =
      applicative f (applicative g x).
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Lemma applicative_eta_eta A B (f:A -> B) x :
    applicative (eta f) (eta x) = eta (f x).
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Lemma applicative_etar A B :
    forall (f:m (A -> B)) x,
      applicative f (eta x) = functor (@^~ x) f.
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Definition functor2 A B C (f:A -> B -> C) (x:m A) : m B -> m C :=
    applicative (functor f x).

  Lemma eq_functor2 A B C (f g:A -> B -> C):
    f =2 g -> functor2 f =2 functor2 g.
  Proof.
    rewrite /functor2. case : m => func [b /=[a e0 H e1 e2 e3 e4]].
    exact : H.
  Qed.

  Lemma functor2_eta A B C (f:A -> B -> C) x:
    functor2 f (eta x) =1 functor (f x).
  Proof.
    rewrite /functor2 => y.
      by rewrite -applicative_etal applicative_eta_eta applicative_etal.
  Qed.

  Definition functor3 A B C D (f:A -> B -> C -> D)
             (x:m A) (y:m B) : m C -> m D :=
    applicative (functor2 f x y).

  Lemma eq_functor3 A B C D (f g:A -> B -> C -> D):
    (forall x, f x =2 g x) -> forall x, functor3 f x =2 functor3 g x.
  Proof.
    rewrite /functor3 /functor2. case : m => func [b /=[a e0 e1 H e2 e3 e4]].
    exact : H.
  Qed.

  Lemma functor3_eta A B C D (f:A -> B -> C -> D) x:
    functor3 f (eta x) =2 functor2 (f x).
  Proof.
    rewrite /functor3 => y z. by rewrite functor2_eta.
  Qed.
End Applicative_lemma.

Definition eq_applicativeMap (m:Type -> Type) (c d:Applicative.class_of m) :=
  eq_pfunctorMap c d /\
  forall A B, @applicative (Applicative.Pack c) A B
                =2 @applicative (Applicative.Pack d) _ _.

Section Applicative_canonicals.
  (* id *)
  Definition id_applicative_mixin_of : Applicative.mixin_of id_pfunctorMap.
  Proof.
    exact : (@Applicative.Mixin
               _ ((fun _ _ => id) : Applicative id_pfunctorMap)).
  Defined.
  Definition id_applicative_class_of : Applicative.class_of id :=
    Applicative.Class id_applicative_mixin_of.
  Definition id_applicativeMap : applicativeMap :=
    Eval hnf in @Applicative.Pack id id_applicative_class_of.

  (* comp *)
  Definition comp_applicative_mixin_of (m n:applicativeMap) :
    Applicative.mixin_of (comp_pfunctorMap m n).
  Proof.
    apply : (@Applicative.Mixin
               _ ((fun A B (f:m (n (A -> B)))
                   => functor2 (@applicative _ _ _) f)
                  : Applicative (comp_pfunctorMap _ _)))
              =>/=[A B f x|A B C f g fg x y|A B C D f g fg x y z|
                   A B C f g x|A B f x|A B f x].
    - rewrite functor_comp functor2_eta. apply : eq_functor => y.
      exact : applicative_etal.
    - rewrite functor_comp /= /functor2 -!functorD. apply : eq_functor2.
      exact : eq_functor2.
    - rewrite functor_comp /= /functor2 -!functorD -!applicative_etal.
      rewrite -!applicativeA !applicative_eta_eta !applicative_etal.
      apply : eq_functor3. exact : eq_functor3.
    - rewrite eta_comp /= functor2_eta /functor2 -!applicative_etal.
      do ! (rewrite -applicativeA !applicative_eta_eta).
         rewrite -2!applicativeA applicative_etar -applicative_etal.
         do ! (rewrite -applicativeA !applicative_eta_eta).
            rewrite !applicative_etal.
      apply : eq_functor3. exact : applicativeA.
    - by rewrite eta_comp functor2_eta -applicative_etal !applicative_eta_eta.
    - rewrite functor_comp eta_comp /= /functor2 applicative_etar -functorD.
      apply : eq_functor => y. exact : applicative_etar.
  Defined.
  Definition comp_applicative_class_of (m n:applicativeMap) :
    Applicative.class_of (fun A => m (n A)) :=
    Applicative.Class (comp_applicative_mixin_of m n).
  Definition comp_applicativeMap (m n:applicativeMap) : applicativeMap :=
    Eval hnf in @Applicative.Pack
                  (fun A => m (n A)) (comp_applicative_class_of m n).

  Lemma applicative_comp (m n:applicativeMap):
    @applicative (comp_applicativeMap m n) =
    fun A B (f:m (n (A -> B))) => functor2 (@applicative _ _ _) f.
  Proof. done. Qed.

  Lemma applicative_functor2 (m n:applicativeMap) A B C f:
    @functor2 (comp_applicativeMap m n) A B C f =2 functor2 (functor2 f).
  Proof.
    rewrite /functor2 applicative_comp /functor2 functor_comp => x y /=.
    rewrite -functorD. apply : eq_functor2 =>{x y} x y.
    exact : eq_functor2.
  Qed.

  Lemma applicative_functor3 (m n:applicativeMap) A B C D f x:
    @functor3 (comp_applicativeMap m n) A B C D f x =2 functor3 (functor3 f) x.
  Proof.
    rewrite /functor3 applicative_comp /functor2 functor_comp => y z /=.
    rewrite -!applicative_etal -!applicativeA applicative_eta_eta.
    rewrite -!applicative_etal -applicativeA !applicative_eta_eta.
    rewrite -applicativeA !applicative_eta_eta applicative_etal.
    apply : eq_functor3. exact : eq_functor3.
  Qed.

  (* option *)
  Definition option_applicative_mixin_of:
    Applicative.mixin_of option_pfunctorMap.
  Proof.
    by apply : (@Applicative.Mixin
                  _ (fun _ _ oF ox
                     => if oF is Some f
                        then if ox is Some x then Some (f x) else None
                        else None))
                 =>/=[|A B C f g fg [x|][y|]|A B C D f g fg [x|][y|][z|]|
                      A B C [f|][g|][x|]||]//; rewrite functor_option fg.
  Defined.
  Definition option_applicative_class_of : @Applicative.class_of option :=
    Applicative.Class option_applicative_mixin_of.
  Canonical option_applicativeMap : applicativeMap :=
    Eval hnf in @Applicative.Pack option option_applicative_class_of.

  Lemma applicative_option :
    @applicative option_applicativeMap =
    fun _ _ oF ox => if oF is Some f
                     then if ox is Some x then Some (f x) else None
                     else None.
  Proof. done. Qed.
End Applicative_canonicals.

(* ********************* *)

Module Monad.
  Definition Mu (m:Type -> Type) := forall A, m (m A) -> m A.

  Record mixin_of (m:pfunctorMap) :=
    Mixin {
        mu : Mu m;
        _: forall A (x:m A), mu (eta _ x) = x;
        _: forall A x,
            mu (functor (@eta _ A) x) = x;
        _: forall A x,
            mu (functor (@mu A) x) = mu (mu x)
      }.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : PFunctor.class_of m;
          mixin : mixin_of (PFunctor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Notation monadMap := map.
    Notation Mu := Mu.
    Definition mu T := (mu (class T)).
  End Exports.
End Monad.
Import Monad.Exports.

Section Monad_lemma.
  Variable (m : monadMap).
  Let eta := eta m.

  Lemma mu_eta : forall A (x:m A), mu (eta x) = x.
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Lemma mu_functor_eta : forall A x, mu (functor (@eta A) x) = x.
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Lemma mu_functor_mu : forall A x, mu (functor (@mu m A) x) = mu (mu x).
  Proof. rewrite /eta. by case : m => func [b []]. Qed.
End Monad_lemma.

Definition eq_monadMap (m:Type -> Type) (c d:Monad.class_of m) :=
  [/\ eq_pureMap c d, eq_functorMap c d &
   forall A, @mu (Monad.Pack c) A =1 @mu (Monad.Pack d) _].

Section Monad_canonicals.
  (* id *)
  Definition id_monad_mixin_of : Monad.mixin_of id_pfunctorMap.
  Proof.
    exact : (@Monad.Mixin _ ((fun _ => id) : Mu id_pfunctorMap)).
  Defined.
  Definition id_monad_class_of : Monad.class_of id :=
    Monad.Class id_monad_mixin_of.
  Definition id_monadMap : monadMap :=
    Eval hnf in @Monad.Pack id id_monad_class_of.

  (* option *)
  Definition option_monad_mixin_of : Monad.mixin_of option_pfunctorMap.
  Proof.
      by apply : (@Monad.Mixin _  (fun _ o => if o is Some x then x else None))
      =>[A [x|]|A [x|]|A [x|]].
  Defined.
  Definition option_monad_class_of : Monad.class_of option :=
    Monad.Class option_monad_mixin_of.
  Canonical option_monadMap : monadMap :=
    Eval hnf in @Monad.Pack option option_monad_class_of.

  Lemma mu_option :
    @mu option_monadMap = fun _ o => if o is Some x then x else None.
  Proof. done. Qed.

  (* seq *)
  Lemma seq_monad_mixin_of : Monad.mixin_of seq_pfunctorMap.
  Proof.
    apply : (@Monad.Mixin _ (@flatten))=>/=[||A].
    - exact : cats0.
    - exact : flatten_seq1.
    - elim =>[|x s IHs]//=. by rewrite flatten_cat -IHs.
  Defined.
  Definition seq_monad_class_of : Monad.class_of seq :=
    Monad.Class seq_monad_mixin_of.
  Canonical seq_monadMap : monadMap :=
    Eval hnf in @Monad.Pack seq seq_monad_class_of.

  Lemma mu_seq : @mu seq_monadMap = @flatten.
  Proof. done. Qed.

End Monad_canonicals.

Section Monad_applicative.
  Variable (m:monadMap).
  Definition hApplicative : Applicative m :=
    fun A B f x => mu (functor (fun x => functor (@^~ x) f) x).
  Definition vApplicative : Applicative m :=
    fun A B f x => mu (functor ((@functor _ _ _)^~ x) f).
End Monad_applicative.

Eval compute in (hApplicative [:: (fun x => x.+1); (fun x =>x.+2)] [:: 10; 20]).
(* = [:: 11; 12; 21; 22] *)
Eval compute in (vApplicative [:: (fun x => x.+1); (fun x =>x.+2)] [:: 10; 20]).
(* = [:: 11; 21; 12; 22] *)

Section Monad_applicative_lemma.
  Definition eq_hvApplicative m :=
    forall A B, @hApplicative m A B =2 @vApplicative _ _ _.

  Lemma id_eq_hvApplicative : eq_hvApplicative id_monadMap.
  Proof. done. Qed.

  Lemma option_eq_hvApplicative : eq_hvApplicative option_monadMap.
  Proof. by move => A B [f|] [x|]. Qed.
End Monad_applicative_lemma.

(* ********************* *)

Module Kleisli.
  Record mixin_of (m:monadMap) :=
    Mixin {
        _: forall A B (f:(A -> B)) x,
          functor f (eta m x) = eta _ (f x);
        _: forall A B (f:A -> B) (x:m (m A)),
            functor f (mu x) = mu (functor (functor f) x)
      }.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : Monad.class_of m;
          mixin : mixin_of (Monad.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Monad.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Notation kleisliMap := map.
  End Exports.
End Kleisli.
Import Kleisli.Exports.

Section Kleisli_lemma.
  Variable (m:kleisliMap).
  Let eta := eta m.

  Lemma functor_eta : forall A B (f:A -> B) x,
      functor f (eta x) = eta (f x).
  Proof. rewrite /eta. by case m => func [b []]. Qed.

  Lemma functor_mu : forall A B (f:A -> B) (x:m (m A)),
      functor f (mu x) = mu (functor (functor f) x).
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  (* *)
  Definition Unit := Eta.
  Definition Bind (m:Type -> Type) := forall A B, m A -> (A -> m B) -> m B.

  Definition unit : Unit m := eta.
  Definition bind : Bind m := fun A B x f => mu (functor f x).

  Lemma eq_bind A B (f g:A -> m B) :
    f =1 g -> (@bind _ _)^~ f =1 (@bind _ _)^~ g.
  Proof. move => fg x. by rewrite /bind (eq_functor fg). Qed.

  Lemma bind_unitr A (x:m A) : bind x (@unit _) = x.
  Proof. exact : mu_functor_eta. Qed.

  Lemma bind_unitl A B x (f:A -> m B) : bind (unit x) f = f x.
  Proof. by rewrite /bind /unit functor_eta mu_eta. Qed.

  Lemma bindA A B C x (f:A -> m B) (g:B -> m C) :
    bind (bind x f) g = bind x (fun y => bind (f y) g).
  Proof. by rewrite /bind functor_mu -mu_functor_mu -!functorD. Qed.

  (* hApplicative *)
  Definition hApplicative_mixin_of : Applicative.mixin_of m.
  Proof.
    apply : (@Applicative.Mixin _ (@hApplicative m))
    =>[A B f x|A B C f g fg x y|A B C D f g fg x y z|
       A B C f g x|A B f x|A B f x];
        rewrite /hApplicative /=.
    - by rewrite (eq_functor (g:= @eta _ \o f))
      =>[|y]/=; rewrite ?functor_eta // functorD mu_functor_eta.
    - congr(mu). apply : eq_functor =>{y} y. rewrite -!functorD.
        by apply : eq_functor =>{x} x /=.
    - congr(mu). apply : eq_functor =>{z} z. rewrite !functor_mu. congr(mu).
      rewrite -!functorD. apply : eq_functor =>{y} y /=.
      rewrite -!functorD. apply : eq_functor =>{x} x /=.
      exact : fg.
    - rewrite functor_mu -mu_functor_mu. congr(mu). rewrite -!functorD.
      apply : eq_functor =>{x} x /=. rewrite functor_mu. congr(mu).
      rewrite -!functorD. apply : eq_functor =>{g} g /=.
      rewrite !functor_mu -!functorD.
        by rewrite (eq_functor (g:= @eta _ \o @^~ (g x)))
        =>[|z]/=; rewrite ?functor_eta // functorD mu_functor_eta.
    - by rewrite !functor_eta mu_eta.
    - by rewrite functor_eta mu_eta.
  Defined.
  Definition hApplicative_class_of : Applicative.class_of m :=
    Applicative.Class hApplicative_mixin_of.
  Definition hApplicativeMap : applicativeMap :=
    @Applicative.Pack m hApplicative_class_of.
  Lemma applicative_hApplicative :
    @applicative hApplicativeMap = @hApplicative m.
  Proof. done. Qed.

  (* vApplicative *)
  Definition vApplicative_mixin_of : Applicative.mixin_of m.
  Proof.
    apply : (@Applicative.Mixin _ (@vApplicative m))
    =>[A B f x|A B C f g fg x y|A B C D f g fg x y z|
       A B C f g x|A B f x|A B f x];
        rewrite /vApplicative /=.
    - by rewrite functor_eta mu_eta.
    - congr(mu). rewrite -!functorD. apply : eq_functor =>{x} x /=.
      exact : eq_functor.
    - congr(mu). rewrite !functor_mu -!functorD. congr(mu).
      apply : eq_functor =>{x} x /=. rewrite -!functorD.
      apply : eq_functor =>{y} y /=. apply : eq_functor =>{z} z /=.
      exact : fg.
    - rewrite functor_eta mu_eta functor_mu -mu_functor_mu -!functorD.
      congr(mu). apply : eq_functor =>{f} f /=. rewrite functor_mu -!functorD.
      congr(mu). apply : eq_functor =>{g} g /=. exact : functorD.
    - by rewrite !functor_eta mu_eta.
    - by rewrite (eq_functor (g:= @eta _ \o @^~ x))
      =>[|y]/=; rewrite ?functor_eta // functorD mu_functor_eta.
  Defined.
  Definition vApplicative_class_of : Applicative.class_of m :=
    Applicative.Class vApplicative_mixin_of.
  Definition vApplicativeMap : applicativeMap :=
    @Applicative.Pack m vApplicative_class_of.
  Lemma applicative_vApplicative :
    @applicative vApplicativeMap = @vApplicative m.
  Proof. done. Qed.
End Kleisli_lemma.

Definition eq_kleisliMap (m:Type -> Type) (c d:Kleisli.class_of m) :=
  eq_monadMap c d.

Section Kleisli_canonicals.
  (* id *)
  Definition id_kleisli_mixin_of : Kleisli.mixin_of id_monadMap.
  Proof. exact : Kleisli.Mixin. Defined. 
  Definition id_kleisli_class_of : Kleisli.class_of id :=
    Kleisli.Class id_kleisli_mixin_of.
  Definition id_kleisliMap : kleisliMap :=
    Eval hnf in @Kleisli.Pack id id_kleisli_class_of.

  (* option *)
  Definition option_kleisli_mixin_of : Kleisli.mixin_of option_monadMap.
  Proof.
      by apply : Kleisli.Mixin =>[|A B f [[x|]|]].
  Defined.
  Definition option_kleisli_class_of : Kleisli.class_of option :=
    Kleisli.Class option_kleisli_mixin_of.
  Canonical option_kleisliMap : kleisliMap :=
    Eval hnf in @Kleisli.Pack option option_kleisli_class_of.

  (* seq *)
  Definition seq_kleisli_mixin_of : Kleisli.mixin_of seq_monadMap.
  Proof.
    apply : Kleisli.Mixin =>// A B. exact : map_flatten.
  Defined.
  Definition seq_kleisli_class_of : Kleisli.class_of seq :=
    Kleisli.Class seq_kleisli_mixin_of.
  Canonical seq_kleisliMap : kleisliMap :=
    Eval hnf in @Kleisli.Pack seq seq_kleisli_class_of.

  (* sumt *)
  Definition sumt_monad_mixin_of R (m:kleisliMap) :
    Monad.mixin_of (sumt_pfunctorMap R m).
  Proof.
    apply : (@Monad.Mixin
               _ ((fun _ x => mu (functor
                                  (fun x => match x with
                                            | inl r => eta _ (inl r)
                                            | inr x => x
                                            end) x)) : Mu (sumt R m)))
    =>[A x|A x|A x].
    - by rewrite functor_eta mu_eta.
    - rewrite /eta /= -functorD (eq_functor (g:=@eta _ _)) =>[|[r|y]]//.
        by rewrite mu_functor_eta.
    - rewrite functor_mu -mu_functor_mu -!functorD. congr(mu).
      apply : eq_functor =>{x} [[a|x]]//=.
        by rewrite functor_eta mu_eta.
  Defined.
  Definition sumt_monad_class_of R (m:kleisliMap) : Monad.class_of (sumt R m) :=
    Monad.Class (sumt_monad_mixin_of R m).
  Canonical sumt_monadMap R (m:kleisliMap) : monadMap :=
    Eval hnf in @Monad.Pack (sumt R m) (sumt_monad_class_of R m).

  Lemma mu_sumt R m :
    @mu (sumt_monadMap R m) =
    fun _ x => mu (functor (fun x => match x with
                                     | inl r => eta _ (inl r)
                                     | inr x => x
                                     end) x).
  Proof. done. Qed.

  Definition sumt_kleisli_mixin_of R (m:kleisliMap) :
    Kleisli.mixin_of (sumt_monadMap R m).
  Proof.
    apply : Kleisli.Mixin =>[A B f x|A B f x]/=.
    - by rewrite [functor _ _]functor_eta.
    - rewrite [functor _ _]functor_mu functor_sumt /sumt. congr(mu).
      rewrite -!functorD. apply : eq_functor =>{x}[[a|x]]//=.
        by rewrite functor_eta.
  Defined.
  Definition sumt_kleisli_class_of R (m:kleisliMap) :
    Kleisli.class_of (sumt R m) :=
    Kleisli.Class (sumt_kleisli_mixin_of R m).
  Definition sumt_kleisliMap R (m:kleisliMap) : kleisliMap :=
    Eval hnf in @Kleisli.Pack (sumt R m) (sumt_kleisli_class_of R m).

  (* mult *)
  Definition mult_monad_mixin_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    Monad.mixin_of (mult_pfunctorMap op m).
  Proof.
    apply : (@Monad.Mixin
               _ ((fun _ x =>
                    mu (functor (fun amx =>
                                   match amx with
                                   | (a,mx) =>
                                     functor (fun bx =>
                                                match bx with
                                                | (b,x) => (op a b,x)
                                                end) mx
                                   end) x)) : Mu (mult_pfunctorMap op m)))
              =>/=[A x|A x|A x].
    - rewrite [functor _ _]functor_eta mu_eta.
      rewrite (eq_functor (g:=id)) ?functor_id // =>[[r y]].
        by rewrite Monoid.mul1m.
    - rewrite -functorD (eq_functor (g:=@eta _ _)) ?mu_functor_eta
      =>[|[r y]]//=. by rewrite functor_eta Monoid.mulm1.
    - rewrite functor_mu -mu_functor_mu -!functorD. congr(mu).
      apply : eq_functor =>[[r y]]/=. rewrite functor_mu -!functorD. congr(mu).
      apply : eq_functor =>[[s z]]/=. rewrite -functorD.
      apply : eq_functor =>[[t w]]/=. by rewrite Monoid.mulmA.
  Defined.
  Definition mult_monad_class_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    Monad.class_of (mult op m) := Monad.Class (mult_monad_mixin_of op m).
  Canonical mult_monadMap R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    monadMap := Eval hnf in @Monad.Pack (mult op m) (mult_monad_class_of op m).

  Lemma mu_mult R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    @mu (mult_monadMap op m) =
    (fun _ x =>
       mu (functor (fun amx =>
                      match amx with
                      | (a,mx) =>
                        functor (fun bx =>
                                   match bx with
                                   | (b,x) => (op a b,x)
                                   end) mx
                      end) x)).
  Proof. done. Qed.

  Definition mult_kleisli_mixin_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap):
    Kleisli.mixin_of (mult_monadMap op m).
  Proof.
    apply : Kleisli.Mixin =>/=[A B f x|A B f x].
    - by rewrite [functor _ _]functor_eta.
    - rewrite mu_mult functor_mult functor_mu -!functorD. congr(mu).
      apply : eq_functor =>[[r y]]/=. rewrite -!functorD.
        by apply : eq_functor =>[[]].
  Defined.
  Definition mult_kleisli_class_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap):
    Kleisli.class_of (mult op m) := Kleisli.Class (mult_kleisli_mixin_of op m).
  Canonical mult_kleisliMap R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    kleisliMap :=
    Eval hnf in @Kleisli.Pack (mult op m) (mult_kleisli_class_of op m).
End Kleisli_canonicals.

(* ********************* *)

Module AKleisli.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Kleisli.class_of t;
          mixin : Applicative.mixin_of (PFunctor.Pack base)
        }.
    Definition applicative_class_of t (class:class_of t)
      : Applicative.class_of t :=
      Applicative.Class (mixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
    Definition kleisliMap := Kleisli.Pack (base class).
    Definition applicativeMap := Applicative.Pack (applicative_class_of class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Kleisli.class_of.
    Coercion mixin : class_of >-> Applicative.mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Coercion kleisliMap : map >-> Kleisli.map.
    Canonical kleisliMap.
    Coercion applicative_class_of : class_of >-> Applicative.class_of.
    Coercion applicativeMap : map >-> Applicative.map.
    Canonical applicativeMap.
    Notation akleisliMap := map.
  End Exports.
End AKleisli.
Import AKleisli.Exports.

Section AKleisli_lemma.
  Variable (m:kleisliMap).

  Definition hkleisli_class_of : AKleisli.class_of m
    := AKleisli.Class (hApplicative_mixin_of m).
  Definition hkleisli : akleisliMap := @AKleisli.Pack m hkleisli_class_of.

  Definition vkleisli_class_of : AKleisli.class_of m
    := AKleisli.Class (vApplicative_mixin_of m).
  Definition vkleisli : akleisliMap := @AKleisli.Pack m vkleisli_class_of.
End AKleisli_lemma.

(* ********************* *)

Module Sequence.
  Definition Sequence (t:Type -> Type) :=
    forall (m:applicativeMap) A, t (m A) -> m (t A).

  Record mixin_of (t:functorMap) :=
    Mixin {
        sequence:Sequence t;
        _:forall (m:applicativeMap) A B (f:A -> B) (x:t (m A)),
            sequence (functor (functor f) x) =
            functor (functor f) (sequence x)
      }.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Functor.class_of t;
          mixin : mixin_of (Functor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition functorMap := Functor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Functor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Notation sequenceMap := map.
    Notation Sequence := Sequence.
    Definition sequence T := sequence (class T).
  End Exports.
End Sequence.
Import Sequence.Exports.

Section Sequence_lemma.
  Variable (t:sequenceMap).

  Lemma sequence_functor_functor :
    forall (m:applicativeMap) A B (f:A -> B) (x:t (m A)),
      sequence (functor (functor f) x) = functor (functor f) (sequence x).
  Proof. by case : t => func [b []]. Qed.
End Sequence_lemma.

Definition eq_sequenceMap (t:Type -> Type) (c d:Sequence.class_of t) :=
  eq_functorMap c d /\
  forall m A,
    @sequence (Sequence.Pack c) m A =1 @sequence (Sequence.Pack d) m _.

Section Sequence_canonicals.
  (* id *)
  Definition id_sequence_mixin_of : Sequence.mixin_of id_functorMap.
  Proof.
    exact : (@Sequence.Mixin _ ((fun _ _ => id) : Sequence id_functorMap)).
  Defined.
  Definition id_sequence_class_of : Sequence.class_of id :=
    Sequence.Class id_sequence_mixin_of.
  Definition id_sequenceMap : sequenceMap :=
    Eval hnf in @Sequence.Pack id id_sequence_class_of.

  (* comp *)
  Definition comp_sequnece_mixin_of (t s:sequenceMap) :
    Sequence.mixin_of (comp_functorMap t s).
  Proof.
    apply : (@Sequence.Mixin
               _ ((fun _ _ => @sequence _ _ _ \o functor (@sequence _ _ _))
                  : Sequence (comp_functorMap t s)))=>/= m A B f x.
    rewrite -sequence_functor_functor -!functorD. congr (sequence).
    apply : eq_functor => y /=. by rewrite sequence_functor_functor.
  Defined.
  Definition comp_sequence_class_of (t s:sequenceMap) :
    Sequence.class_of (fun A => t (s A)) :=
    Sequence.Class (comp_sequnece_mixin_of t s).
  Definition comp_sequenceMap (t s:sequenceMap) : sequenceMap :=
    Eval hnf in @Sequence.Pack (fun A => t (s A)) (comp_sequence_class_of t s).

  Lemma sequence_comp t s :
    @sequence (comp_sequenceMap t s) =
    fun _ _ => @sequence _ _ _ \o functor (@sequence _ _ _).
  Proof. done. Qed.

  (* option *)
  Definition option_sequence_mixin_of : Sequence.mixin_of option_functorMap.
  Proof.
    apply : (@Sequence.Mixin
               _ (fun _ _ o =>
                    if o is Some x then functor (@Some _) x else eta _ None))
    => m A B f [x|]/=.
    - by rewrite -!functorD.
    - by rewrite -applicative_etal applicative_eta_eta.
  Defined.
  Definition option_sequence_class_of : Sequence.class_of option :=
    Sequence.Class option_sequence_mixin_of.
  Canonical option_sequenceMap : sequenceMap :=
    Eval hnf in @Sequence.Pack option option_sequence_class_of.

  Lemma sequence_option :
    @sequence option_sequenceMap =
    fun _ _ o => if o is Some x then functor (@Some _) x else eta _ None.
  Proof. done. Qed.

  (* seq *)
  Definition seq_sequence_mixin_of : Sequence.mixin_of seq_functorMap.
  Proof.
    apply : (@Sequence.Mixin
               _ (fun _ _ => foldr (functor2 cons) (eta _ [::])))
    => m A B f /=.
    elim =>[|x s /=->].
    - by rewrite -applicative_etal applicative_eta_eta.
    - rewrite /functor2 -!applicative_etal -applicativeA applicative_etar.
      do ! rewrite -applicativeA !applicative_eta_eta.
         rewrite !applicative_etal -functorD. exact : eq_functor2.
  Defined.
  Definition seq_sequence_class_of : Sequence.class_of seq :=
    Sequence.Class seq_sequence_mixin_of.
  Canonical seq_sequenceMap : sequenceMap :=
    Eval hnf in @Sequence.Pack seq seq_sequence_class_of.

  Lemma sequence_seq :
    @sequence seq_sequenceMap = fun _ _ => foldr (functor2 cons) (eta _ [::]).
  Proof. done. Qed.

  (* sumt *)
  Definition sumt_sequence_mixin_of R (t:sequenceMap):
    Sequence.mixin_of (sumt_functorMap R t).
  Proof.
    apply : (@Sequence.Mixin
               _ ((fun m _ f =>
                     sequence (functor (fun rma =>
                                          match rma with
                                          | inl r => eta _ (inl r)
                                          | inr ma => @functor m _ _ inr ma
                                          end) f))
                  : Sequence (sumt_functorMap R t)))=>[m A B f x].
    rewrite -sequence_functor_functor -!functorD. congr(sequence).
    apply : eq_functor =>{x} [[r|x]]/=.
    - by rewrite -applicative_etal applicative_eta_eta.
    - rewrite -!functorD. exact : eq_functor.
  Defined.
  Definition sumt_sequence_class_of R (t:sequenceMap) :
    Sequence.class_of (sumt R t) :=
    Sequence.Class (sumt_sequence_mixin_of R t).
  Canonical sumt_sequenceMap R (t:sequenceMap) : sequenceMap :=
    Eval hnf in @Sequence.Pack (sumt R t) (sumt_sequence_class_of R t).    

  Lemma sequence_sumt R (t:sequenceMap) :
    @sequence (sumt_sequenceMap R t) =
    fun m _ f => sequence (functor (fun rma => match rma with
                                               | inl r => eta _ (inl r)
                                               | inr ma => @functor m _ _ inr ma
                                               end) f).
  Proof. done. Qed.

  (* mult *)
  Definition mult_sequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:sequenceMap): Sequence.mixin_of (mult_functorMap op t).
  Proof.
    apply : (@Sequence.Mixin
               _ ((fun _ _ f =>
                    sequence (functor (fun rma =>
                                         match rma with
                                         | (r,ma) => functor (pair r) ma
                                         end) f)) : Sequence (mult op t)))
    => m A B f x.
    rewrite -sequence_functor_functor -!functorD. congr(sequence).
    apply : eq_functor =>[[r ma]]/=. rewrite -!functorD.
    exact : eq_functor.
  Defined.
  Definition mult_sequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:sequenceMap) : Sequence.class_of (mult op t) :=
    Sequence.Class (mult_sequence_mixin_of op t).
  Canonical mult_sequenceMap R (idx:R) (op:Monoid.law idx) (t:sequenceMap):
    sequenceMap :=
    Eval hnf in @Sequence.Pack (mult op t) (mult_sequence_class_of op t).    

  Lemma sequence_mult R (idx:R) (op:Monoid.law idx) (t:sequenceMap) :
    @sequence (mult_sequenceMap op t) =
    fun _ _ f => sequence (functor (fun rma =>
                                      match rma with
                                      | (r,ma) => functor (pair r) ma
                                      end) f).
  Proof. done. Qed.
End Sequence_canonicals.

(* ********************* *)

Module Traversable.
  Definition Traverse (t:Type -> Type) :=
    forall (m:applicativeMap) A B, (A -> m B) -> t A -> m (t B).

  Record mixin_of (t:sequenceMap) :=
    Mixin { 
        _: forall (m:Type -> Type) (c d:Applicative.class_of m),
            eq_applicativeMap c d ->
            forall A,
              @sequence t (Applicative.Pack c) A
              =1 @sequence t (Applicative.Pack d) A;
        _: forall A, @sequence t id_applicativeMap A =1 @id _;
        _: forall (m n:applicativeMap) A (x:t (m (n A))),
            @sequence t (comp_applicativeMap _ _) _ x =
            functor (@sequence _ _ _) (sequence x)
      }.
  Section ClassDef.
  Record class_of (t:Type -> Type) :=
    Class {
        base : Sequence.class_of t;
        mixin : mixin_of (Sequence.Pack base)
      }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition functorMap := Functor.Pack (base class).
    Definition sequenceMap := Sequence.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Sequence.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion sequenceMap : map >-> Sequence.map.
    Canonical sequenceMap.
    Notation traverseMap := map.
    Notation Traverse := Traverse.
  End Exports.
End Traversable.
Import Traversable.Exports.

Section Traversable_lemma.
  Variable (t:traverseMap).

  Lemma sequence_eq_applicativeMap : forall m (c d:Applicative.class_of m),
      eq_applicativeMap c d ->
      forall A,
        @sequence t (Applicative.Pack c) A
        =1 @sequence _ (Applicative.Pack d) A.
  Proof. by case : t => func [b []]. Qed.

  Lemma sequence_id : forall A, @sequence t id_applicativeMap A =1 @id _.
  Proof. by case : t => func [b []]. Qed.

  Lemma sequenceD : forall (m n:applicativeMap) A (x:t (m (n A))),
      @sequence t (comp_applicativeMap _ _) _ x =
      functor (@sequence _ _ _) (sequence x).
  Proof. by case : t => func [b []]. Qed.

  Definition traverse : Traverse t := fun _ _ _ f x => sequence (functor f x).

  Lemma traverse_eq_applicativeMap m (c d:Applicative.class_of m) :
    eq_applicativeMap c d -> 
    forall A B (f:A -> m B),
      @traverse (Applicative.Pack c) _ _ f
      =1 @traverse (Applicative.Pack d) _ _ f.
  Proof. move => cd A B f x. exact : sequence_eq_applicativeMap. Qed.

  Lemma eq_traverse : forall (m:applicativeMap) A B (f g:A -> m B),
      f =1 g -> traverse f =1 traverse g.
  Proof. rewrite /traverse => m A B f g fg x. by rewrite (eq_functor fg). Qed.

  Lemma traverse_id A B : @traverse id_applicativeMap A B =2 @functor t _ _.
  Proof. rewrite /traverse => f x. by rewrite sequence_id. Qed.

  Lemma traverseD (m n:applicativeMap) A B C (f:B -> m C) (g:A -> n B) x :
    @traverse (comp_applicativeMap _ _) _ _ (functor f \o g) x
    = functor (traverse f) (traverse g x).
  Proof.
    rewrite /traverse sequenceD [functor (_ \o g) _]functorD.
      by rewrite sequence_functor_functor -functorD.
  Qed.

  Lemma traverse_compf (m:applicativeMap) A B C (f:B -> m C) (g:A -> B) x :
    traverse (f \o g) x = traverse f (functor g x).
  Proof. by rewrite /traverse functorD. Qed.

  Lemma traverse_functor_comp
        (m:applicativeMap) A B C (f:B -> C) (g:A -> m B) x :
    traverse (functor f \o g) x = functor (functor f) (traverse g x).
  Proof. by rewrite /traverse functorD sequence_functor_functor. Qed.

  Lemma sequence_def (m:applicativeMap) A (x:t (m A)):
    sequence x = traverse id x.
  Proof. by rewrite /traverse functor_id. Qed.

End Traversable_lemma.

Definition eq_traverseMap (t:Type -> Type) (c d:Traversable.class_of t) :=
  eq_sequenceMap c d.

Section Traversable_canonicals.
  (* id *)
  Definition id_traverse_mixin_of : Traversable.mixin_of id_sequenceMap.
  Proof.
    apply : Traversable.Mixin =>//= m n A x. by rewrite functor_id.
  Defined.
  Definition id_traverse_class_of : Traversable.class_of id :=
    Traversable.Class id_traverse_mixin_of.
  Definition id_traverseMap : traverseMap :=
    Eval hnf in @Traversable.Pack id id_traverse_class_of.

  (* comp *)
  Definition comp_traverse_mixin_of (t s:traverseMap) :
    Traversable.mixin_of (comp_sequenceMap t s).
  Proof.
    apply : Traversable.Mixin =>/=[m c d cd A x|A x|m n A x];
      rewrite sequence_comp /=.
    - rewrite (sequence_eq_applicativeMap cd).
      congr(@sequence t (Applicative.Pack d)). apply : eq_functor => y.
        by rewrite (sequence_eq_applicativeMap cd).
    - rewrite sequence_id. apply : eq_functor_id. exact : sequence_id.
    - rewrite sequenceD functorD -sequence_functor_functor -functorD.
      congr(functor _ (sequence _)). apply : eq_functor => y /=.
      exact : sequenceD.
  Defined.
  Definition comp_traverse_class_of (m n:traverseMap) :
    Traversable.class_of (fun A => m (n A)) :=
    Traversable.Class (comp_traverse_mixin_of m n).
  Definition comp_traverseMap (m n:traverseMap) : traverseMap :=
    Eval hnf in @Traversable.Pack (fun A => m (n A))
                                  (comp_traverse_class_of m n).

  (* option *)
  Definition option_traverse_mixin_of:
    Traversable.mixin_of option_sequenceMap.
  Proof.
    apply : Traversable.Mixin =>/=[m c d cd A [x|]|A [x|]|m n A [x|]]//;
                              rewrite sequence_option.
    - by case : cd =>[[_ ->] _].
    - by case : cd =>[[-> _] _].
    - rewrite -functorD. exact : eq_functor.
    - by rewrite -applicative_etal applicative_eta_eta.
  Defined.
  Definition option_traverse_class_of : Traversable.class_of option :=
    Traversable.Class option_traverse_mixin_of.
  Canonical option_traverseMap : traverseMap :=
    Eval hnf in @Traversable.Pack option option_traverse_class_of.

  (* seq *)
  Lemma eq_foldr T R (f g:T -> R -> R):
    f =2 g -> foldr f =2 foldr g.
  Proof. move => fg z. by elim =>[|x s /=->]. Qed.

  Definition seq_traverse_mixin_of:
    Traversable.mixin_of seq_sequenceMap.
  Proof.
    apply : Traversable.Mixin =>/=[m c d cd A s|A|m n A];
      rewrite sequence_seq.
    - rewrite /functor2. case : cd =>[[-> cdf] cda]. apply : eq_foldr => y z.
        by rewrite cdf cda.
    - by elim =>[|x s /=->].
    - rewrite /functor2 eta_comp functor_comp applicative_comp /=.
      elim =>[|x s /=->]//=.
      + by rewrite -applicative_etal applicative_eta_eta.
      + rewrite /functor2 -functorD -!applicative_etal -applicativeA.
        rewrite applicative_etar !applicative_etal -!functorD -applicative_etal.
        rewrite -applicativeA applicative_eta_eta applicative_etal -functorD.
        exact : eq_functor2.
  Defined.
  Definition seq_traverse_class_of : Traversable.class_of seq :=
    Traversable.Class seq_traverse_mixin_of.
  Canonical seq_traverseMap : traverseMap :=
    Eval hnf in @Traversable.Pack seq seq_traverse_class_of.

  (* sumt *)
  Definition sumt_traverse_mixin_of R (t:traverseMap):
    Traversable.mixin_of (sumt_sequenceMap R t).
  Proof.
    apply : Traversable.Mixin =>/=[m c d cd A x|A x|m n A x];
      rewrite sequence_sumt.
    - rewrite (sequence_eq_applicativeMap cd).
      case : cd =>[[eta_cd fun_cd] app_cd].
      congr(@sequence t (Applicative.Pack d)). apply : eq_functor =>[[r|ma]].
      + exact : eta_cd.
      + exact : fun_cd.
    - rewrite sequence_id. exact : eq_functor_id.
    - rewrite functorD sequenceD. congr(functor).
      rewrite -(@sequence_functor_functor t) -functorD. congr(sequence).
      apply : eq_functor =>[[r|ma]]/=.
      + by rewrite -applicative_etal applicative_eta_eta.
      + rewrite -functorD. exact : eq_functor.
  Defined.
  Definition sumt_traverse_class_of R (t:traverseMap):
    Traversable.class_of (sumt R t) :=
    Traversable.Class (sumt_traverse_mixin_of R t).
  Canonical sumt_traverseMap R (t:traverseMap) : traverseMap :=
    Eval hnf in @Traversable.Pack (sumt R t) (sumt_traverse_class_of R t).

  (* mult *)
  Definition mult_traverse_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:traverseMap): Traversable.mixin_of (mult_sequenceMap op t).
  Proof.
    apply : Traversable.Mixin =>[m c d cd A x|A x|m n A x];
                                  rewrite sequence_mult.
    - rewrite (sequence_eq_applicativeMap cd).
      case : cd =>[[_ fun_cd] _].
      congr(@sequence t (Applicative.Pack d)). apply : eq_functor =>[[r ma]].
      exact : fun_cd.
    - rewrite sequence_id. apply : eq_functor_id. exact : eq_functor_id.
    - rewrite functorD sequenceD. congr(@functor m).
      rewrite -(@sequence_functor_functor t) -functorD. congr(sequence).
      apply : eq_functor =>[[r ma]]/=. rewrite -functorD.
      exact : eq_functor.
  Defined.
  Definition mult_traverse_class_of R (idx:R) (op:Monoid.law idx)
             (t:traverseMap) : Traversable.class_of (mult op t) :=
    Traversable.Class (mult_traverse_mixin_of op t).
  Canonical mult_traverseMap R (idx:R) (op:Monoid.law idx) (t:traverseMap):
    traverseMap :=
    Eval hnf in @Traversable.Pack (mult op t) (mult_traverse_class_of op t).    
End Traversable_canonicals.

(* ********************* *)

Module RCompKleisli.
  Record mixin_of (t:kleisliMap) (sequence:Sequence t) :=
    Mixin {
        _: forall (m:akleisliMap) A (x:m A),
          sequence _ _ (eta _ x) = functor (@eta _ _) x;
        _: forall (m:akleisliMap) A (x:t A),
            sequence _ _ (functor (@eta m _) x) = eta _ x;
        _: forall (m:akleisliMap) A (x:t (t (m A))),
            sequence _ _ (mu x) =
            functor (@mu _ _) (sequence _ _ (functor (sequence _ _) x));
        _: forall (m:akleisliMap) A (x:t (m (m A))),
            sequence  _ _ (functor (@mu _ _) x) =
            mu (functor (sequence _ _) (sequence _ _ x))
      }.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Kleisli.class_of t;
          sMixin : Sequence.mixin_of (Functor.Pack base);
          mixin : @mixin_of (Kleisli.Pack base) (Sequence.sequence sMixin)
        }.
    Definition sequence_class_of t class :=
      Sequence.Class (@sMixin t class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
    Definition kleisliMap := Kleisli.Pack (base class).
    Definition sequenceMap := Sequence.Pack (sequence_class_of class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Kleisli.class_of.
    Coercion sMixin : class_of >-> Sequence.mixin_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Coercion kleisliMap : map >-> Kleisli.map.
    Canonical kleisliMap.
    Coercion sequence_class_of : class_of >-> Sequence.class_of.
    Coercion sequenceMap : map >-> Sequence.map.
    Canonical sequenceMap.
    Notation rcompKleisliMap := map.
  End Exports.
End RCompKleisli.
Import RCompKleisli.Exports.

Section RCompKleisli_lemma.
  Variable (t:rcompKleisliMap).
  Let sequence := @sequence t.

  Lemma sequence_eta : forall (m:akleisliMap) A (x:m A),
      sequence (eta t x) = functor (@eta _ _) x.
  Proof. rewrite /sequence. by case : t => func [b sm []]. Qed.

  Lemma sequence_functor_eta : forall (m:akleisliMap) A (x:t A),
      sequence (functor (@eta m _) x) = eta m x.
  Proof. rewrite /sequence. by case : t => func [b sm []]. Qed.

  Lemma sequence_mu : forall (m:akleisliMap) A (x:t (t (m A))),
      sequence (@mu t _ x) =
      functor (@mu t _) (sequence (functor (@sequence _ _) x)).
  Proof. rewrite /sequence. by case : t => func [b sm []]. Qed.

  Lemma sequence_functor_mu : forall (m:akleisliMap) A (x:t (m (m A))),
      sequence (functor (@mu _ _) x) =
      mu (functor (@sequence _ _) (sequence x)).
  Proof. rewrite /sequence. by case : t => func [b sm []]. Qed.
End RCompKleisli_lemma.

Definition rcomp_monad_class_of (m:akleisliMap) (t:rcompKleisliMap):
  Monad.class_of (fun A => m (t A)).
Proof.
  apply : (@Monad.Class _ (comp_pfunctor_class_of m t)).
  apply : (@Monad.Mixin
             _ ((fun _ => functor (@mu _ _) \o (@mu _ _) \o
                                  functor (@sequence t m _)) :
                  Mu (comp_pfunctorMap m t)))
            =>/=[A x|A x|A x].
  - rewrite eta_comp /= functor_eta mu_eta sequence_eta -functorD.
    rewrite (eq_functor (g:=id)) ?functor_id =>// y /=.
      by rewrite mu_eta.
  - rewrite functor_comp eta_comp /= -functorD.
    rewrite (eq_functor (g:= @eta m _ \o functor (@eta t _)))=>[|y]/=.
    + rewrite functorD mu_functor_eta -functorD.
      rewrite (eq_functor (g:=id)) ?functor_id =>// y /=.
        by rewrite mu_functor_eta.
    + by rewrite functorD sequence_functor_eta.
  - rewrite !functor_mu -!functorD -mu_functor_mu -functorD. congr(mu).
    apply : eq_functor =>{x} x /=.
    rewrite 2!functorD sequence_functor_functor sequence_functor_mu.
    rewrite !functor_mu sequence_functor_functor -!functorD. congr(mu).
    apply : eq_functor =>{x} x /=.
    rewrite sequence_mu -!functorD. apply : eq_functor =>{x} x /=.
      by rewrite mu_functor_mu.
Defined.

Definition rcomp_kleisli_class_of (m:akleisliMap) (t:rcompKleisliMap):
  Kleisli.class_of (fun A => m (t A)).
Proof.
  apply : (@Kleisli.Class _ (rcomp_monad_class_of m t)).
  apply : Kleisli.Mixin =>/=[A B f x|A B f x].
  - by rewrite functor_comp eta_comp /= !functor_eta.
  - rewrite !functor_comp /mu /= -!functorD.
    rewrite (eq_functor (g:= @mu t _ \o functor (functor f)))
    =>[|y]/=; [|by rewrite functor_mu].
    rewrite (eq_functor
               (g:=functor (functor (functor f)) \o @sequence t m _))
    =>[|y]/=; [|by rewrite sequence_functor_functor].
    rewrite 2!functorD. congr (functor). by rewrite functor_mu.
Defined.
Definition rcomp_kleisliMap (m:akleisliMap) (t:rcompKleisliMap) :=
  Eval hnf in @Kleisli.Pack (fun A => m (t A)) (rcomp_kleisli_class_of m t).

Definition rcomp_hkleisliMap (m:kleisliMap) (t:rcompKleisliMap) :=
  rcomp_kleisliMap (hkleisli m) t.
Definition rcomp_vkleisliMap (m:kleisliMap) (t:rcompKleisliMap) :=
  rcomp_kleisliMap (vkleisli m) t.

Section RCompKleisli_canonicals.
  (* id *)
  Definition id_rcompKleisli_mixin_of :
    @RCompKleisli.mixin_of
      id_kleisliMap (Sequence.sequence id_sequence_mixin_of).
  Proof.
      by apply : RCompKleisli.Mixin
                   =>/=[m A x||m A x|m A x]//; rewrite !functor_id.
  Defined.
  Definition id_rcompKleisli_class_of : RCompKleisli.class_of id :=
    RCompKleisli.Class id_rcompKleisli_mixin_of.
  Definition id_rcompKleisliMap : rcompKleisliMap :=
    Eval hnf in @RCompKleisli.Pack id id_rcompKleisli_class_of.

  (* option *)
  Definition option_rcompKleisli_mixin_of :
    @RCompKleisli.mixin_of
      option_kleisliMap (Sequence.sequence option_sequence_mixin_of).
  Proof.
    apply : RCompKleisli.Mixin =>[|m A [x|]|m A [[x|]|]|m A [x|]]//=.
    - by rewrite functor_eta.
    - rewrite -!functorD. exact : eq_functor.
    - by rewrite -functorD functor_eta.
    - by rewrite functor_eta.
    - by rewrite functor_mu -functorD.
    - by rewrite functor_eta mu_eta.
  Defined.
  Definition option_rcompKleisli_class_of : RCompKleisli.class_of option :=
    RCompKleisli.Class option_rcompKleisli_mixin_of.
  Definition option_rcompKleisliMap : rcompKleisliMap :=
    Eval hnf in @RCompKleisli.Pack option option_rcompKleisli_class_of.
(*
  (* seq *)
  Definition seq_rcompKleisli_mixin_of :
    @RCompKleisli.mixin_of
      seq_kleisliMap (Sequence.sequence seq_sequence_mixin_of).
  Proof.
    apply : RCompKleisli.Mixin =>/=[m A x|m A|m A|m A]//=;
    rewrite /functor2.
    - by rewrite /functor2 applicative_etar -functorD.
    - elim =>[|x s /=->]//. by rewrite applicative_etar !functor_eta.
    - rewrite /mu /=. elim =>[|s ss IHss]/=.
      + by rewrite functor_eta.
      + rewrite foldr_cat IHss foldr_map -!applicative_etal -applicativeA.
        rewrite applicative_eta_eta !applicative_etal -functorD.
        elim : s {IHss} =>[|x s /=->]//=.
        * rewrite functor_eta applicative_etal /=. exact : eq_functor.
        * rewrite -!applicative_etal -2!applicativeA !applicative_etal.
          rewrite applicative_etar -!functorD -applicative_etal.
          rewrite -applicativeA applicative_eta_eta applicative_etal.
          rewrite -functorD. exact : eq_functor3.
    - elim =>[|x s /=->]//=.
      + by rewrite functor_eta mu_eta.
      + rewrite -!applicative_etal -applicativeA applicative_eta_eta.
        rewrite !applicative_etal -functorD.
 *)

  (* sumt *)
  Definition sumt_rcompKleisli_mixin_of R (t:rcompKleisliMap):
    @RCompKleisli.mixin_of
      (sumt_kleisliMap R t) (Sequence.sequence (sumt_sequence_mixin_of R t)).
  Proof.
    apply : RCompKleisli.Mixin =>[m A x|m A x|m A x|m A x]/=.
    - by rewrite functor_eta [in RHS]functorD sequence_eta.
    - rewrite -functorD -sequence_functor_eta. congr(@sequence t).
      apply : eq_functor =>[[r|a]]//=. by rewrite functor_eta.
    - rewrite functor_mu sequence_mu [in RHS]functorD. congr(functor).
      rewrite -(@sequence_functor_functor t) -!functorD. congr(sequence).
      apply : eq_functor =>[[r|y]]/=.
      + by rewrite !functor_eta sequence_eta functor_eta.
      + by rewrite -functorD eq_functor_id.
    - rewrite [in RHS]functorD -(@sequence_functor_functor t).
      rewrite -sequence_functor_mu -!functorD. congr(@sequence t).
      apply : eq_functor =>[[r|ma]]/=.
      + by rewrite functor_eta mu_eta.
      + by rewrite -functorD functor_mu.
  Defined.
  Definition sumt_rcompKleisli_class_of R (t:rcompKleisliMap) :
    RCompKleisli.class_of (sumt R t) :=
    RCompKleisli.Class (sumt_rcompKleisli_mixin_of R t).
  Definition sumt_rcompKleisliMap R (t:rcompKleisliMap) : rcompKleisliMap :=
    Eval hnf in @RCompKleisli.Pack (sumt R t) (sumt_rcompKleisli_class_of R t).

  (* mult *)
  Definition mult_rcompKleisli_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:rcompKleisliMap):
    @RCompKleisli.mixin_of
      (mult_kleisliMap op t) (Sequence.sequence (mult_sequence_mixin_of op t)).
  Proof.
    apply : RCompKleisli.Mixin =>[m A x|m A x|m A x|m A x]/=.
    - by rewrite functor_eta sequence_eta -functorD.
    - rewrite -functorD -sequence_functor_eta. congr(@sequence t).
      apply : eq_functor =>[[r ma]]/=. by rewrite functor_eta.
    - rewrite functor_mu sequence_mu [in RHS]functorD. congr(functor).
      rewrite -(@sequence_functor_functor t) -!functorD. congr(sequence).
      apply : eq_functor =>[[r ma]]/=. rewrite -!functorD.
      rewrite (eq_functor
                 (g:=functor
                       (fun bx : _ * _ => let (b,x) := bx in (op r b,x))))=>//.
      rewrite -sequence_functor_functor -functorD. congr(sequence).
      apply : eq_functor =>[[s a]]/=. by rewrite -functorD.
    - rewrite [in RHS]functorD -(@sequence_functor_functor t).
      rewrite -sequence_functor_mu -!functorD. congr(@sequence t).
      apply : eq_functor =>[[r ma]]/=. by rewrite functor_mu -functorD.
  Defined.
  Definition mult_rcompKleisli_class_of R (idx:R) (op:Monoid.law idx)
             (t:rcompKleisliMap) : RCompKleisli.class_of (mult op t) :=
    RCompKleisli.Class (mult_rcompKleisli_mixin_of op t).
  Definition mult_rcompKleisliMap R (idx:R) (op:Monoid.law idx)
             (t:rcompKleisliMap) : rcompKleisliMap :=
    Eval hnf in
      @RCompKleisli.Pack (mult op t) (mult_rcompKleisli_class_of op t).  
End RCompKleisli_canonicals.
