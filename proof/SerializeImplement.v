Require Import Ascii List.
Require Import ListUtil Object MultiByte Util SerializeSpec ProofUtil.

Open Scope char_scope.

Definition serialize_rev_list (serialize_rev: object -> list ascii8 -> list ascii8) :=
  fix F os acc :=
    match os with
    | [] => acc
    | o :: os => F os (serialize_rev o acc)
    end.

Definition serialize_rev_kvs (serialize_rev: object -> list ascii8 -> list ascii8) :=
  fix F ps acc :=
    match ps with
    | [] => acc
    | (k,v) :: ps => F ps (serialize_rev v (serialize_rev k acc))
    end.

Fixpoint serialize_rev (obj : object) acc : list ascii8 :=
  match obj with
    | Nil        => "192" :: acc
    | Bool false => "194" :: acc
    | Bool true  => "195" :: acc
    | PFixnum (Ascii b1 b2 b3 b4 b5 b6 b7 _) =>
      (Ascii b1 b2 b3 b4 b5 b6 b7 false) :: acc
    | NFixnum (Ascii b1 b2 b3 b4 b5 _ _ _) =>
      (Ascii b1 b2 b3 b4 b5 true true true) :: acc
    | Uint8  c => rev_append (list_of_ascii8  c) ("204":: acc)
    | Uint16 c => rev_append (list_of_ascii16 c) ("205" :: acc)
    | Uint32 c => rev_append (list_of_ascii32 c) ("206" :: acc)
    | Uint64 c => rev_append (list_of_ascii64 c) ("207" :: acc)
    | Int8   c => rev_append (list_of_ascii8  c) ("208" :: acc)
    | Int16  c => rev_append (list_of_ascii16 c) ("209" :: acc)
    | Int32  c => rev_append (list_of_ascii32 c) ("210" :: acc)
    | Int64  c => rev_append (list_of_ascii64 c) ("211" :: acc)
    | Float  c => rev_append (list_of_ascii32 c) ("202" :: acc)
    | Double c => rev_append (list_of_ascii64 c) ("203" :: acc)
    | FixRaw xs =>
      match ascii8_of_nat @@ length_tailrec xs with
        | Ascii b1 b2 b3 b4 b5 _ _ _ =>
          rev_append xs ((Ascii b1 b2 b3 b4 b5 true false true) :: acc)
      end
    | Raw16 xs =>
      let (s1,s2) := ascii16_of_nat @@ length_tailrec xs in
      rev_append xs (s2 :: s1 :: "218" :: acc)
    | Raw32 xs =>
      match ascii32_of_nat @@ length_tailrec xs with
        | ((s1,s2),(s3,s4)) =>
          rev_append xs (s4 :: s3 :: s2 :: s1 :: "219" :: acc)
      end
    | FixArray xs =>
      match ascii8_of_nat @@ length_tailrec xs with
        | Ascii b1 b2 b3 b4 _ _ _ _ =>
          serialize_rev_list serialize_rev xs
            ((Ascii b1 b2 b3 b4 true false false true) :: acc)
      end
    | Array16 xs =>
      let (s1, s2) := ascii16_of_nat @@ length_tailrec xs in
      serialize_rev_list serialize_rev xs (s2 :: s1 :: "220" :: acc)
    | Array32 xs =>
      match ascii32_of_nat @@ length_tailrec xs with
        | ((s1,s2),(s3,s4)) =>
          serialize_rev_list serialize_rev xs (s4 :: s3 :: s2 :: s1 :: "221" :: acc)
      end
    | FixMap xs =>
      match ascii8_of_nat @@ length_tailrec xs with
        | Ascii b1 b2 b3 b4 _ _ _ _ =>
          serialize_rev_kvs serialize_rev xs
            ((Ascii b1 b2 b3 b4 false false false true) :: acc)
      end
    | Map16 xs =>
      let (s1, s2) := ascii16_of_nat @@ length_tailrec xs in
      serialize_rev_kvs serialize_rev xs (s2 :: s1 :: "222" :: acc)
    | Map32 xs =>
      match ascii32_of_nat @@ length_tailrec xs with
        | ((s1,s2),(s3,s4)) =>
          serialize_rev_kvs serialize_rev xs (s4 :: s3 :: s2 :: s1 :: "223" :: acc)
      end
  end.

Definition Correct obj xs :=
  forall acc,
  Serialized obj xs ->
  serialize_rev obj acc = rev_append xs acc.

Ltac straitfoward :=
  unfold Correct;
  intros;
  simpl;
  reflexivity.

Lemma correct_nil:
  Correct Nil ["192"].
Proof.
straitfoward.
Qed.

Lemma correct_false:
  Correct (Bool false) ["194"].
Proof.
straitfoward.
Qed.

Lemma correct_true:
  Correct (Bool true) ["195"].
Proof.
straitfoward.
Qed.

Lemma correct_pfixnum: forall x1 x2 x3 x4 x5 x6 x7,
  Correct (PFixnum   (Ascii x1 x2 x3 x4 x5 x6 x7 false))
          [Ascii x1 x2 x3 x4 x5 x6 x7 false].
Proof.
straitfoward.
Qed.

Lemma correct_nfixnum: forall x1 x2 x3 x4 x5,
  Correct (NFixnum   (Ascii x1 x2 x3 x4 x5 true true true))
          [Ascii x1 x2 x3 x4 x5 true true true].
Proof.
straitfoward.
Qed.

Lemma correct_uint8 : forall c,
  Correct (Uint8 c) ("204"::list_of_ascii8 c).
Proof.
straitfoward.
Qed.

Lemma correct_uint16 : forall c,
  Correct (Uint16 c) ("205"::list_of_ascii16 c).
Proof.
straitfoward.
Qed.

Lemma correct_uint32 : forall c,
  Correct (Uint32 c) ("206"::list_of_ascii32 c).
Proof.
straitfoward.
Qed.

Lemma correct_uint64 : forall c,
  Correct (Uint64 c) ("207"::list_of_ascii64 c).
Proof.
straitfoward.
Qed.

Lemma correct_int8 : forall c,
  Correct (Int8 c) ("208"::list_of_ascii8 c).
Proof.
straitfoward.
Qed.

Lemma correct_int16 : forall c,
  Correct (Int16 c) ("209"::list_of_ascii16 c).
Proof.
straitfoward.
Qed.

Lemma correct_int32 : forall c,
  Correct (Int32 c) ("210"::list_of_ascii32 c).
Proof.
straitfoward.
Qed.

Lemma correct_int64 : forall c,
  Correct (Int64 c) ("211"::list_of_ascii64 c).
Proof.
straitfoward.
Qed.

Lemma correct_float : forall c,
  Correct (Float c) ("202"::list_of_ascii32 c).
Proof.
straitfoward.
Qed.

Lemma correct_double : forall c,
  Correct (Double c) ("203"::list_of_ascii64 c).
Proof.
straitfoward.
Qed.

Lemma correct_fixraw : forall cs b1 b2 b3 b4 b5,
  Ascii b1 b2 b3 b4 b5 false false false = ascii8_of_nat (length cs) ->
  Correct (FixRaw cs) ((Ascii b1 b2 b3 b4 b5 true false true)::cs).
Proof.
unfold Correct.
intros.
inversion H0.
simpl.
rewrite length_tailrec_equiv.
rewrite_for (ascii8_of_nat (length cs)).
reflexivity.
Qed.

Lemma correct_raw16: forall cs s1 s2,
  (s1,s2) =  ascii16_of_nat (length cs) ->
  Correct (Raw16 cs) ("218"::s1::s2::cs).
Proof.
unfold Correct.
intros.
inversion H0.
simpl.
rewrite length_tailrec_equiv.
rewrite_for (ascii16_of_nat (length cs)).
reflexivity.
Qed.

Lemma correct_raw32 : forall cs s1 s2 s3 s4,
  ((s1,s2),(s3,s4)) =  ascii32_of_nat (length cs) ->
  Correct (Raw32 cs) ("219"::s1::s2::s3::s4::cs).
Proof.
unfold Correct.
intros.
inversion H0.
simpl.
rewrite length_tailrec_equiv.
rewrite_for (ascii32_of_nat (length cs)).
reflexivity.
Qed.

Lemma correct_fixarray_nil:
  Correct (FixArray []) ["144"].
Proof.
straitfoward.
Qed.

Lemma correct_array16_nil:
  Correct (Array16 []) ["220"; "000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
rewrite <- ascii8_of_nat_O.
reflexivity.
Qed.

Lemma correct_array32_nil:
  Correct (Array32 []) ["221"; "000"; "000";"000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
rewrite <- ascii8_of_nat_O.
reflexivity.
Qed.

Lemma correct_fixmap_nil:
  Correct (FixMap []) ["128"].
Proof.
straitfoward.
Qed.

Lemma correct_map16_nil:
  Correct (Map16 []) ["222"; "000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
rewrite <- ascii8_of_nat_O.
reflexivity.
Qed.

Lemma correct_map32_nil:
  Correct (Map32 []) ["223"; "000"; "000";"000"; "000"].
Proof.
unfold Correct.
intros.
simpl.
rewrite <- ascii8_of_nat_O.
reflexivity.
Qed.

Lemma Prepending_serialize_rev_list': forall f os, (Forall (fun o => Prepending (f o))) os ->
  Prepending (serialize_rev_list f os).
Proof.
  unfold Prepending. intros * H.
  induction H; [reflexivity|].
  intros ys zs. simpl. rewrite H. apply IHForall.
Qed.

Lemma Prepending_serialize_rev_kvs': forall f ps,
  (Forall (fun p => Prepending (f (fst p)) /\ Prepending (f (snd p)))) ps ->
  Prepending (serialize_rev_kvs f ps).
Proof.
  unfold Prepending. intros * H.
  induction H as [|[x1 x2] ? [H1 H2]]; [reflexivity|].
  intros ys zs. simpl. rewrite H1, H2. apply IHForall.
Qed.

Lemma Prepending_serialize_rev: forall o,
  Prepending (serialize_rev o).
Proof.
unfold Prepending.
intros.
generalize ys zs; clear ys zs.
induction o using object_ind'; intros ys zs; simpl.
- destruct x; reflexivity.
- reflexivity.
- destruct x. reflexivity.
- destruct x. reflexivity.
- reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- rewrite <-Prepending_rev_append. reflexivity.
- destruct (ascii8_of_nat (length_tailrec x)). rewrite <-Prepending_rev_append. reflexivity.
- destruct (ascii16_of_nat (length_tailrec x)). rewrite <-Prepending_rev_append. reflexivity.
- destruct (ascii32_of_nat (length_tailrec x)) as [[? ?] [? ?]].
  rewrite <-Prepending_rev_append. reflexivity.
- destruct (ascii8_of_nat (length_tailrec os)) as [b1 b2 b3 b4 b5 b6 b7 b8].
  rewrite app_comm_cons.
  generalize ((Ascii b1 b2 b3 b4 true false false true :: ys)); intros.
  apply (Prepending_serialize_rev_list' serialize_rev).
  apply H.
- destruct (ascii16_of_nat (length_tailrec os)) as [s1 s2].
  rewrite !app_comm_cons.
  generalize ((s2 :: s1 :: "220" :: ys)); intros.
  apply (Prepending_serialize_rev_list' serialize_rev).
  apply H.
- destruct (ascii32_of_nat (length_tailrec os)) as [[s1 s2] [s3 s4]].
  rewrite !app_comm_cons.
  generalize ((s4 :: s3 :: s2 :: s1 :: "221" :: ys)); intros.
  apply (Prepending_serialize_rev_list' serialize_rev).
  apply H.
- destruct (ascii8_of_nat (length_tailrec ps)) as [b1 b2 b3 b4 b5 b6 b7 b8].
  rewrite app_comm_cons.
  generalize ((Ascii b1 b2 b3 b4 false false false true :: ys)); intros.
  apply (Prepending_serialize_rev_kvs' serialize_rev).
  apply H.
- destruct (ascii16_of_nat (length_tailrec ps)) as [s1 s2].
  rewrite !app_comm_cons.
  generalize ((s2 :: s1 :: "222" :: ys)); intros.
  apply (Prepending_serialize_rev_kvs' serialize_rev).
  apply H.
- destruct (ascii32_of_nat (length_tailrec ps)) as [[s1 s2] [s3 s4]].
  rewrite !app_comm_cons.
  generalize ((s4 :: s3 :: s2 :: s1 :: "223" :: ys)); intros.
  apply (Prepending_serialize_rev_kvs' serialize_rev).
  apply H.
Qed.

Lemma Prepending_serialize_rev_list: forall os,
  Prepending (serialize_rev_list serialize_rev os).
Proof.
  intros.
  apply Prepending_serialize_rev_list'.
  apply Forall_forall.
  intros.
  apply Prepending_serialize_rev.
Qed.

Lemma Prepending_serialize_rev_kvs: forall ps,
  Prepending (serialize_rev_kvs serialize_rev ps).
Proof.
  intros.
  apply Prepending_serialize_rev_kvs'.
  apply Forall_forall.
  intros.
  split; apply Prepending_serialize_rev.
Qed.


Lemma correct_fixarray_cons: forall x xs y ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length (x::xs)) ->
  Serialized x y ->
  Correct x y ->
  Serialized (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Correct (FixArray xs) ((Ascii b1 b2 b3 b4 true false false true)::ys) ->
  Correct (FixArray (x :: xs)) ((Ascii b5 b6 b7 b8 true false false true)::y ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
rewrite length_tailrec_equiv in *.
simpl.
rewrite_for (ascii8_of_nat (S (length xs))).
eapply H2 in H1.
apply (H4 acc) in H3.
rewrite_for (ascii8_of_nat (length xs)).
rewrite rev_append_app_left.
rewrite <-H1.
rewrite (Prepending_nil _ (Prepending_rev_append _ _)).
rewrite (Prepending_nil (serialize_rev_list serialize_rev xs)); [|apply Prepending_serialize_rev_list].
rewrite (Prepending_nil _ (Prepending_rev_append _ _)) in H3.
rewrite (Prepending_nil (serialize_rev_list serialize_rev xs)) in H3; [|apply Prepending_serialize_rev_list].
apply app_inv_tail in H3.
rewrite H3.
reflexivity.
Qed.

Lemma correct_array16_cons: forall x xs t1 t2 s1 s2 y ys,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length (x :: xs)) ->
  Serialized x y ->
  (Serialized x y -> Correct x y) ->
  Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
  (Serialized (Array16 xs) ("220" :: t1 :: t2 :: ys) ->
    Correct (Array16 xs) ("220" :: t1 :: t2 :: ys)) ->
  Correct (Array16 (x :: xs)) ("220" :: s1 :: s2 :: y ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
rewrite length_tailrec_equiv in *.
simpl.
rewrite_for (ascii16_of_nat (S (length xs))).
eapply H2 in H1; auto.
specialize (H4 H3 acc).
rewrite_for (ascii16_of_nat (length xs)).
rewrite rev_append_app_left.
rewrite <-H1.
rewrite (Prepending_nil _ (Prepending_rev_append _ _)).
rewrite (Prepending_nil (serialize_rev_list serialize_rev xs)); [|apply Prepending_serialize_rev_list].
rewrite (Prepending_nil _ (Prepending_rev_append _ _)) in H4.
rewrite (Prepending_nil (serialize_rev_list serialize_rev xs)) in H4; [|apply Prepending_serialize_rev_list].
apply app_inv_tail in H4; auto.
rewrite H4.
reflexivity.
Qed.

Lemma correct_array32_cons: forall x xs y ys s1 s2 s3 s4 t1 t2 t3 t4,
  ((t1,t2),(t3,t4)) = ascii32_of_nat (length xs) ->
  ((s1,s2),(s3,s4)) = ascii32_of_nat (length (x::xs)) ->
  Serialized x y ->
  (Serialized x y -> Correct x y) ->
  Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) ->
  (Serialized (Array32 xs) ("221"::t1::t2::t3::t4::ys) -> Correct (Array32 xs) ("221"::t1::t2::t3::t4::ys)) ->
  Correct (Array32 (x::xs)) ("221"::s1::s2::s3::s4::y ++ ys).
Proof.
  unfold Correct.
  intros.
  simpl in *.
  rewrite length_tailrec_equiv in *.
  simpl.
  rewrite_for (ascii32_of_nat (S (length xs))).
  eapply H2 in H1; auto.
  specialize (H4 H3 acc).
  rewrite_for (ascii32_of_nat (length xs)).
  rewrite rev_append_app_left.
  rewrite <-H1.
  rewrite (Prepending_nil _ (Prepending_rev_append _ _)).
  rewrite (Prepending_nil (serialize_rev_list serialize_rev xs)); [|apply Prepending_serialize_rev_list].
  rewrite (Prepending_nil _ (Prepending_rev_append _ _)) in H4.
  rewrite (Prepending_nil (serialize_rev_list serialize_rev xs)) in H4; [|apply Prepending_serialize_rev_list].
  apply app_inv_tail in H4; auto.
  rewrite H4.
  reflexivity.
Qed.

Lemma correct_fixmap_cons: forall x1 x2 xs y1 y2 ys b1 b2 b3 b4 b5 b6 b7 b8,
  Ascii b1 b2 b3 b4 false false false false = ascii8_of_nat (length xs) ->
  Ascii b5 b6 b7 b8 false false false false = ascii8_of_nat (length ((x1,x2)::xs)) ->
  Serialized x1 y1 -> Correct x1 y1 ->
  Serialized x2 y2 -> Correct x2 y2 ->
  Serialized (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Correct (FixMap xs) (Ascii b1 b2 b3 b4 false false false true :: ys) ->
  Correct (FixMap ((x1, x2) :: xs)) (Ascii b5 b6 b7 b8 false false false true :: y1 ++ y2 ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
rewrite length_tailrec_equiv in *.
simpl.
rewrite_for (ascii8_of_nat (S (length xs))).
eapply H2 in H1.
eapply H4 in H3.
apply (H6 acc) in H5.
rewrite_for (ascii8_of_nat (length xs)).
do 2 rewrite rev_append_app_left.
rewrite <-H1, <-H3.
rewrite (Prepending_nil _ (Prepending_rev_append _ _)).
rewrite (Prepending_nil (serialize_rev_kvs serialize_rev xs)); [|apply Prepending_serialize_rev_kvs].
rewrite (Prepending_nil _ (Prepending_rev_append _ _)) in H5.
rewrite (Prepending_nil (serialize_rev_kvs serialize_rev xs)) in H5; [|apply Prepending_serialize_rev_kvs].
apply app_inv_tail in H5.
rewrite H5.
reflexivity.
Qed.

Lemma correct_map16_cons: forall x1 x2 xs y1 y2 ys s1 s2 t1 t2,
  (t1, t2) = ascii16_of_nat (length xs) ->
  (s1, s2) = ascii16_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Correct x1 y1 ->
  Serialized x2 y2 ->
  Correct x2 y2 ->
  Serialized (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Correct (Map16 xs) ("222" :: t1 :: t2 :: ys) ->
  Correct (Map16 ((x1, x2) :: xs)) ("222" :: s1 :: s2 :: y1 ++ y2 ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
rewrite length_tailrec_equiv in *.
simpl.
rewrite_for (ascii16_of_nat (S (length xs))).
eapply H2 in H1.
eapply H4 in H3.
apply (H6 acc) in H5.
rewrite_for (ascii16_of_nat (length xs)).
do 2 rewrite rev_append_app_left.
rewrite <-H1, <-H3.
rewrite (Prepending_nil _ (Prepending_rev_append _ _)).
rewrite (Prepending_nil (serialize_rev_kvs serialize_rev xs)); [|apply Prepending_serialize_rev_kvs].
rewrite (Prepending_nil _ (Prepending_rev_append _ _)) in H5.
rewrite (Prepending_nil (serialize_rev_kvs serialize_rev xs)) in H5; [|apply Prepending_serialize_rev_kvs].
apply app_inv_tail in H5.
rewrite H5.
reflexivity.
Qed.

Lemma correct_map32_cons : forall x1 x2 xs y1 y2 ys s1 s2 s3 s4 t1 t2 t3 t4,
  (t1, t2, (t3, t4)) = ascii32_of_nat (length xs) ->
  (s1, s2, (s3, s4)) = ascii32_of_nat (length ((x1, x2) :: xs)) ->
  Serialized x1 y1 ->
  Correct x1 y1 ->
  Serialized x2 y2 ->
  Correct x2 y2 ->
  Serialized (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Correct (Map32 xs) ("223" :: t1 :: t2 :: t3 :: t4 :: ys) ->
  Correct (Map32 ((x1, x2) :: xs)) ("223" :: s1 :: s2 :: s3 :: s4 :: y1 ++ y2 ++ ys).
Proof.
unfold Correct.
intros.
simpl in *.
rewrite length_tailrec_equiv in *.
simpl.
rewrite_for (ascii32_of_nat (S (length xs))).
eapply H2 in H1.
eapply H4 in H3.
apply (H6 acc) in H5.
rewrite <-H in *.
do 2 rewrite rev_append_app_left.
rewrite <-H1, <-H3.
rewrite (Prepending_nil _ (Prepending_rev_append _ _)).
rewrite (Prepending_nil (serialize_rev_kvs serialize_rev xs)); [|apply Prepending_serialize_rev_kvs].
rewrite (Prepending_nil _ (Prepending_rev_append _ _)) in H5.
rewrite (Prepending_nil (serialize_rev_kvs serialize_rev xs)) in H5; [|apply Prepending_serialize_rev_kvs].
apply app_inv_tail in H5.
rewrite H5.
reflexivity.
Qed.

Lemma correct_intro : forall obj xs,
  (Serialized obj xs -> Correct obj xs) ->
  Correct obj xs.
Proof.
unfold Correct.
intros.
auto.
Qed.

Hint Resolve
  correct_true correct_false
  correct_nil correct_pfixnum correct_nfixnum
  correct_uint8 correct_uint16 correct_uint32 correct_uint64
  correct_int8  correct_int16  correct_int32  correct_int64
  correct_float correct_double
  correct_raw16 correct_raw32
  correct_fixarray_nil correct_array16_nil correct_array32_nil
  correct_fixmap_nil correct_map16_nil correct_map32_nil
  : correct.


Theorem serialize_correct : forall obj xs,
  Correct obj xs.
Proof.
intros.
apply correct_intro.
intro.
pattern obj,xs.
apply Serialized_ind; intros; auto with correct.
 apply correct_fixraw; auto.
 apply correct_fixarray_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply correct_array16_cons with (t1:=t1) (t2:=t2); auto.
 apply correct_array32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
 apply correct_fixmap_cons with (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4); auto.
 apply correct_map16_cons with (t1:=t1) (t2:=t2); auto.
 apply correct_map32_cons with (t1:=t1) (t2:=t2) (t3:=t3) (t4:=t4); auto.
Qed.

