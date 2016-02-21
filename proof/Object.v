(* -*- coding:utf-8 -*- *)
Require Import List Ascii.
Require Import Pow MultiByte ListUtil.

Open Scope char_scope.

(** MsgPackで使うオブジェクトの定義 *)
Inductive object :=
| Bool (_ : bool)
| Nil
| PFixnum (_ : ascii8)
| NFixnum (_ : ascii8)
| Uint8  (_ : ascii8)
| Uint16 (_ : ascii16)
| Uint32 (_ : ascii32)
| Uint64 (_ : ascii64)
| Int8   (_ : ascii8)
| Int16  (_ : ascii16)
| Int32  (_ : ascii32)
| Int64  (_ : ascii64)
| Float  (_ : ascii32)
| Double (_ : ascii64)
| FixRaw (_ : list ascii8)
| Raw16  (_ : list ascii8)
| Raw32  (_ : list ascii8)
| FixArray ( _ : list object)
| Array16  ( _ : list object)
| Array32  ( _ : list object)
| FixMap   ( _ : list (object * object)%type)
| Map16    ( _ : list (object * object)%type)
| Map32    ( _ : list (object * object)%type).

(** 妥当なオブジェクトの定義 *)
Inductive Valid : object -> Prop :=
| VBool : forall b,
  Valid (Bool b)
| VPFixNum : forall n,
  nat_of_ascii8 n < 128 -> Valid (PFixnum n)
| VNFixNum : forall n,
  (* 負の数を導入したくないので、補数表現を使う *)
  223 < nat_of_ascii8 n /\ nat_of_ascii8 n < 256 -> Valid (NFixnum n)
| VUint8  : forall c, Valid (Uint8 c)
| VUint16 : forall c, Valid (Uint16 c)
| VUint32 : forall c, Valid (Uint32 c)
| VUint64 : forall c, Valid (Uint64 c)
| VInt8   : forall c, Valid (Int8 c)
| VInt16  : forall c, Valid (Int16 c)
| VInt32  : forall c, Valid (Int32 c)
| VInt64  : forall c, Valid (Int64 c)
| VFloat  : forall c, Valid (Float c)
| VDouble : forall c, Valid (Double c)
| VFixRaw : forall xs,
  length xs < pow 5 -> Valid (FixRaw xs)
| VRaw16 : forall xs,
  length xs < pow 16 -> Valid (Raw16 xs)
| VRaw32 : forall xs,
  length xs < pow 32 -> Valid (Raw32 xs)
| VFixArrayNil :
  Valid (FixArray [])
| VFixArrayCons : forall x xs,
  Valid x ->
  Valid (FixArray xs) ->
  length (x::xs) < pow 4 ->
  Valid (FixArray (x::xs))
| VArray16Nil :
  Valid (Array16 [])
| VArray16Cons: forall x xs,
  Valid x ->
  Valid (Array16 xs) ->
  length (x::xs) < pow 16 ->
  Valid (Array16 (x::xs))
| VArray32Nil :
  Valid (Array32 [])
| VArray32Cons : forall x xs,
  Valid x ->
  Valid (Array32 xs) ->
  length (x::xs) < pow 32 ->
  Valid (Array32 (x::xs))
| VFixMapNil:
  Valid (FixMap [])
| VFixMapCons : forall k v xs,
  Valid k ->
  Valid v ->
  Valid (FixMap xs)  ->
  length ((k,v)::xs) < pow 4 ->
  Valid (FixMap ((k,v)::xs))
| VMap16Nil :
  Valid (Map16 [])
| VMap16Cons : forall k v xs,
  Valid k ->
  Valid v ->
  Valid (Map16 xs)  ->
  length ((k,v)::xs) < pow 16 ->
  Valid (Map16 ((k,v)::xs))
| VMap32Nil :
  Valid (Map32 [])
| VMap32Cons : forall k v xs,
  Valid k ->
  Valid v ->
  Valid (Map32 xs)  ->
  length ((k,v)::xs) < pow 32 ->
  Valid (Map32 ((k,v)::xs)).

Lemma varray16_inv1: forall x xs,
  Valid (Array16 (x::xs)) ->
  ("000", "000") <> ascii16_of_nat (length (x :: xs)).
Proof.
intros.
apply ascii16_not_O.
split; [ apply length_lt_O | inversion H; auto ].
Qed.

Lemma varray16_inv2 : forall A (x y : A) xs ys,
  pow 16 > length (x :: xs) ->
  pow 16 > length (y :: ys) ->
  ascii16_of_nat (length (x :: xs)) = ascii16_of_nat (length (y :: ys)) ->
  ascii16_of_nat (length xs) = ascii16_of_nat (length ys).
Proof.
intros.
apply ascii16_of_nat_eq in H1; auto.
Qed.

(* Better induction principle for object. Pattern copied from
   http://adam.chlipala.net/cpdt/html/InductiveTypes.html *)
Section ObjectInd'.
  Variable P: object -> Prop.

  Let P_both p := P (fst p) /\ P (snd p).

  Hypothesis PBool: forall x, P (Bool x).
  Hypothesis PNil: P Nil.
  Hypothesis PPFixnum: forall x, P (PFixnum x).
  Hypothesis PNFixnum: forall x, P (NFixnum x).
  Hypothesis PUint8  : forall x, P (Uint8 x).
  Hypothesis PUint16 : forall x, P (Uint16 x).
  Hypothesis PUint32 : forall x, P (Uint32 x).
  Hypothesis PUint64 : forall x, P (Uint64 x).
  Hypothesis PInt8   : forall x, P (Int8 x).
  Hypothesis PInt16  : forall x, P (Int16 x).
  Hypothesis PInt32  : forall x, P (Int32 x).
  Hypothesis PInt64  : forall x, P (Int64 x).
  Hypothesis PFloat  : forall x, P (Float x).
  Hypothesis PDouble : forall x, P (Double x).
  Hypothesis PFixRaw : forall x, P (FixRaw x).
  Hypothesis PRaw16  : forall x, P (Raw16 x).
  Hypothesis PRaw32  : forall x, P (Raw32 x).

  Hypothesis PFixArray: forall os, Forall P os -> P (FixArray os).
  Hypothesis PArray16: forall os, Forall P os -> P (Array16 os).
  Hypothesis PArray32: forall os, Forall P os -> P (Array32 os).
  Hypothesis PFixMap: forall ps, Forall P_both ps -> P (FixMap ps).
  Hypothesis PMap16: forall ps, Forall P_both ps -> P (Map16 ps).
  Hypothesis PMap32: forall ps, Forall P_both ps -> P (Map32 ps).

  Let P_all object_ind' := fix F os :=
    match os return Forall P os with
    | [] => Forall_nil P
    | o :: os => Forall_cons o (object_ind' o) (F os)
    end.

  Let P_all_pairs object_ind' := fix F ps :=
    match ps return Forall P_both ps with
    | [] => Forall_nil P_both
    | (k,v) :: ps => Forall_cons (k,v) (@conj (P k) (P v) (object_ind' k) (object_ind' v)) (F ps)
    end.

  Fixpoint object_ind' o: P o :=
    match o return P o with
    | Nil => PNil
    | Bool    x => PBool x
    | PFixnum x => PPFixnum x
    | NFixnum x => PNFixnum x
    | Uint8   x => PUint8 x
    | Uint16  x => PUint16 x
    | Uint32  x => PUint32 x
    | Uint64  x => PUint64 x
    | Int8    x => PInt8 x
    | Int16   x => PInt16 x
    | Int32   x => PInt32 x
    | Int64   x => PInt64 x
    | Float   x => PFloat x
    | Double  x => PDouble x
    | FixRaw  x => PFixRaw x
    | Raw16   x => PRaw16 x
    | Raw32   x => PRaw32 x
    | FixArray os => PFixArray os (P_all object_ind' os)
    | Array16 os => PArray16 os (P_all object_ind' os)
    | Array32 os => PArray32 os (P_all object_ind' os)
    | FixMap ps => PFixMap ps (P_all_pairs object_ind' ps)
    | Map16 ps => PMap16 ps (P_all_pairs object_ind' ps)
    | Map32 ps => PMap32 ps (P_all_pairs object_ind' ps)
    end.
End ObjectInd'.
