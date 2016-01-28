type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val plus : int -> int -> int **)

let rec plus = (+)

(** val mult : int -> int -> int **)

let rec mult = ( * )

(** val nat_iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n0

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> int **)
  
  let rec size_nat = function
  | XI p0 -> Pervasives.succ (size_nat p0)
  | XO p0 -> Pervasives.succ (size_nat p0)
  | XH -> Pervasives.succ 0
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive * mask)
      -> positive * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then ((XI s), (sub_mask r' s')) else ((XO s), (IsPos r'))
     | _ -> ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> positive * mask **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> (XH, (IsPos XH)))
  | XH -> (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : int -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a
            | Lt -> gcdn n1 (sub b' a') a
            | Gt -> gcdn n1 (sub a' b') b)
         | XO b0 -> gcdn n1 a b0
         | XH -> XH)
      | XO a0 ->
        (match b with
         | XI p -> gcdn n1 a0 b
         | XO b0 -> XO (gcdn n1 a0 b0)
         | XH -> XH)
      | XH -> XH)
      n0
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)
  
  let rec ggcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a,
      b)))
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n1 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n1 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 ->
           let (g, p) = ggcdn n1 a b0 in
           let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI p ->
           let (g, p0) = ggcdn n1 a0 b in
           let (aa, bb) = p0 in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n1 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n0
  
  (** val ggcd : positive -> positive -> positive * (positive * positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> int -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> int -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> int -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XO p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         false)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XH ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n1 ->
         false)
         n0)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> int **)
  
  let to_nat x =
    iter_op plus x (Pervasives.succ 0)
  
  (** val of_nat : int -> positive **)
  
  let rec of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        XH)
        (fun n1 ->
        succ (of_nat x))
        x)
      n0
  
  (** val of_succ_nat : int -> positive **)
  
  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0
 end

module Coq_Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> int **)
  
  let rec size_nat = function
  | XI p0 -> Pervasives.succ (size_nat p0)
  | XO p0 -> Pervasives.succ (size_nat p0)
  | XH -> Pervasives.succ 0
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive * mask)
      -> positive * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then ((XI s), (sub_mask r' s')) else ((XO s), (IsPos r'))
     | _ -> ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> positive * mask **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> (XH, (IsPos XH)))
  | XH -> (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : int -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a
            | Lt -> gcdn n1 (sub b' a') a
            | Gt -> gcdn n1 (sub a' b') b)
         | XO b0 -> gcdn n1 a b0
         | XH -> XH)
      | XO a0 ->
        (match b with
         | XI p -> gcdn n1 a0 b
         | XO b0 -> XO (gcdn n1 a0 b0)
         | XH -> XH)
      | XH -> XH)
      n0
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)
  
  let rec ggcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a,
      b)))
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n1 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n1 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 ->
           let (g, p) = ggcdn n1 a b0 in
           let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI p ->
           let (g, p0) = ggcdn n1 a0 b in
           let (aa, bb) = p0 in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n1 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n0
  
  (** val ggcd : positive -> positive -> positive * (positive * positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> int -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> int -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> int -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XO p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         false)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XH ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n1 ->
         false)
         n0)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> int **)
  
  let to_nat x =
    iter_op plus x (Pervasives.succ 0)
  
  (** val of_nat : int -> positive **)
  
  let rec of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        XH)
        (fun n1 ->
        succ (of_nat x))
        x)
      n0
  
  (** val of_succ_nat : int -> positive **)
  
  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0
  
  (** val eq_dec : positive -> positive -> bool **)
  
  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> false)
    | XO p0 ->
      (match y0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> false)
    | XH ->
      (match y0 with
       | XH -> true
       | _ -> false)
  
  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let rec peano_rect a f p =
    let f2 = peano_rect (f XH a) (fun p0 x -> f (succ (XO p0)) (f (XO p0) x))
    in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)
  
  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)
  
  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)
  
  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0), (peanoView_xO p0 q0))))
  
  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0), (peanoView_xI p0 q0))))
  
  (** val peanoView : positive -> coq_PeanoView **)
  
  let rec peanoView = function
  | XI p0 -> peanoView_xI p0 (peanoView p0)
  | XO p0 -> peanoView_xO p0 (peanoView p0)
  | XH -> PeanoOne
  
  (** val coq_PeanoView_iter :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)
  
  (** val eqb_spec : positive -> positive -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq : comparison -> comparison -> comparison **)
  
  let switch_Eq c = function
  | Eq -> c
  | x -> x
  
  (** val mask2cmp : mask -> comparison **)
  
  let mask2cmp = function
  | IsNul -> Eq
  | IsPos p0 -> Gt
  | IsNeg -> Lt
  
  (** val leb_spec0 : positive -> positive -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : positive -> positive -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : positive -> positive -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : positive -> positive -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : positive -> positive -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : positive -> positive -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t = n
  
  (** val zero : n **)
  
  let zero =
    N0
  
  (** val one : n **)
  
  let one =
    Npos XH
  
  (** val two : n **)
  
  let two =
    Npos (XO XH)
  
  (** val succ_double : n -> n **)
  
  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val double : n -> n **)
  
  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val succ : n -> n **)
  
  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)
  
  (** val pred : n -> n **)
  
  let pred = function
  | N0 -> N0
  | Npos p -> Coq_Pos.pred_N p
  
  (** val succ_pos : n -> positive **)
  
  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p
  
  (** val add : n -> n -> n **)
  
  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))
  
  (** val sub : n -> n -> n **)
  
  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))
  
  (** val mul : n -> n -> n **)
  
  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))
  
  (** val compare : n -> n -> comparison **)
  
  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Eq
       | Npos m' -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')
  
  (** val eqb : n -> n -> bool **)
  
  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m with
       | N0 -> false
       | Npos q -> Coq_Pos.eqb p q)
  
  (** val leb : n -> n -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : n -> n -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val min : n -> n -> n **)
  
  let min n0 n' =
    match compare n0 n' with
    | Gt -> n'
    | _ -> n0
  
  (** val max : n -> n -> n **)
  
  let max n0 n' =
    match compare n0 n' with
    | Gt -> n0
    | _ -> n'
  
  (** val div2 : n -> n **)
  
  let div2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos p
     | XO p -> Npos p
     | XH -> N0)
  
  (** val even : n -> bool **)
  
  let even = function
  | N0 -> true
  | Npos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : n -> bool **)
  
  let odd n0 =
    negb (even n0)
  
  (** val pow : n -> n -> n **)
  
  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 ->
    (match n0 with
     | N0 -> N0
     | Npos q -> Npos (Coq_Pos.pow q p0))
  
  (** val square : n -> n **)
  
  let square = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.square p)
  
  (** val log2 : n -> n **)
  
  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)
  
  (** val size : n -> n **)
  
  let size = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.size p)
  
  (** val size_nat : n -> int **)
  
  let size_nat = function
  | N0 -> 0
  | Npos p -> Coq_Pos.size_nat p
  
  (** val pos_div_eucl : positive -> n -> n * n **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XH ->
      (match b with
       | N0 -> (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> ((Npos XH), N0)
          | _ -> (N0, (Npos XH))))
  
  (** val div_eucl : n -> n -> n * n **)
  
  let div_eucl a b =
    match a with
    | N0 -> (N0, N0)
    | Npos na ->
      (match b with
       | N0 -> (N0, a)
       | Npos p -> pos_div_eucl na b)
  
  (** val div : n -> n -> n **)
  
  let div a b =
    fst (div_eucl a b)
  
  (** val modulo : n -> n -> n **)
  
  let modulo a b =
    snd (div_eucl a b)
  
  (** val gcd : n -> n -> n **)
  
  let gcd a b =
    match a with
    | N0 -> b
    | Npos p ->
      (match b with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))
  
  (** val ggcd : n -> n -> n * (n * n) **)
  
  let ggcd a b =
    match a with
    | N0 -> (b, (N0, (Npos XH)))
    | Npos p ->
      (match b with
       | N0 -> (a, ((Npos XH), N0))
       | Npos q ->
         let (g, p0) = Coq_Pos.ggcd p q in
         let (aa, bb) = p0 in ((Npos g), ((Npos aa), (Npos bb))))
  
  (** val sqrtrem : n -> n * n **)
  
  let sqrtrem = function
  | N0 -> (N0, N0)
  | Npos p ->
    let (s, m) = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> ((Npos s), (Npos r))
     | _ -> ((Npos s), N0))
  
  (** val sqrt : n -> n **)
  
  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.sqrt p)
  
  (** val coq_lor : n -> n -> n **)
  
  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))
  
  (** val coq_land : n -> n -> n **)
  
  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)
  
  (** val ldiff : n -> n -> n **)
  
  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)
  
  (** val coq_lxor : n -> n -> n **)
  
  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)
  
  (** val shiftl_nat : n -> int -> n **)
  
  let shiftl_nat a n0 =
    nat_iter n0 double a
  
  (** val shiftr_nat : n -> int -> n **)
  
  let shiftr_nat a n0 =
    nat_iter n0 div2 a
  
  (** val shiftl : n -> n -> n **)
  
  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)
  
  (** val shiftr : n -> n -> n **)
  
  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter p div2 a
  
  (** val testbit_nat : n -> int -> bool **)
  
  let testbit_nat = function
  | N0 -> (fun x -> false)
  | Npos p -> Coq_Pos.testbit_nat p
  
  (** val testbit : n -> n -> bool **)
  
  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
  
  (** val to_nat : n -> int **)
  
  let to_nat = function
  | N0 -> 0
  | Npos p -> Coq_Pos.to_nat p
  
  (** val of_nat : int -> n **)
  
  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      N0)
      (fun n' -> Npos
      (Coq_Pos.of_succ_nat n'))
      n0
  
  (** val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f x
  
  (** val eq_dec : n -> n -> bool **)
  
  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos x ->
      (match m with
       | N0 -> false
       | Npos p0 -> Coq_Pos.eq_dec x p0)
  
  (** val discr : n -> positive option **)
  
  let discr = function
  | N0 -> None
  | Npos p -> Some p
  
  (** val binary_rect :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n0 =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p ->
       let rec f = function
       | XI p1 -> fS2' p1 (f p1)
       | XO p1 -> f2' p1 (f p1)
       | XH -> fS2 N0 f0
       in f p)
  
  (** val binary_rec :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rect f0 f n0 =
    let f' = fun p -> f (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f N0 f0) f' p)
  
  (** val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : n -> n -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : n -> n -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : n -> n **)
  
  let sqrt_up a =
    match compare N0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> N0
  
  (** val log2_up : n -> n **)
  
  let log2_up a =
    match compare (Npos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> N0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : n -> n -> n **)
  
  let lcm a b =
    mul a (div b (gcd a b))
  
  (** val eqb_spec : n -> n -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> n **)
  
  let b2n = function
  | true -> Npos XH
  | false -> N0
  
  (** val setbit : n -> n -> n **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Npos XH) n0)
  
  (** val clearbit : n -> n -> n **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Npos XH) n0)
  
  (** val ones : n -> n **)
  
  let ones n0 =
    pred (shiftl (Npos XH) n0)
  
  (** val lnot : n -> n -> n **)
  
  let lnot a n0 =
    coq_lxor a (ones n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : n -> n -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : n -> n -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : n -> n -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : n -> n -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a::l0 -> rev_append l0 (a::l')

(** val rev' : 'a1 list -> 'a1 list **)

let rev' l =
  rev_append l []

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t0 -> fold_left f t0 (f a0 b)

(** val eucl_dev : int -> int -> (int * int) **)

let eucl_dev = fun n m -> (m/n, m mod n)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val zero0 : ascii **)

let zero0 =
  Ascii (false, false, false, false, false, false, false, false)

(** val one0 : ascii **)

let one0 =
  Ascii (true, false, false, false, false, false, false, false)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
| Ascii (a1, a2, a3, a4, a5, a6, a7, a8) ->
  Ascii (c, a1, a2, a3, a4, a5, a6, a7)

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      zero0)
      (fun n' ->
      match p with
      | XI p' -> shift true (loop n' p')
      | XO p' -> shift false (loop n' p')
      | XH -> one0)
      n0
  in loop (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0))))))))

(** val ascii_of_N : n -> ascii **)

let ascii_of_N = function
| N0 -> zero0
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : int -> ascii **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b::l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : ascii -> n **)

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[]))))))))

(** val nat_of_ascii : ascii -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val length_tailrec : 'a1 list -> int **)

let length_tailrec xs =
  fold_left (fun x x0 -> Pervasives.succ x) xs 0

(** val rev_tailrec : 'a1 list -> 'a1 list **)

let rev_tailrec xs =
  rev' xs

(** val flat_map_tailrec : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let flat_map_tailrec f xs =
  rev_tailrec (fold_left (fun acc x -> rev_append (f x) acc) xs [])

(** val take : int -> 'a1 list -> 'a1 list **)

let rec take n0 xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    [])
    (fun m ->
    match xs with
    | [] -> []
    | x::xs0 -> x::(take m xs0))
    n0

(** val drop : int -> 'a1 list -> 'a1 list **)

let rec drop n0 xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    xs)
    (fun m ->
    match xs with
    | [] -> []
    | x::xs0 -> drop m xs0)
    n0

(** val split_at : int -> 'a1 list -> 'a1 list * 'a1 list **)

let split_at n0 xs =
  ((take n0 xs), (drop n0 xs))

(** val pair : 'a1 list -> ('a1 * 'a1) list **)

let rec pair = function
| [] -> []
| k::l ->
  (match l with
   | [] -> []
   | v::ys -> (k, v)::(pair ys))

(** val pow0 : int -> int **)

let rec pow0 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Pervasives.succ
    0)
    (fun n' ->
    mult (Pervasives.succ (Pervasives.succ 0)) (pow0 n'))
    n0

(** val divmod : int -> int -> (int * int) **)

let divmod n0 m =
  eucl_dev m n0

type ascii8 = ascii

type ascii16 = ascii8 * ascii8

type ascii32 = ascii16 * ascii16

type ascii64 = ascii32 * ascii32

(** val nat_of_ascii8 : ascii -> int **)

let nat_of_ascii8 =
  nat_of_ascii

(** val ascii8_of_nat : int -> ascii **)

let ascii8_of_nat =
  ascii_of_nat

(** val ascii16_of_nat : int -> ascii * ascii **)

let ascii16_of_nat a =
  let (q, r) =
    divmod a
      (pow0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))
  in
  ((ascii8_of_nat q), (ascii8_of_nat r))

(** val nat_of_ascii16 : ascii16 -> int **)

let nat_of_ascii16 = function
| (a1, a2) ->
  plus
    (mult (nat_of_ascii8 a1)
      (pow0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))) (nat_of_ascii8 a2)

(** val ascii32_of_nat : int -> (ascii * ascii) * (ascii * ascii) **)

let ascii32_of_nat a =
  let (q, r) =
    divmod a
      (pow0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))
  in
  ((ascii16_of_nat q), (ascii16_of_nat r))

(** val nat_of_ascii32 : ascii32 -> int **)

let nat_of_ascii32 = function
| (a1, a2) ->
  plus
    (mult (nat_of_ascii16 a1)
      (pow0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))))) (nat_of_ascii16 a2)

(** val list_of_ascii8 : ascii8 -> ascii8 list **)

let list_of_ascii8 x =
  x::[]

(** val list_of_ascii16 : ascii16 -> ascii8 list **)

let list_of_ascii16 = function
| (x1, x2) -> app (list_of_ascii8 x1) (list_of_ascii8 x2)

(** val list_of_ascii32 : ascii32 -> ascii8 list **)

let list_of_ascii32 = function
| (x1, x2) -> app (list_of_ascii16 x1) (list_of_ascii16 x2)

(** val list_of_ascii64 : ascii64 -> ascii8 list **)

let list_of_ascii64 = function
| (x1, x2) -> app (list_of_ascii32 x1) (list_of_ascii32 x2)

type object0 =
| Bool of bool
| Nil
| PFixnum of ascii8
| NFixnum of ascii8
| Uint8 of ascii8
| Uint16 of ascii16
| Uint32 of ascii32
| Uint64 of ascii64
| Int8 of ascii8
| Int16 of ascii16
| Int32 of ascii32
| Int64 of ascii64
| Float of ascii32
| Double of ascii64
| FixRaw of ascii8 list
| Raw16 of ascii8 list
| Raw32 of ascii8 list
| FixArray of object0 list
| Array16 of object0 list
| Array32 of object0 list
| FixMap of (object0 * object0) list
| Map16 of (object0 * object0) list
| Map32 of (object0 * object0) list

(** val serialize_rev_list :
    (object0 -> ascii8 list -> ascii8 list) -> object0 list -> ascii8 list ->
    ascii8 list **)

let rec serialize_rev_list serialize_rev0 os acc =
  match os with
  | [] -> acc
  | o::os0 -> serialize_rev_list serialize_rev0 os0 (serialize_rev0 o acc)

(** val serialize_rev_kvs :
    (object0 -> ascii8 list -> ascii8 list) -> (object0 * object0) list ->
    ascii8 list -> ascii8 list **)

let rec serialize_rev_kvs serialize_rev0 ps acc =
  match ps with
  | [] -> acc
  | y::ps0 ->
    let (k, v) = y in
    serialize_rev_kvs serialize_rev0 ps0
      (serialize_rev0 v (serialize_rev0 k acc))

(** val serialize_rev : object0 -> ascii list -> ascii8 list **)

let rec serialize_rev obj acc =
  match obj with
  | Bool b ->
    if b
    then (Ascii (true, true, false, false, false, false, true, true))::acc
    else (Ascii (false, true, false, false, false, false, true, true))::acc
  | Nil ->
    (Ascii (false, false, false, false, false, false, true, true))::acc
  | PFixnum a ->
    let Ascii (b1, b2, b3, b4, b5, b6, b7, b) = a in
    (Ascii (b1, b2, b3, b4, b5, b6, b7, false))::acc
  | NFixnum a ->
    let Ascii (b1, b2, b3, b4, b5, b, b0, b6) = a in
    (Ascii (b1, b2, b3, b4, b5, true, true, true))::acc
  | Uint8 c ->
    rev_append (list_of_ascii8 c) ((Ascii (false, false, true, true, false,
      false, true, true))::acc)
  | Uint16 c ->
    rev_append (list_of_ascii16 c) ((Ascii (true, false, true, true, false,
      false, true, true))::acc)
  | Uint32 c ->
    rev_append (list_of_ascii32 c) ((Ascii (false, true, true, true, false,
      false, true, true))::acc)
  | Uint64 c ->
    rev_append (list_of_ascii64 c) ((Ascii (true, true, true, true, false,
      false, true, true))::acc)
  | Int8 c ->
    rev_append (list_of_ascii8 c) ((Ascii (false, false, false, false, true,
      false, true, true))::acc)
  | Int16 c ->
    rev_append (list_of_ascii16 c) ((Ascii (true, false, false, false, true,
      false, true, true))::acc)
  | Int32 c ->
    rev_append (list_of_ascii32 c) ((Ascii (false, true, false, false, true,
      false, true, true))::acc)
  | Int64 c ->
    rev_append (list_of_ascii64 c) ((Ascii (true, true, false, false, true,
      false, true, true))::acc)
  | Float c ->
    rev_append (list_of_ascii32 c) ((Ascii (false, true, false, true, false,
      false, true, true))::acc)
  | Double c ->
    rev_append (list_of_ascii64 c) ((Ascii (true, true, false, true, false,
      false, true, true))::acc)
  | FixRaw xs ->
    let Ascii (b1, b2, b3, b4, b5, b, b0, b6) =
      ascii8_of_nat (length_tailrec xs)
    in
    rev_append xs ((Ascii (b1, b2, b3, b4, b5, true, false, true))::acc)
  | Raw16 xs ->
    let (s1, s2) = ascii16_of_nat (length_tailrec xs) in
    rev_append xs (s2::(s1::((Ascii (false, true, false, true, true, false,
      true, true))::acc)))
  | Raw32 xs ->
    let (p, p0) = ascii32_of_nat (length_tailrec xs) in
    let (s1, s2) = p in
    let (s3, s4) = p0 in
    rev_append xs (s4::(s3::(s2::(s1::((Ascii (true, true, false, true, true,
      false, true, true))::acc)))))
  | FixArray xs ->
    let Ascii (b1, b2, b3, b4, b, b0, b5, b6) =
      ascii8_of_nat (length_tailrec xs)
    in
    serialize_rev_list serialize_rev xs ((Ascii (b1, b2, b3, b4, true, false,
      false, true))::acc)
  | Array16 xs ->
    let (s1, s2) = ascii16_of_nat (length_tailrec xs) in
    serialize_rev_list serialize_rev xs (s2::(s1::((Ascii (false, false,
      true, true, true, false, true, true))::acc)))
  | Array32 xs ->
    let (p, p0) = ascii32_of_nat (length_tailrec xs) in
    let (s1, s2) = p in
    let (s3, s4) = p0 in
    serialize_rev_list serialize_rev xs (s4::(s3::(s2::(s1::((Ascii (true,
      false, true, true, true, false, true, true))::acc)))))
  | FixMap xs ->
    let Ascii (b1, b2, b3, b4, b, b0, b5, b6) =
      ascii8_of_nat (length_tailrec xs)
    in
    serialize_rev_kvs serialize_rev xs ((Ascii (b1, b2, b3, b4, false, false,
      false, true))::acc)
  | Map16 xs ->
    let (s1, s2) = ascii16_of_nat (length_tailrec xs) in
    serialize_rev_kvs serialize_rev xs (s2::(s1::((Ascii (false, true, true,
      true, true, false, true, true))::acc)))
  | Map32 xs ->
    let (p, p0) = ascii32_of_nat (length_tailrec xs) in
    let (s1, s2) = p in
    let (s3, s4) = p0 in
    serialize_rev_kvs serialize_rev xs (s4::(s3::(s2::(s1::((Ascii (true,
      true, true, true, true, false, true, true))::acc)))))

(** val compact : object0 list -> ascii8 list **)

let compact xs =
  flat_map_tailrec (fun x ->
    match x with
    | FixRaw xs0 -> xs0
    | _ -> []) xs

(** val deserialize : int -> ascii8 list -> object0 list **)

let rec deserialize n0 xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match xs with
    | [] -> []
    | a::ys ->
      let Ascii (b1, b2, b3, b4, b5, b6, b7, b) = a in
      if b1
      then if b2
           then if b3
                then if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | s1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | s2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | s3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | s4::ys0 ->
                                                          let n1 =
                                                            nat_of_ascii32
                                                              ((s1, s2), (s3,
                                                              s4))
                                                          in
                                                          let (zs, ws) =
                                                            split_at
                                                              (mult
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0)) n1)
                                                              (deserialize 0
                                                                ys0)
                                                          in
                                                          (Map32
                                                          (pair zs))::ws))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | c3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | c4::l2 ->
                                                          (match l2 with
                                                           | [] -> []
                                                           | c5::l3 ->
                                                             (match l3 with
                                                              | [] -> []
                                                              | c6::l4 ->
                                                                (match l4 with
                                                                 | [] -> []
                                                                 | c7::l5 ->
                                                                   (match l5 with
                                                                    | [] ->
                                                                    []
                                                                    | c8::ys0 ->
                                                                    (Uint64
                                                                    (((c1,
                                                                    c2), (c3,
                                                                    c4)),
                                                                    ((c5,
                                                                    c6), (c7,
                                                                    c8))))::
                                                                    (deserialize
                                                                    0 ys0)))))))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                else if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | s1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | s2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | s3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | s4::ys0 ->
                                                          let n1 =
                                                            nat_of_ascii32
                                                              ((s1, s2), (s3,
                                                              s4))
                                                          in
                                                          let (zs, ws) =
                                                            split_at n1
                                                              (deserialize n1
                                                                ys0)
                                                          in
                                                          (Raw32
                                                          (compact zs))::ws))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | c3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | c4::l2 ->
                                                          (match l2 with
                                                           | [] -> []
                                                           | c5::l3 ->
                                                             (match l3 with
                                                              | [] -> []
                                                              | c6::l4 ->
                                                                (match l4 with
                                                                 | [] -> []
                                                                 | c7::l5 ->
                                                                   (match l5 with
                                                                    | [] ->
                                                                    []
                                                                    | c8::ys0 ->
                                                                    (Double
                                                                    (((c1,
                                                                    c2), (c3,
                                                                    c4)),
                                                                    ((c5,
                                                                    c6), (c7,
                                                                    c8))))::
                                                                    (deserialize
                                                                    0 ys0)))))))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | c3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | c4::l2 ->
                                                          (match l2 with
                                                           | [] -> []
                                                           | c5::l3 ->
                                                             (match l3 with
                                                              | [] -> []
                                                              | c6::l4 ->
                                                                (match l4 with
                                                                 | [] -> []
                                                                 | c7::l5 ->
                                                                   (match l5 with
                                                                    | [] ->
                                                                    []
                                                                    | c8::ys0 ->
                                                                    (Int64
                                                                    (((c1,
                                                                    c2), (c3,
                                                                    c4)),
                                                                    ((c5,
                                                                    c6), (c7,
                                                                    c8))))::
                                                                    (deserialize
                                                                    0 ys0)))))))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (Bool true)::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
           else if b3
                then if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | s1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | s2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | s3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | s4::ys0 ->
                                                          let n1 =
                                                            nat_of_ascii32
                                                              ((s1, s2), (s3,
                                                              s4))
                                                          in
                                                          let (zs, ws) =
                                                            split_at n1
                                                              (deserialize 0
                                                                ys0)
                                                          in
                                                          (Array32 zs)::ws))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::ys0 ->
                                                    (Uint16 (c1,
                                                      c2))::(deserialize 0
                                                              ys0)))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                else if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::ys0 ->
                                                    (Int16 (c1,
                                                      c2))::(deserialize 0
                                                              ys0)))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
      else if b2
           then if b3
                then if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | s1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | s2::ys0 ->
                                                    let n1 =
                                                      nat_of_ascii16 (s1, s2)
                                                    in
                                                    let (zs, ws) =
                                                      split_at
                                                        (mult
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0)) n1)
                                                        (deserialize 0 ys0)
                                                    in
                                                    (Map16 (pair zs))::ws))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | c3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | c4::ys0 ->
                                                          (Uint32 ((c1, c2),
                                                            (c3,
                                                            c4)))::(deserialize
                                                                    0 ys0)))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                else if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | s1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | s2::ys0 ->
                                                    let n1 =
                                                      nat_of_ascii16 (s1, s2)
                                                    in
                                                    let (zs, ws) =
                                                      split_at n1
                                                        (deserialize n1 ys0)
                                                    in
                                                    (Raw16 (compact zs))::ws))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | c3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | c4::ys0 ->
                                                          (Float ((c1, c2),
                                                            (c3,
                                                            c4)))::(deserialize
                                                                    0 ys0)))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | c2::l0 ->
                                                    (match l0 with
                                                     | [] -> []
                                                     | c3::l1 ->
                                                       (match l1 with
                                                        | [] -> []
                                                        | c4::ys0 ->
                                                          (Int32 ((c1, c2),
                                                            (c3,
                                                            c4)))::(deserialize
                                                                    0 ys0)))))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (Bool
                                                false)::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
           else if b3
                then if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | s1::l ->
                                                 (match l with
                                                  | [] -> []
                                                  | s2::ys0 ->
                                                    let n1 =
                                                      nat_of_ascii16 (s1, s2)
                                                    in
                                                    let (zs, ws) =
                                                      split_at n1
                                                        (deserialize 0 ys0)
                                                    in
                                                    (Array16 zs)::ws))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::ys0 ->
                                                 (Uint8
                                                   c1)::(deserialize 0 ys0))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                else if b4
                     then if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then []
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                     else if b5
                          then if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then (match ys with
                                               | [] -> []
                                               | c1::ys0 ->
                                                 (Int8
                                                   c1)::(deserialize 0 ys0))
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize 0 ys)
                                              in
                                              (FixArray zs)::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                          else if b6
                               then if b7
                                    then if b
                                         then (NFixnum (Ascii (b1, b2, b3,
                                                b4, b5, true, true,
                                                true)))::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, b5, false, false,
                                                  false))
                                              in
                                              let (zs, ws) =
                                                split_at n1
                                                  (deserialize n1 ys)
                                              in
                                              (FixRaw (compact zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                               else if b7
                                    then if b
                                         then Nil::(deserialize 0 ys)
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys)
                                    else if b
                                         then let n1 =
                                                nat_of_ascii8 (Ascii (b1, b2,
                                                  b3, b4, false, false,
                                                  false, false))
                                              in
                                              let (zs, ws) =
                                                split_at
                                                  (mult (Pervasives.succ
                                                    (Pervasives.succ 0)) n1)
                                                  (deserialize 0 ys)
                                              in
                                              (FixMap (pair zs))::ws
                                         else (PFixnum (Ascii (b1, b2, b3,
                                                b4, b5, b6, b7,
                                                false)))::(deserialize 0 ys))
    (fun m ->
    match xs with
    | [] -> []
    | y::ys -> (FixRaw (y::[]))::(deserialize m ys))
    n0

